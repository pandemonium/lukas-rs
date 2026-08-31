use fmt::Write;
use std::cell::RefCell;
use std::rc::Rc;
use std::{collections::HashMap, fmt, fs, io, path};

use std::sync::atomic::{AtomicUsize, Ordering};

use crate::{
    ast::{
        self, BUILTIN_MODULE_NAME, Binding, Literal, ProductElement, STDLIB_MODULE_NAME, Segment,
        TypeExpression,
        namer::{QualifiedName, TypeDefinition},
        pattern::Pattern,
    },
    closed::{self, CaptureInfo, Closed, Identifier, LexicalLevel},
    lambda_lift::{
        self, ChainWorker, ClosureInfo, CoproductLayout, LiftedFunction, TopLevelBinding, Worker,
    },
    phase,
    typer::{BaseType, Type, memory_layout_evidence_name},
};

/// What a worker's own recursive call looks like, for tail-call loopification. A top-level
/// `Worker` names itself by its global name; a lifted (recursive) lambda names itself through
/// `self` (`Identifier::SelfRef`).
#[derive(Clone, Copy)]
enum SelfCall<'a> {
    Named(&'a QualifiedName),
    SelfRef,
}

// Widest inlined field before it is kept a pointer instead; must match
// `FLAT_INLINE_CAP` in lambda_lift so codegen and the layout table agree.
const FLAT_INLINE_CAP: usize = 8;
const FLAT_MAX_SHAPE: usize = 128;
const FLAT_MAX_FIELDS: usize = 64;

fn direct_array_enabled() -> bool {
    std::env::var_os("MARM_NO_DIRECT_ARRAY").is_none() && std::env::var_os("MARM_NOFLAT").is_none()
}

fn direct_write_enabled() -> bool {
    direct_array_enabled() && std::env::var_os("MARM_NO_DIRECT_WRITE").is_none()
}

/// Runtime packing shape for one array element. This mirrors the compact shape
/// grammar in `c/gc.c`: `0` is a leaf, a positive value is a product arity, and
/// `-1` introduces a tagged sum with a fixed-width union payload.
#[derive(Debug, Clone, PartialEq, Eq)]
enum RuntimeShape {
    Leaf,
    Product(Vec<RuntimeShape>),
    NicheSum {
        niche_tag: usize,
        payload_tag: usize,
        niche_offset: usize,
        payload_fields: Vec<RuntimeShape>,
    },
    Sum {
        payload_words: usize,
        variants: Vec<Vec<RuntimeShape>>,
    },
}

impl RuntimeShape {
    fn stored_words(&self) -> usize {
        match self {
            Self::Leaf => 1,
            Self::Product(fields) => fields.iter().map(Self::stored_words).sum(),
            Self::NicheSum { payload_fields, .. } => {
                payload_fields.iter().map(Self::stored_words).sum()
            }
            Self::Sum { payload_words, .. } => 1 + payload_words,
        }
    }

    fn encode(&self, out: &mut Vec<i64>) {
        match self {
            Self::Leaf => out.push(0),
            Self::Product(fields) => {
                out.push(fields.len() as i64);
                for field in fields {
                    field.encode(out);
                }
            }
            Self::NicheSum {
                niche_tag,
                payload_tag,
                niche_offset,
                payload_fields,
            } => {
                out.extend([
                    -2,
                    *niche_tag as i64,
                    *payload_tag as i64,
                    *niche_offset as i64,
                ]);
                out.push(payload_fields.len() as i64);
                for field in payload_fields {
                    field.encode(out);
                }
            }
            Self::Sum {
                payload_words,
                variants,
            } => {
                out.extend([-1, *payload_words as i64, variants.len() as i64]);
                for variant in variants {
                    out.push(variant.len() as i64);
                    for field in variant {
                        field.encode(out);
                    }
                }
            }
        }
    }

    fn zero_niche(&self) -> Option<usize> {
        match self {
            Self::Leaf => Some(0),
            Self::Product(fields) => {
                let mut offset = 0;
                for field in fields {
                    if let Some(inner) = field.zero_niche() {
                        return Some(offset + inner);
                    }
                    offset += field.stored_words();
                }
                None
            }
            // The zero pattern is the nullary value, hence is already valid.
            Self::NicheSum { .. } => None,
            // A tagged sum stores VInt(tag) in its first word; raw zero is invalid.
            Self::Sum { .. } => Some(0),
        }
    }
}

struct ShapeResult {
    shape: RuntimeShape,
    reaches_enclosing_type: bool,
}

#[derive(Clone)]
struct ArrayElementPlace {
    array: String,
    index: String,
    element_type: Type,
    source_array: Expr,
    source_index: Expr,
}

#[derive(Clone)]
struct FlatValuePlace {
    words: Vec<String>,
}

#[derive(Clone)]
struct CapturePlace {
    offset: usize,
    width: usize,
    ty: Type,
}

thread_local! {
    /// Lexical locals whose value is represented by a packed array element rather
    /// than an eagerly rebuilt canonical object. Entries are scoped by
    /// `compile_let`; code generation itself is single-threaded.
    static ARRAY_ELEMENT_PLACES: RefCell<HashMap<usize, ArrayElementPlace>> =
        RefCell::new(HashMap::new());
    /// Record-valued locals split into their canonical words. A whole-value use
    /// rebuilds the record; projections and other flat consumers read the words.
    static FLAT_VALUE_PLACES: RefCell<HashMap<usize, FlatValuePlace>> =
        RefCell::new(HashMap::new());
    /// Logical closure capture index -> physical range in the flat capture array.
    static CAPTURE_PLACES: RefCell<Vec<CapturePlace>> = RefCell::new(Vec::new());
}

pub struct Codegen;

impl phase::Phase for Codegen {
    type Annotation = CaptureInfo;
    type TermId = closed::Identifier;
    type TypeId = QualifiedName;
}

type Expr = phase::Expr<Codegen>;

// Naming for the C backend. Mirrors the strategy the Scheme backend uses --
// builtin/foreign terms map to a fixed runtime name, everything else to its
// qualified surface name -- but is kept independent of `chez.rs` (which is
// Scheme-only) and always emits valid C identifiers.
fn c_name(q: &QualifiedName) -> String {
    if is_builtin(q) {
        map_builtin_name(q).to_owned()
    } else {
        surface_name(q)
    }
}

fn is_builtin(q: &QualifiedName) -> bool {
    q.module.head == BUILTIN_MODULE_NAME || q.module.head == STDLIB_MODULE_NAME
}

// Qualified name flattened to a C identifier: module path and member joined
// with `_`. The lexer allows `'` (prime) in identifiers -- e.g. `take_while'` --
// which is not a valid C identifier character, so it is rewritten to a readable
// `_prime` suffix. Operators reach `c_name` only as builtins (named via
// `map_builtin_name`), so nothing else here needs escaping. Definitions and uses
// both flow through this function, so the rewrite stays consistent.
// Escape a string for embedding in a C string literal: the delimiters/backslash and
// control characters that would otherwise break the literal (or `sizeof`'s byte count).
// Non-ASCII UTF-8 is emitted verbatim -- valid in a C string literal in a UTF-8 source.
fn c_string_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            // Any other control character as a fixed-width octal escape (three digits, so
            // a following literal digit can't extend it).
            c if (c as u32) < 0x20 => out.push_str(&format!("\\{:03o}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

// A `VChar('...')` C char constant for a Marmelade char. A raw newline, quote, or
// backslash cannot appear literally inside a char constant, so escape those (plus the
// common control escapes); printable ASCII is emitted verbatim. Everything else --
// other control characters and non-ASCII -- becomes a fixed-width octal escape of the
// low byte, matching the runtime's single-byte `Char` (`as_char` masks to 0xFF).
fn c_char_literal(c: char) -> String {
    let body = match c {
        '\'' => "\\'".to_owned(),
        '\\' => "\\\\".to_owned(),
        '\n' => "\\n".to_owned(),
        '\t' => "\\t".to_owned(),
        '\r' => "\\r".to_owned(),
        c if (0x20..0x7f).contains(&(c as u32)) => c.to_string(),
        c => format!("\\{:03o}", (c as u32) & 0xFF),
    };
    format!("VChar('{body}')")
}

fn surface_name(q: &QualifiedName) -> String {
    let mut parts = Vec::with_capacity(2 + q.module.tail.len());
    parts.push(q.module.head.clone());
    parts.extend_from_slice(q.module.tail.as_slice());
    parts.push(q.member.as_str().to_owned());
    parts.join("_").replace('\'', "_prime")
}

// Runtime function names for builtin/foreign primitives -- these name the C
// runtime the emitted code links against, so they must be valid C identifiers.
fn map_builtin_name(q: &QualifiedName) -> &'static str {
    match q.member.as_str() {
        "print_endline" => "builtin_print_endline",
        "prim_eq" => "builtin_eq",
        "-" => "builtin_sub",
        "+" => "builtin_add",
        "*" => "builtin_mul",
        "/" => "builtin_div",
        "%" => "builtin_mod",
        "prim_lt" => "builtin_lt",
        "prim_gt" => "builtin_gt",
        "and" => "builtin_and",
        "xor" => "builtin_xor",
        "or" => "builtin_or",
        "not" => "builtin_not",
        "negate" => "builtin_neg",
        "int_of_char" => "builtin_int_of_char",
        "float_of_int" => "builtin_float_of_int",
        "int_of_float" => "builtin_int_of_float",
        "char_of_byte" => "builtin_char_of_byte",
        "prim_gte" => "builtin_ge",
        "prim_lte" => "builtin_le",
        "text_fold_right" => "builtin_text_fold_right",
        otherwise => panic!("unmapped builtin {otherwise:?}"),
    }
}

#[derive(Debug, Default)]
pub struct CodeBuffer(String);

impl CodeBuffer {
    pub fn write_to_file(&self, path: impl AsRef<path::Path>) -> io::Result<()> {
        fs::write(path, &self.0)
    }

    /// Splice a file's contents into the buffer verbatim -- used to inline a
    /// module's foreign `.ss` implementation into the emitted Scheme.
    pub fn splice_file(&mut self, path: impl AsRef<path::Path>) -> io::Result<()> {
        let path = path.as_ref();
        let contents = fs::read_to_string(path)
            .map_err(|e| io::Error::new(e.kind(), format!("{}: {e}", path.display())))?;
        self.0.push_str(&contents);
        self.0.push('\n');
        Ok(())
    }
}

impl fmt::Write for CodeBuffer {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0.push_str(s);
        Ok(())
    }
}

impl fmt::Display for CodeBuffer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self(buffer) = self;
        write!(f, "{buffer}")
    }
}

// If `head` names a builtin with a direct primitive form, return its C prim
// name and arity. A *saturated* application of it can be emitted as a direct
// call (`prim_add(x, y)`) instead of the allocating curried-closure `apply`
// chain. text_fold_right has no prim form and stays curried.
fn builtin_prim(head: &Expr) -> Option<(&'static str, usize)> {
    let q = match head {
        Expr::Variable(_, Identifier::Global(q)) => q.as_ref(),
        Expr::InvokeBridge(_, the) => &the.qualified_name,
        _otherwise => return None,
    };
    if !is_builtin(q) {
        return None;
    }
    Some(match q.member.as_str() {
        "+" => ("prim_add", 2),
        "-" => ("prim_sub", 2),
        "*" => ("prim_mul", 2),
        "/" => ("prim_div", 2),
        "%" => ("prim_mod", 2),
        "prim_eq" => ("prim_eq", 2),
        "prim_lt" => ("prim_lt", 2),
        "prim_gt" => ("prim_gt", 2),
        "prim_lte" => ("prim_le", 2),
        "prim_gte" => ("prim_ge", 2),
        "and" => ("prim_and", 2),
        "or" => ("prim_or", 2),
        "xor" => ("prim_xor", 2),
        "not" => ("prim_not", 1),
        "negate" => ("prim_neg", 1),
        "int_of_char" => ("prim_int_of_char", 1),
        "float_of_int" => ("prim_float_of_int", 1),
        "int_of_float" => ("prim_int_of_float", 1),
        "char_of_byte" => ("prim_char_of_byte", 1),
        "prim_show" => ("prim_show", 1),
        "print_endline" => ("prim_print_endline", 1),
        _otherwise => return None,
    })
}

// The monomorphic `prim_show` leaf for `arg`'s static type. `prim_show` is only ever
// applied at a primitive (leaf) type -- the `Display` witnesses for compound types
// recurse through `display`, never calling `prim_show` on a tuple/constructor -- so a
// non-leaf here is a compiler invariant break.
// `Text` reaches codegen two ways: the legacy builtin base type, and the stdlib DU
// `opaque Text ::= Text Bytes` that string literals now elaborate to. Both erase to
// the same OBJ_SLICE, so both are eligible for the monomorphic prims.
//
// The DU arm compares against `stdlib_text_type()` -- the compiler's one sanctioned
// reference to `Root.Prelude.Text` -- NOT against the bare member name. Matching
// `name.member == "Text"` would also accept any user type that happens to be called
// `Text` in any module, and `prim_text_eq` would then read a value that is not a
// Slice as one.
fn is_text_type(ty: &Type) -> bool {
    matches!(ty, Type::Base(BaseType::Text)) || *ty == crate::typer::stdlib_text_type()
}

fn show_prim(arg: &Expr) -> &'static str {
    match &arg.annotation().type_info.inferred_type {
        Type::Base(BaseType::Int) => "prim_show_int",
        Type::Base(BaseType::Float) => "prim_show_float",
        Type::Base(BaseType::Char) => "prim_show_char",
        Type::Base(BaseType::Text) => "prim_show_text",
        // `Text` is the stdlib DU `Text ::= Text Bytes`, so it appears as a constructor.
        Type::Constructor(name) if name.member.as_str() == "Text" => "prim_show_text",
        other => panic!(
            "prim_show applied to non-primitive type {other:?}; render compound values \
             through `display` / string interpolation, not raw `prim_show`"
        ),
    }
}

// The builtin arithmetic/ordering operators are polymorphic (`∀a. a -> a -> a` and
// `∀a. a -> a -> Bool`), so their prim is chosen from the operands' static type -- the
// runtime word carries no Int/Float tag. When that type is `Float`, remap the int prim
// (`prim_add`, `prim_lt`, ...) to its boxed-double variant (`prim_fadd`, `prim_flt`,
// ...). `prim_eq` needs no remap: `val_eq` already dispatches on the boxed float's kind.
fn float_prim(prim: &str) -> Option<&'static str> {
    Some(match prim {
        "prim_add" => "prim_fadd",
        "prim_sub" => "prim_fsub",
        "prim_mul" => "prim_fmul",
        "prim_div" => "prim_fdiv",
        "prim_mod" => "prim_fmod",
        "prim_lt" => "prim_flt",
        "prim_gt" => "prim_fgt",
        "prim_le" => "prim_fle",
        "prim_ge" => "prim_fge",
        "prim_neg" => "prim_fneg",
        _otherwise => return None,
    })
}

// `and`/`or`/`xor` are logical on Bool and bitwise on Int. `builtin_prim` yields the
// Bool (logical) prim; when the operands' static type is Int, remap to the bitwise
// variant (`prim_band`, ...). Mirrors `float_prim` for the arithmetic operators.
fn bitwise_prim(prim: &str) -> Option<&'static str> {
    Some(match prim {
        "prim_and" => "prim_band",
        "prim_or" => "prim_bor",
        "prim_xor" => "prim_bxor",
        "prim_not" => "prim_bnot",
        _otherwise => return None,
    })
}

// The element type `τ` of an `Array τ`. The array type reaches codegen either as
// the dedicated `Type::Array` or, as the typer actually builds a non-empty array
// literal (`infer_array`), an application of the builtin `Array` constructor:
// `Apply { Constructor(QualifiedName::builtin("Array")), τ }`. Identity is by
// QualifiedName equality against that same canonical constructor.
fn array_element_type(ty: &Type) -> Option<&Type> {
    match ty {
        Type::Array(element) => Some(element),
        Type::Apply {
            constructor,
            argument,
        } if matches!(constructor.as_ref(), Type::Constructor(name) if *name == QualifiedName::builtin("Array")) => {
            Some(argument)
        }
        _ => None,
    }
}

fn mutable_array_element_type(ty: &Type) -> Option<&Type> {
    match ty {
        Type::Apply {
            constructor,
            argument,
        } if matches!(constructor.as_ref(), Type::Constructor(name)
            if surface_name(name).ends_with("Stdlib_Data_Array_Mutable_Array")) =>
        {
            Some(argument)
        }
        _ => None,
    }
}

/// Peel `T a b` into `(T, [a, b])` in source order.
fn applied_type(ty: &Type) -> Option<(&QualifiedName, Vec<Type>)> {
    let mut head = ty;
    let mut arguments = Vec::new();
    while let Type::Apply {
        constructor,
        argument,
    } = head
    {
        arguments.push((**argument).clone());
        head = constructor;
    }
    arguments.reverse();
    match head {
        Type::Constructor(name) => Some((name, arguments)),
        _ => None,
    }
}

/// Instantiate a declaration-side type expression with the concrete arguments
/// of the nominal type currently being laid out.
fn instantiate_type_expression<A>(
    expression: &TypeExpression<A, QualifiedName>,
    bindings: &HashMap<crate::parser::Identifier, Type>,
) -> Option<Type> {
    match expression {
        TypeExpression::Constructor(_, name) => Some(Type::Constructor(name.clone())),
        TypeExpression::Parameter(_, parameter) => bindings.get(parameter).cloned(),
        TypeExpression::Apply(_, application) => Some(Type::Apply {
            constructor: instantiate_type_expression(&application.function, bindings)?.into(),
            argument: instantiate_type_expression(&application.argument, bindings)?.into(),
        }),
        TypeExpression::Arrow(_, arrow) => Some(Type::Arrow {
            domain: instantiate_type_expression(&arrow.domain, bindings)?.into(),
            codomain: instantiate_type_expression(&arrow.codomain, bindings)?.into(),
        }),
        TypeExpression::Tuple(_, tuple) => Some(Type::Tuple(crate::typer::TupleType(
            tuple
                .0
                .iter()
                .map(|element| instantiate_type_expression(element, bindings))
                .collect::<Option<Vec<_>>>()?,
        ))),
    }
}

// Peel type ascriptions off an expression -- they are erased at codegen. Used by
// the flat-record path to see through to a `Record`/`Project` node.
fn strip_ascription(mut expr: &Expr) -> &Expr {
    while let Expr::Ascription(_, ascription) = expr {
        expr = &ascription.ascribed_tree;
    }
    expr
}

fn raw_array_get_arguments(expr: &Expr) -> Option<(&Expr, &Expr)> {
    let mut head = expr;
    let mut arguments = Vec::new();
    while let Expr::Apply(_, application) = head {
        arguments.push(application.argument.as_ref());
        head = application.function.as_ref();
    }
    arguments.reverse();
    if arguments.len() != 2 {
        return None;
    }
    let name = match head {
        Expr::Variable(_, Identifier::Global(name)) => name.as_ref(),
        Expr::InvokeBridge(_, bridge) => &bridge.qualified_name,
        _ => return None,
    };
    surface_name(name)
        .ends_with("Stdlib_Data_Array_Mutable_Array_raw_get_unchecked")
        .then_some((arguments[0], arguments[1]))
}

fn raw_array_set_arguments(expr: &Expr) -> Option<(&Expr, &Expr, &Expr)> {
    let mut head = strip_ascription(expr);
    let mut arguments = Vec::new();
    while let Expr::Apply(_, application) = head {
        arguments.push(application.argument.as_ref());
        head = strip_ascription(&application.function);
    }
    arguments.reverse();
    if arguments.len() != 3 {
        return None;
    }
    let name = match head {
        Expr::Variable(_, Identifier::Global(name)) => name.as_ref(),
        Expr::InvokeBridge(_, bridge) => &bridge.qualified_name,
        _ => return None,
    };
    surface_name(name)
        .ends_with("Stdlib_Data_Array_Mutable_Array_raw_set_unchecked")
        .then_some((arguments[0], arguments[1], arguments[2]))
}

fn projection_root_and_selectors(
    projection: &phase::Projection<Closed>,
) -> (&Expr, Vec<ProductElement>) {
    let mut selectors = vec![projection.select.clone()];
    let mut root = strip_ascription(&projection.base);
    while let Expr::Project(_, inner) = root {
        selectors.push(inner.select.clone());
        root = strip_ascription(&inner.base);
    }
    selectors.reverse();
    (root, selectors)
}

// Fresh scrutinee temporaries for `deconstruct`. A monotonic counter keeps each
// match's binding distinct from every other (including nested matches).
static MATCH_ID: AtomicUsize = AtomicUsize::new(0);

impl lambda_lift::Program {
    // Emit a complete, self-contained C translation unit: every lifted lambda
    // becomes a `Value f(Value self, Value arg)` function, every top-level
    // definition a `Value` global initialised once in `startup`, and `main`
    // runs the program's `start` entry point. Builtin definitions are omitted --
    // the runtime (`c/runtime.c`) provides them.
    pub fn generate_code(&self, out: &mut CodeBuffer) -> fmt::Result {
        writeln!(out, "#include \"runtime.h\"")?;
        writeln!(out, "#include \"gc.h\"\n")?;

        // Forward declarations, so functions and globals can reference each
        // other (and themselves) regardless of definition order.
        for LiftedFunction { name, .. } in &self.functions {
            writeln!(out, "Value {}(Value self, Value l0);", c_name(name))?;
        }
        for Worker { name, params, .. } in &self.workers {
            let signature = vec!["Value"; *params].join(", ");
            writeln!(out, "Value {}_worker({});", c_name(name), signature)?;
        }
        for ChainWorker { head, .. } in &self.chain_workers {
            writeln!(
                out,
                "Value {}_uworker(Value self, Value *args);",
                c_name(head)
            )?;
        }
        for TopLevelBinding { name, .. } in &self.globals {
            if !is_builtin(name) {
                writeln!(out, "Value {};", c_name(name))?;
            }
        }

        // Foreign globals live in the companion `<Module>.c` (defined by the
        // `FOREIGN_DECL` macro alongside a `<name>__init` builder and, for arity
        // >= 1, an uncurried `<name>_worker`). Declare them here so the emitted
        // code can reference the value, call the builder, and direct-call the
        // worker at saturated call sites.
        for name in &self.foreign {
            // The `memory_layout` marker has no companion C global: its references are
            // synthesised inline as layout dictionaries (see `compile_layout_dict`).
            if *name == memory_layout_evidence_name() {
                continue;
            }
            writeln!(out, "extern Value {0};", c_name(name))?;
            writeln!(out, "extern Value {0}__init(void);", c_name(name))?;
            if let Some(&arity) = self.arities.get(name) {
                if arity > 0 {
                    let params = vec!["Value"; arity].join(", ");
                    writeln!(out, "extern Value {0}_worker({1});", c_name(name), params)?;
                }
            }
        }
        writeln!(out)?;

        // A single-stage closure that is BUILT AND IMMEDIATELY APPLIED needs no heap
        // environment: its captures can be ordinary arguments. The lifted body is already
        // a `for(;;)` loop -- the closure was never the control flow, only the parameter
        // block -- so this removes one allocation per entry to such a loop.
        //
        // Deliberately done HERE, in codegen, rather than as a source-to-source pass:
        // rewriting the loop's captures into parameters before the flat-array analyses
        // run makes them lose track of the element and materialise it, which cost far
        // more than the closure saved. By this point those analyses have already run.
        for LiftedFunction { name, code, .. } in &self.functions {
            CAPTURE_PLACES.with(|places| *places.borrow_mut() = self.capture_places(name));
            tracing::trace!("generate_code: {name}");
            writeln!(out, "Value {}(Value self, Value l0) {{", c_name(name))?;
            writeln!(out, "  (void)self; (void)l0;")?;
            // A lifted lambda that tail-calls itself (through `self`) is emitted as a loop, so a
            // deep recursion -- e.g. a strictified IO loop after `deforest_io` -- runs in constant
            // stack instead of `apply(self, …)` per turn. Its captures live in `self`, which is
            // loop-invariant, so only the parameter is reassigned. Arity is 1 (a lifted frame binds
            // one parameter); a curried self-call applies more and simply does not match.
            let loopify = std::env::var_os("MARM_NO_LOOPIFY").is_none();
            if loopify && self.has_tail_self_call(SelfCall::SelfRef, 1, code) {
                write!(out, "  for (;;) {{ ")?;
                self.compile_tail(SelfCall::SelfRef, 1, code, out)?;
                writeln!(out, " }}\n}}\n")?;
            } else {
                write!(out, "  return ")?;
                self.compile_expr(code, out)?;
                writeln!(out, ";\n}}\n")?;
            }
        }

        // Uncurried workers: an N-ary function whose parameters are the flat frame
        // `l0..l{N-1}`. No `self` -- these are closure-free, so their bodies carry
        // no captures. `compile_apply` calls them directly at saturated call sites.
        CAPTURE_PLACES.with(|places| places.borrow_mut().clear());
        for Worker { name, params, body } in &self.workers {
            let signature = (0..*params)
                .map(|i| format!("Value l{i}"))
                .collect::<Vec<_>>()
                .join(", ");
            writeln!(out, "Value {}_worker({}) {{", c_name(name), signature)?;
            for i in 0..*params {
                write!(out, "  (void)l{i};")?;
            }
            // A worker that tail-calls itself is emitted as a loop (each self
            // tail-call becomes reassign-params + `continue`), so the recursion
            // runs in constant stack instead of relying on clang's unreliable
            // tail-call elimination. Workers with no self-tail-call keep the
            // plain `return <expr>;` form (output-identical to before).
            let loopify = std::env::var_os("MARM_NO_LOOPIFY").is_none();
            if loopify && self.has_tail_self_call(SelfCall::Named(name), *params, body) {
                write!(out, "\n  for (;;) {{ ")?;
                self.compile_tail(SelfCall::Named(name), *params, body, out)?;
                writeln!(out, " }}\n}}\n")?;
            } else {
                write!(out, "\n  return ")?;
                self.compile_expr(body, out)?;
                writeln!(out, ";\n}}\n")?;
            }
        }

        // Chain workers: the uncurried entry a chain-head closure carries, run by
        // `apply_n` when the head is applied to exactly `arity` arguments. `self`
        // is the head closure (so `env_get(self, i)` still reads the chain's
        // captures); the flattened parameters arrive in `args[0..arity]`, which we
        // name `l0..l{arity-1}` to match the frame the flattened body expects.
        for ChainWorker { head, arity, body } in &self.chain_workers {
            CAPTURE_PLACES.with(|places| *places.borrow_mut() = self.capture_places(head));
            writeln!(
                out,
                "Value {}_uworker(Value self, Value *args) {{",
                c_name(head)
            )?;
            write!(out, "  (void)self;")?;
            for i in 0..*arity {
                write!(out, " Value l{i} = args[{i}];")?;
            }
            // Same loopification as the arity-1 lifted lambda, for an uncurried recursive frame:
            // a saturated tail `self`-call reassigns `l0..l{arity-1}` and continues.
            let loopify = std::env::var_os("MARM_NO_LOOPIFY").is_none();
            if loopify && self.has_tail_self_call(SelfCall::SelfRef, *arity, body) {
                write!(out, "\n  for (;;) {{ ")?;
                self.compile_tail(SelfCall::SelfRef, *arity, body, out)?;
                writeln!(out, " }}\n}}\n")?;
            } else {
                write!(out, "\n  return ")?;
                self.compile_expr(body, out)?;
                writeln!(out, ";\n}}\n")?;
            }
        }

        CAPTURE_PLACES.with(|places| places.borrow_mut().clear());
        writeln!(out, "void startup(void) {{")?;
        // Foreign closures init first: their `__init` builders are self-contained
        // (they build a closure or compute a C-side constant and never read a user
        // global), and an *eager* user global may APPLY a foreign at its own init
        // (e.g. `char_width := Array.get_element Char_Width`), which dereferences
        // the foreign's Value -- so it must already hold its closure, not null.
        // Runs after `gc_init`/`runtime_init` (see `main`), so `mk_closure` is safe.
        for name in &self.foreign {
            if *name == memory_layout_evidence_name() {
                continue; // synthesised inline; no companion global to initialise
            }
            writeln!(out, "  {0} = {0}__init();", c_name(name))?;
        }
        // User globals then init in dependency order (`in_resolvable_order`): a
        // binding that merely names another global's closure is order-immaterial,
        // but one that eagerly applies another user global depends on that global
        // already being built, which the ordering guarantees.
        for TopLevelBinding { name, value, .. } in &self.globals {
            if is_builtin(name) {
                continue;
            }
            write!(out, "  {} = ", c_name(name))?;
            self.compile_expr(value, out)?;
            writeln!(out, ";")?;
        }
        writeln!(out, "}}\n")?;

        // The GC's global-root table: the address of every top-level Value the
        // collector must keep. Builtins are rooted inside the runtime, so only
        // user globals and foreign closures go here. A one-element `{0}` avoids a
        // zero-length array when the program has no top-level values of its own.
        let root_names = self
            .globals
            .iter()
            .map(|b| &b.name)
            .filter(|name| !is_builtin(name))
            .chain(self.foreign.iter())
            // The `memory_layout` marker has no companion Value global to root.
            .filter(|name| **name != memory_layout_evidence_name())
            .collect::<Vec<_>>();
        writeln!(out, "Value *const gc_user_roots[] = {{")?;
        if root_names.is_empty() {
            writeln!(out, "  0")?;
        } else {
            for name in &root_names {
                writeln!(out, "  &{},", c_name(name))?;
            }
        }
        writeln!(out, "}};")?;
        writeln!(
            out,
            "const size_t gc_user_roots_count = {};\n",
            root_names.len()
        )?;

        writeln!(out, "int main(void) {{")?;
        writeln!(out, "  int gc_anchor;")?;
        writeln!(out, "  gc_init(&gc_anchor);")?;
        writeln!(out, "  runtime_init();")?;
        writeln!(out, "  startup();")?;
        // `start` receives the process's start time in milliseconds. The entry is
        // synthesised as `start <arg>`; call the closure with the clock instead.
        match &self.start {
            Expr::Apply(_, the) => {
                write!(out, "  apply(")?;
                self.compile_expr(&the.function, out)?;
                writeln!(out, ", VInt(now_millis()));")?;
            }
            other => {
                write!(out, "  ")?;
                self.compile_expr(other, out)?;
                writeln!(out, ";")?;
            }
        }
        writeln!(out, "  return 0;\n}}")?;
        Ok(())
    }

    // Compile an expression to a single C expression of type `Value`. Control
    // constructs stay expressions: `if` is a ternary, `let` a GCC statement
    // expression, sequencing the comma operator.
    fn compile_expr(&self, expr: &Expr, code: &mut CodeBuffer) -> fmt::Result {
        match expr {
            // The compiler-synthesised `memory_layout` marker (evidence for a ground
            // `Memory_Layout τ`) is not a real global: emit the layout dictionary for
            // `τ`, recovered from this reference's inferred type.
            Expr::Variable(a, Identifier::Global(q)) if **q == memory_layout_evidence_name() => {
                self.compile_layout_dict(&a.type_info.inferred_type, code)
            }
            Expr::Variable(_, the) => write!(code, "{}", self.compile_var(the)),
            Expr::InvokeBridge(_, the) => write!(code, "{}", c_name(&the.qualified_name)),
            Expr::Constant(_, the) => write!(code, "{}", self.compile_constant(the)),
            Expr::RecursiveLambda(_, _the) => panic!("lambdas are lifted"),
            Expr::Lambda(_, _the) => panic!("lambdas are lifted"),
            Expr::Apply(a, the) => self.compile_apply(a, the, code),
            Expr::Let(_, the) => self.compile_let(the, code),
            Expr::Tuple(_, the) => self.compile_tuple(&the.elements, code),
            Expr::Record(a, the) => self.compile_record(a, the, code),
            Expr::RecordUpdate(a, the) => self.compile_record_update(a, the, code),
            Expr::Inject(_, the) => self.compile_inject(the, code),
            Expr::Array(a, the) => self.compile_array(a, &the.elements, code),
            Expr::Project(a, the) => self.compile_projection(a, the, code),
            Expr::Sequence(_, the) => self.compile_sequence(the, code),
            Expr::Deconstruct(_, the) => self.compile_deconstruct(the, code),
            Expr::If(_, the) => self.compile_if(the, code),
            Expr::Interpolate(_, the) => self.compile_interpolate(&the.0, code),
            Expr::Ascription(_, the) => self.compile_expr(&the.ascribed_tree, code),
            Expr::MakeClosure(_, the) => self.compile_closure(the, code),
        }
    }

    fn compile_tuple(&self, elements: &[Rc<Expr>], code: &mut CodeBuffer) -> fmt::Result {
        // Fixed-arity `mk_tupleN(e0, ..)` for small tuples (no variadic tax); the
        // `mk_tuple(N, e0, ..)` fallback carries the count for larger ones.
        let mut written = if elements.len() <= 4 {
            write!(code, "mk_tuple{}(", elements.len())?;
            false
        } else {
            write!(code, "mk_tuple({}", elements.len())?;
            true
        };
        for element in elements {
            if written {
                write!(code, ", ")?;
            }
            written = true;
            self.compile_expr(element, code)?;
        }
        write!(code, ")")
    }

    // A readonly `[...]` array literal builds a flat array: one heap object with
    // its elements' leaves inline (an array of products is one object), exactly
    // like `Mutable_Array` -- the sole other `Array` source. The elements are
    // evaluated into a stack `(Value[]){...}` block that `mk_flat_array_from`
    // reads, discovering the element shape from element 0. Access stays through
    // `Array.get`/`length` (arrays are never `proj`'d), so the layout is opaque.
    fn compile_array(
        &self,
        annotation: &CaptureInfo,
        elements: &[Rc<Expr>],
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        if elements.is_empty() {
            return write!(code, "mk_flat_array_from(0, 0)");
        }
        // When the element type is a flat sum, the runtime cannot discover the
        // element shape from element 0 (it never sees the other variants), so emit
        // a type-driven shape and take the shaped constructor. Every other element
        // type keeps the element-0 path unchanged (=> byte-identical).
        let shape = array_element_type(&annotation.type_info.inferred_type)
            .and_then(|element| self.flat_array_shape(element));
        let constructor = if shape.is_some() {
            "mk_flat_array_from_shaped"
        } else {
            "mk_flat_array_from"
        };
        write!(code, "{constructor}({}, (Value[]){{", elements.len())?;
        for (i, element) in elements.iter().enumerate() {
            if i > 0 {
                write!(code, ", ")?;
            }
            self.compile_expr(element, code)?;
        }
        write!(code, "}}")?;
        if let Some(shape) = shape {
            write!(code, ", (int64_t[]){{")?;
            for (i, entry) in shape.iter().enumerate() {
                if i > 0 {
                    write!(code, ", ")?;
                }
                write!(code, "{entry}")?;
            }
            write!(code, "}}, {}", shape.len())?;
        }
        write!(code, ")")
    }

    /// Derive the complete runtime shape of a ground array element. Nominal type
    /// declarations are retained through lambda lifting so this can preserve
    /// nested record/tuple/sum structure instead of reducing every constructor
    /// field to a width. Recursive knots and unsupported structural inference
    /// types stay boxed leaves. Oversized encodings fall back to element-zero
    /// discovery, preserving the old representation.
    fn flat_array_shape(&self, element: &Type) -> Option<Vec<i64>> {
        if std::env::var_os("MARM_NOFLAT").is_some() || !element.variables().is_empty() {
            return None;
        }
        let result = self.runtime_shape(element, &mut Vec::new());
        let mut encoded = Vec::new();
        result.shape.encode(&mut encoded);
        (encoded.len() <= FLAT_MAX_SHAPE).then_some(encoded)
    }

    fn runtime_shape(&self, ty: &Type, on_path: &mut Vec<Type>) -> ShapeResult {
        match ty {
            Type::Tuple(tuple) => {
                let children = tuple
                    .elements()
                    .iter()
                    .map(|element| self.runtime_shape(element, on_path))
                    .collect::<Vec<_>>();
                ShapeResult {
                    reaches_enclosing_type: children
                        .iter()
                        .any(|child| child.reaches_enclosing_type),
                    shape: RuntimeShape::Product(
                        children.into_iter().map(|child| child.shape).collect(),
                    ),
                }
            }
            Type::Constructor(name) => self.runtime_named_shape(name, &[], on_path),
            Type::Apply { .. } => {
                let Some((name, arguments)) = applied_type(ty) else {
                    return ShapeResult {
                        shape: RuntimeShape::Leaf,
                        reaches_enclosing_type: false,
                    };
                };
                self.runtime_named_shape(name, &arguments, on_path)
            }
            Type::Coproduct(coproduct) => {
                let constructors = coproduct.constructors().collect::<Vec<_>>();
                let Some(max_tag) = constructors
                    .iter()
                    .filter_map(|(name, _)| self.constructor_tags.get(name).copied())
                    .max()
                else {
                    return ShapeResult {
                        shape: RuntimeShape::Leaf,
                        reaches_enclosing_type: false,
                    };
                };
                let mut variants = Vec::new();
                variants.resize_with(max_tag as usize + 1, || None);
                for (name, fields) in constructors {
                    let Some(&tag) = self.constructor_tags.get(name) else {
                        return ShapeResult {
                            shape: RuntimeShape::Leaf,
                            reaches_enclosing_type: false,
                        };
                    };
                    variants[tag as usize] = Some(
                        fields
                            .iter()
                            .map(|field| self.runtime_shape(field, on_path))
                            .collect::<Vec<_>>(),
                    );
                }
                if variants.iter().any(Option::is_none) {
                    ShapeResult {
                        shape: RuntimeShape::Leaf,
                        reaches_enclosing_type: false,
                    }
                } else {
                    self.runtime_sum_shape(variants.into_iter().map(Option::unwrap).collect())
                }
            }
            Type::Variable(..)
            | Type::Base(..)
            | Type::Arrow { .. }
            | Type::Record(..)
            | Type::Array(..) => ShapeResult {
                shape: RuntimeShape::Leaf,
                reaches_enclosing_type: false,
            },
        }
    }

    /// Whether every word of `ty`'s packed-array representation is an immediate
    /// (or the zero niche). A store of such a word cannot create an old-to-young
    /// heap edge and therefore needs no generational write barrier.
    fn packed_type_is_immediate(&self, ty: &Type) -> bool {
        self.packed_type_is_immediate_on_path(ty, &mut Vec::new())
    }

    fn packed_type_is_immediate_on_path(&self, ty: &Type, on_path: &mut Vec<Type>) -> bool {
        match ty {
            Type::Base(BaseType::Int | BaseType::Bool | BaseType::Unit | BaseType::Char) => true,
            Type::Tuple(tuple) => tuple
                .elements()
                .iter()
                .all(|element| self.packed_type_is_immediate_on_path(element, on_path)),
            Type::Constructor(name) => self.packed_named_type_is_immediate(name, &[], on_path),
            Type::Apply { .. } => applied_type(ty).is_some_and(|(name, arguments)| {
                self.packed_named_type_is_immediate(name, &arguments, on_path)
            }),
            // Float is boxed; Text/Array/arrows and unresolved structural or
            // polymorphic types may contain pointers. Stay conservative.
            Type::Variable(..)
            | Type::Base(..)
            | Type::Arrow { .. }
            | Type::Record(..)
            | Type::Coproduct(..)
            | Type::Array(..) => false,
        }
    }

    fn packed_named_type_is_immediate(
        &self,
        name: &QualifiedName,
        arguments: &[Type],
        on_path: &mut Vec<Type>,
    ) -> bool {
        let instantiated = arguments.iter().cloned().fold(
            Type::Constructor(name.clone()),
            |constructor, argument| Type::Apply {
                constructor: Box::new(constructor),
                argument: Box::new(argument),
            },
        );
        if on_path.contains(&instantiated) {
            return false;
        }
        let Some(definition) = self.type_definitions.get(name) else {
            return false;
        };
        if let TypeDefinition::BaseType(base_type) = definition {
            return matches!(
                base_type,
                BaseType::Int | BaseType::Bool | BaseType::Unit | BaseType::Char
            );
        }
        let parameters = match definition {
            TypeDefinition::Record(record) => &record.type_parameters,
            TypeDefinition::Coproduct(coproduct) => &coproduct.type_parameters,
            TypeDefinition::Alias(alias) => &alias.type_parameters,
            TypeDefinition::Signature(..) => return false,
            TypeDefinition::BaseType(..) => unreachable!("handled above"),
        };
        let bindings = parameters
            .iter()
            .zip(arguments)
            .map(|(parameter, argument)| (parameter.name.clone(), argument.clone()))
            .collect::<HashMap<_, _>>();

        on_path.push(instantiated.clone());
        let result = match definition {
            TypeDefinition::Record(record) => record.fields.iter().all(|field| {
                instantiate_type_expression(&field.type_signature.body, &bindings).is_some_and(
                    |field_type| self.packed_type_is_immediate_on_path(&field_type, on_path),
                )
            }),
            TypeDefinition::Coproduct(coproduct) => {
                let newtype = matches!(coproduct.constructors.as_slice(), [only]
                    if only.signature.len() == 1);
                let packed_inline = newtype
                    || !matches!(
                        self.runtime_shape(&instantiated, &mut Vec::new()).shape,
                        RuntimeShape::Leaf
                    );
                packed_inline
                    && coproduct.constructors.iter().all(|constructor| {
                        constructor.signature.iter().all(|field| {
                            instantiate_type_expression(field, &bindings).is_some_and(
                                |field_type| {
                                    self.packed_type_is_immediate_on_path(&field_type, on_path)
                                },
                            )
                        })
                    })
            }
            TypeDefinition::Alias(alias) => instantiate_type_expression(&alias.body, &bindings)
                .is_some_and(|aliased| self.packed_type_is_immediate_on_path(&aliased, on_path)),
            TypeDefinition::Signature(..) | TypeDefinition::BaseType(..) => false,
        };
        on_path.pop();
        result
    }

    fn runtime_sum_shape(&self, variants: Vec<Vec<ShapeResult>>) -> ShapeResult {
        let recursive = variants
            .iter()
            .flatten()
            .any(|field| field.reaches_enclosing_type);
        let too_many_fields = variants
            .iter()
            .any(|variant| variant.len() > FLAT_MAX_FIELDS);
        if recursive || too_many_fields {
            return ShapeResult {
                shape: RuntimeShape::Leaf,
                reaches_enclosing_type: false,
            };
        }
        let variants = variants
            .into_iter()
            .map(|variant| variant.into_iter().map(|field| field.shape).collect())
            .collect::<Vec<Vec<_>>>();
        if variants.len() == 2 {
            let niche_tag = variants.iter().position(Vec::is_empty);
            let payload_tag = variants.iter().position(|variant| !variant.is_empty());
            if let (Some(niche_tag), Some(payload_tag)) = (niche_tag, payload_tag) {
                if niche_tag != payload_tag {
                    let payload_fields = variants[payload_tag].clone();
                    let payload_shape = RuntimeShape::Product(payload_fields.clone());
                    if let Some(niche_offset) = payload_shape.zero_niche() {
                        return ShapeResult {
                            shape: RuntimeShape::NicheSum {
                                niche_tag,
                                payload_tag,
                                niche_offset,
                                payload_fields,
                            },
                            reaches_enclosing_type: false,
                        };
                    }
                }
            }
        }
        let payload_words = variants
            .iter()
            .map(|variant| variant.iter().map(RuntimeShape::stored_words).sum())
            .max()
            .unwrap_or(0);
        ShapeResult {
            shape: RuntimeShape::Sum {
                payload_words,
                variants,
            },
            reaches_enclosing_type: false,
        }
    }

    fn runtime_named_shape(
        &self,
        name: &QualifiedName,
        arguments: &[Type],
        on_path: &mut Vec<Type>,
    ) -> ShapeResult {
        let instantiated = arguments.iter().cloned().fold(
            Type::Constructor(name.clone()),
            |constructor, argument| Type::Apply {
                constructor: Box::new(constructor),
                argument: Box::new(argument),
            },
        );
        if on_path.contains(&instantiated) {
            return ShapeResult {
                shape: RuntimeShape::Leaf,
                reaches_enclosing_type: true,
            };
        }
        let Some(definition) = self.type_definitions.get(name) else {
            return ShapeResult {
                shape: RuntimeShape::Leaf,
                reaches_enclosing_type: false,
            };
        };
        let parameters = match definition {
            TypeDefinition::Record(record) => &record.type_parameters,
            TypeDefinition::Signature(signature) => &signature.vtable.type_parameters,
            TypeDefinition::Coproduct(coproduct) => &coproduct.type_parameters,
            TypeDefinition::Alias(alias) => &alias.type_parameters,
            TypeDefinition::BaseType(..) => {
                return ShapeResult {
                    shape: RuntimeShape::Leaf,
                    reaches_enclosing_type: false,
                };
            }
        };
        let bindings = parameters
            .iter()
            .zip(arguments)
            .map(|(parameter, argument)| (parameter.name.clone(), argument.clone()))
            .collect::<HashMap<_, _>>();

        on_path.push(instantiated.clone());
        let result = match definition {
            TypeDefinition::Record(record) => {
                // `compile_record` itself splats a record whenever any nested
                // field is wider than one word. A shaped array must describe
                // that canonical value as the already-flat tuple it actually is;
                // otherwise `flatten` would try to descend into an intermediate
                // tuple that was deliberately never allocated.
                if let Some(widths) = self.flat_widths(&instantiated) {
                    if widths.iter().any(|width| *width > 1) {
                        return ShapeResult {
                            shape: RuntimeShape::Product(
                                (0..widths.iter().sum())
                                    .map(|_| RuntimeShape::Leaf)
                                    .collect(),
                            ),
                            reaches_enclosing_type: false,
                        };
                    }
                }
                let mut fields = record.fields.iter().collect::<Vec<_>>();
                fields.sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name));
                let children = fields
                    .into_iter()
                    .map(|field| {
                        self.runtime_type_expression_shape(
                            &field.type_signature.body,
                            &bindings,
                            on_path,
                        )
                    })
                    .collect::<Vec<_>>();
                ShapeResult {
                    reaches_enclosing_type: children
                        .iter()
                        .any(|child| child.reaches_enclosing_type),
                    shape: RuntimeShape::Product(
                        children.into_iter().map(|child| child.shape).collect(),
                    ),
                }
            }
            TypeDefinition::Coproduct(coproduct) => {
                if coproduct.constructors.is_empty() {
                    // An opaque imported type (Text is the important case) has
                    // no visible constructors in the retained declaration. Its
                    // representation cannot be derived here, so keep the
                    // canonical value as one pointer word. Encoding it as a
                    // zero-variant sum would make `flatten` call `data_tag` on an
                    // arbitrary opaque object.
                    ShapeResult {
                        shape: RuntimeShape::Leaf,
                        reaches_enclosing_type: false,
                    }
                } else if let [only] = coproduct.constructors.as_slice()
                    && only.signature.len() == 1
                {
                    // Newtypes are erased, so their array shape is exactly their field's.
                    let child =
                        self.runtime_type_expression_shape(&only.signature[0], &bindings, on_path);
                    ShapeResult {
                        shape: child.shape,
                        reaches_enclosing_type: false,
                    }
                } else {
                    let variants = coproduct
                        .constructors
                        .iter()
                        .map(|constructor| {
                            constructor
                                .signature
                                .iter()
                                .map(|field| {
                                    self.runtime_type_expression_shape(field, &bindings, on_path)
                                })
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>();
                    let recursive = variants
                        .iter()
                        .flatten()
                        .any(|field| field.reaches_enclosing_type);
                    let too_many_fields = variants
                        .iter()
                        .any(|variant| variant.len() > FLAT_MAX_FIELDS);
                    if recursive || too_many_fields {
                        // A recursive sum remains one canonical pointer. Boxing it
                        // here closes the recursion knot for any enclosing layout.
                        ShapeResult {
                            shape: RuntimeShape::Leaf,
                            reaches_enclosing_type: false,
                        }
                    } else {
                        let variants = variants
                            .into_iter()
                            .map(|variant| variant.into_iter().map(|field| field.shape).collect())
                            .collect::<Vec<Vec<_>>>();
                        let niche = if variants.len() == 2 {
                            let niche_tag = variants.iter().position(Vec::is_empty);
                            let payload_tag =
                                variants.iter().position(|variant| !variant.is_empty());
                            match (niche_tag, payload_tag) {
                                (Some(niche_tag), Some(payload_tag))
                                    if niche_tag != payload_tag =>
                                {
                                    let payload_fields = variants[payload_tag].clone();
                                    let payload_shape =
                                        RuntimeShape::Product(payload_fields.clone());
                                    payload_shape.zero_niche().map(|niche_offset| {
                                        RuntimeShape::NicheSum {
                                            niche_tag,
                                            payload_tag,
                                            niche_offset,
                                            payload_fields,
                                        }
                                    })
                                }
                                _ => None,
                            }
                        } else {
                            None
                        };
                        if let Some(shape) = niche {
                            return ShapeResult {
                                shape,
                                reaches_enclosing_type: false,
                            };
                        }
                        let payload_words = variants
                            .iter()
                            .map(|variant| variant.iter().map(RuntimeShape::stored_words).sum())
                            .max()
                            .unwrap_or(0);
                        ShapeResult {
                            shape: RuntimeShape::Sum {
                                payload_words,
                                variants,
                            },
                            reaches_enclosing_type: false,
                        }
                    }
                }
            }
            TypeDefinition::Alias(alias) => {
                self.runtime_type_expression_shape(&alias.body, &bindings, on_path)
            }
            TypeDefinition::Signature(..) | TypeDefinition::BaseType(..) => ShapeResult {
                shape: RuntimeShape::Leaf,
                reaches_enclosing_type: false,
            },
        };
        on_path.pop();
        result
    }

    fn runtime_type_expression_shape<A>(
        &self,
        expression: &TypeExpression<A, QualifiedName>,
        bindings: &HashMap<crate::parser::Identifier, Type>,
        on_path: &mut Vec<Type>,
    ) -> ShapeResult {
        let Some(ty) = instantiate_type_expression(expression, bindings) else {
            return ShapeResult {
                shape: RuntimeShape::Leaf,
                reaches_enclosing_type: false,
            };
        };
        self.runtime_shape(&ty, on_path)
    }

    // Emit the `Memory_Layout τ` dictionary for the synthesised `memory_layout` marker,
    // whose inferred type is `Memory_Layout τ`. The dictionary is a one-field record
    // `{ shape :: Raw_Shape }` (a 1-tuple); `Raw_Shape` is a static MARM_ETERNAL byte
    // body holding `[slen, shape...]` that `raw_generate_shaped` reads. A τ with no flat
    // sum shape reports the leaf shape `[0]` (ML3 totality: the element stays one boxed
    // word, so a generated array is byte-identical to the element-0 discovery path).
    fn compile_layout_dict(&self, dict_type: &Type, code: &mut CodeBuffer) -> fmt::Result {
        let element = match dict_type {
            Type::Apply { argument, .. } => Some(argument.as_ref()),
            _ => None,
        };
        // No flat-sum shape -> an EMPTY shape (slen 0), the runtime's signal to keep
        // element-0 discovery (so a product/scalar element still flattens exactly as
        // before -- byte-identical, no regression). Only a fully GROUND sum element
        // carries a shape: a type still holding variables (a polymorphic caller's
        // element type, un-monomorphised at codegen) stays on the element-0 path, so
        // its representation is unchanged (ML3 totality: an abstract payload is boxed).
        let shape = element
            .and_then(|t| self.flat_array_shape(t))
            .unwrap_or_default();
        let words = shape.len() + 1; // leading `slen` word, then the entries
        write!(
            code,
            "mk_tuple(1, ({{ static const struct {{ GcHeader gch; int64_t s[{words}]; }} __ml = \
             {{{{{}, 0, OBJ_BYTES, MARM_ETERNAL}}, {{{}",
            words * 8,
            shape.len()
        )?;
        for entry in &shape {
            write!(code, ", {entry}")?;
        }
        write!(code, "}}}}; VObject((void *)__ml.s); }}))")
    }

    // A constructor value (sum type) is a `Data` object: an integer tag (the
    // constructor's ordinal within its type) followed by its arguments inline.
    // Pattern matching compares the tag with `==` (see `Coproduct` below), so the
    // tag need only be unique among its own type's constructors. Nullary
    // constructors are just a tag with no fields.
    fn compile_inject(&self, the: &phase::Injection<Closed>, code: &mut CodeBuffer) -> fmt::Result {
        // A newtype (single-ctor single-field) is erased: the wrapper IS its field,
        // so emit the sole argument directly -- no `Data` box. A saturated `Inject`
        // of a newtype always has exactly one argument.
        if self.newtype_constructors.contains(&the.constructor) {
            return self.compile_expr(&the.arguments[0], code);
        }
        let tag = self.constructor_tag(&the.constructor);
        let n = the.arguments.len();
        // A nullary constructor has no fields, so its `Data` is identical and immutable
        // for its tag -- emit one static `MARM_ETERNAL` instance (shared per use site)
        // instead of allocating a fresh `Data` on every mention. Mirrors the capture-
        // free `STATIC_CLOSURE0` and the borrowed-string literal.
        if n == 0 {
            return write!(code, "STATIC_DATA0({tag})");
        }
        // The tag always precedes the fields, so fields keep their leading comma
        // in both forms; only the callee name / count prefix differs.
        if n <= 4 {
            write!(code, "mk_data{n}({tag}")?;
        } else {
            write!(code, "mk_data({tag}, {n}")?;
        }
        for argument in &the.arguments {
            write!(code, ", ")?;
            self.compile_expr(argument, code)?;
        }
        write!(code, ")")
    }

    // -------------------------------------------------- flat record literals
    // Behind `MARM_FLAT_RECORDS`: a record whose fields include nested GROUND
    // records is stored as ONE heap object with those sub-records' leaves inline
    // (the `record_layouts` table gives each field's flattened width). Fewer
    // allocations -- the confirmed bottleneck. Non-nested records are unchanged
    // (all fields width 1 => identical to the tuple lowering), so output stays
    // byte-identical; only allocation count drops.

    fn flat_records_enabled(&self) -> bool {
        // Default ON; opt out with MARM_NO_FLAT_RECORDS (measured 3x fewer allocs,
        // 1.44x wall on flat_boxes, byte-identical elsewhere).
        std::env::var_os("MARM_NO_FLAT_RECORDS").is_none()
    }

    // The per-field (or per-element) flattened widths of `ty`, if it is a flat
    // aggregate: a record (from the layout table) or a tuple (element widths).
    // A record is ALWAYS flat; a tuple is only flat when it is a field of a flat
    // record (its words inlined there) -- callers gate the tuple case on that.
    fn flat_widths(&self, ty: &Type) -> Option<Vec<usize>> {
        self.flat_widths_on_path(ty, &mut Vec::new())
    }

    /// Records wider than one word travel through compiler-generated locals and
    /// closure environments as their canonical flat words. Other values retain
    /// the ordinary one-`Value` representation.
    fn flat_record_width(&self, ty: &Type) -> usize {
        if self.flat_records_enabled()
            && ty.variables().is_empty()
            && matches!(ty, Type::Constructor(_) | Type::Apply { .. })
            && let Some(widths) = self.flat_widths(ty)
        {
            let width = widths.iter().sum();
            if (2..=FLAT_INLINE_CAP).contains(&width) {
                return width;
            }
        }
        1
    }

    fn capture_places(&self, lifted_name: &QualifiedName) -> Vec<CapturePlace> {
        let Some(function) = self
            .functions
            .iter()
            .find(|function| &function.name == lifted_name)
        else {
            return Vec::new();
        };
        let mut offset = 0;
        function
            .capture_info
            .captured_types()
            .iter()
            .map(|info| {
                let width = self.flat_record_width(&info.inferred_type);
                let place = CapturePlace {
                    offset,
                    width,
                    ty: info.inferred_type.clone(),
                };
                offset += width;
                place
            })
            .collect()
    }

    fn current_capture_place(index: usize) -> Option<CapturePlace> {
        CAPTURE_PLACES.with(|places| places.borrow().get(index).cloned())
    }

    fn flat_words_for(&self, expression: &Expr) -> Option<Vec<String>> {
        match strip_ascription(expression) {
            Expr::Variable(_, Identifier::Local(LexicalLevel(level))) => FLAT_VALUE_PLACES
                .with(|places| places.borrow().get(level).map(|place| place.words.clone())),
            Expr::Variable(_, Identifier::Captured(capture)) => {
                let place = Self::current_capture_place(capture.index())?;
                (place.width > 1).then(|| {
                    (0..place.width)
                        .map(|word| format!("env_get(self, {})", place.offset + word))
                        .collect()
                })
            }
            _ => None,
        }
    }

    fn tuple_from_words(words: &[String]) -> String {
        if words.len() <= 4 {
            format!("mk_tuple{}({})", words.len(), words.join(", "))
        } else {
            format!("mk_tuple({}, {})", words.len(), words.join(", "))
        }
    }

    fn flat_widths_on_path(&self, ty: &Type, on_path: &mut Vec<Type>) -> Option<Vec<usize>> {
        if on_path.contains(ty) {
            return None;
        }
        match ty {
            Type::Constructor(name) => {
                let TypeDefinition::Record(record) = self.type_definitions.get(name)? else {
                    return None;
                };
                on_path.push(ty.clone());
                let mut fields = record.fields.iter().collect::<Vec<_>>();
                fields.sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name));
                let widths = fields
                    .into_iter()
                    .map(|field| {
                        let field_type = instantiate_type_expression(
                            &field.type_signature.body,
                            &HashMap::new(),
                        )?;
                        Some(self.flat_width_on_path(&field_type, on_path))
                    })
                    .collect::<Option<Vec<_>>>();
                on_path.pop();
                widths
            }
            Type::Apply { .. } => {
                let (name, arguments) = applied_type(ty)?;
                let TypeDefinition::Record(record) = self.type_definitions.get(&name)? else {
                    return None;
                };
                let bindings = record
                    .type_parameters
                    .iter()
                    .zip(arguments)
                    .map(|(parameter, argument)| (parameter.name.clone(), argument))
                    .collect::<HashMap<_, _>>();
                on_path.push(ty.clone());
                let mut fields = record.fields.iter().collect::<Vec<_>>();
                fields.sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name));
                let widths = fields
                    .into_iter()
                    .map(|field| {
                        let field_type =
                            instantiate_type_expression(&field.type_signature.body, &bindings)?;
                        Some(self.flat_width_on_path(&field_type, on_path))
                    })
                    .collect::<Option<Vec<_>>>();
                on_path.pop();
                widths
            }
            Type::Tuple(tuple) => Some(
                tuple
                    .0
                    .iter()
                    .map(|field| self.flat_width_on_path(field, on_path))
                    .collect(),
            ),
            _ => None,
        }
    }

    fn flat_width_on_path(&self, ty: &Type, on_path: &mut Vec<Type>) -> usize {
        // A ground unary sum may use a one-word zero niche directly inside a
        // canonical flat record. Parametric sums retain their fixed tagged
        // representation: `Perhaps (Perhaps a)` must still distinguish
        // `This Nope` from `Nope` until the payload type is known.
        if ty.variables().is_empty()
            && let Some((_niche_tag, _payload_tag)) = self.one_word_niche(ty)
        {
            return 1;
        }
        match self.flat_widths_on_path(ty, on_path) {
            Some(widths) => {
                let total: usize = widths.iter().sum();
                if (1..=FLAT_INLINE_CAP).contains(&total) {
                    total
                } else {
                    1
                }
            }
            None => self.sum_layout(ty).map_or(1, |layout| {
                if (1..=FLAT_INLINE_CAP).contains(&layout.union_width) {
                    layout.union_width
                } else {
                    1
                }
            }),
        }
    }

    // The inline layout of a coproduct type (peeling `Perhaps τ` to `Perhaps`),
    // if it is an inlined (non-recursive, under-cap) sum. `None` for records,
    // recursive/boxed sums, and everything else.
    fn sum_layout(&self, ty: &Type) -> Option<&CoproductLayout> {
        let mut head = ty;
        while let Type::Apply { constructor, .. } = head {
            head = constructor;
        }
        match head {
            Type::Constructor(name) => self.coproduct_layouts.get(name),
            _ => None,
        }
    }

    fn one_word_niche(&self, ty: &Type) -> Option<(usize, usize)> {
        let RuntimeShape::NicheSum {
            niche_tag,
            payload_tag,
            payload_fields,
            ..
        } = self.runtime_shape(ty, &mut Vec::new()).shape
        else {
            return None;
        };
        (payload_fields
            .iter()
            .map(RuntimeShape::stored_words)
            .sum::<usize>()
            == 1)
            .then_some((niche_tag, payload_tag))
    }

    // Compile a sub-expression to a standalone C string (for splicing into an
    // argument list where a `CodeBuffer` write cannot reach).
    fn compile_to_string(&self, expr: &Expr) -> String {
        let mut buf = CodeBuffer::default();
        let _ = self.compile_expr(expr, &mut buf);
        buf.to_string()
    }

    fn encode_one_word_niche(&self, value: &str, ty: &Type) -> Option<String> {
        let (niche_tag, payload_tag) = self.one_word_niche(ty)?;
        Some(format!(
            "(data_tag({value}) == {niche_tag} ? ((Value){{0}}) : \
             (data_tag({value}) == {payload_tag} ? data_field({value}, 0) : match_fail()))"
        ))
    }

    fn decode_one_word_niche(&self, raw: &str, ty: &Type) -> Option<String> {
        let (niche_tag, payload_tag) = self.one_word_niche(ty)?;
        let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
        Some(format!(
            "({{ Value _nr{id} = {raw}; _nr{id}.w == 0 \
             ? mk_data_inline(VInt({niche_tag}), 0, NULL) \
             : mk_data_inline(VInt({payload_tag}), 1, &_nr{id}); }})"
        ))
    }

    // Fuse a constructor `C args` of an inlined sum `ty` into its inline leaves
    // `[tag, active variant's leaves, zero padding]` to `width` words -- the
    // sub-`Data` box is never built. Shared by the `Inject`-literal and the
    // saturated-application forms. `None` (caller falls back to the splat) when
    // `ty` is not an inlined sum, `C` is a newtype/foreign (not a real tag), or
    // the application is not saturated (a partial application keeps its closure).
    fn fuse_inlined_sum(
        &self,
        ty: &Type,
        constructor: &QualifiedName,
        arguments: &[&Expr],
        width: usize,
        prelude: &mut Vec<String>,
    ) -> Option<Vec<String>> {
        let layout = self.sum_layout(ty)?;
        if self.newtype_constructors.contains(constructor)
            || !self.constructor_tags.contains_key(constructor)
        {
            return None;
        }
        let tag = self.constructor_tag(constructor);
        let variant = layout.variant_widths.get(tag as usize)?;
        if arguments.len() != variant.len() {
            return None; // under-/over-saturated: not a plain construction
        }
        let mut leaves = vec![format!("VInt({tag})")];
        for (argument, w) in arguments.iter().zip(variant) {
            leaves.extend(self.flat_leaves(argument, *w, prelude));
        }
        while leaves.len() < width {
            leaves.push("((Value){0})".to_string());
        }
        Some(leaves)
    }

    // The flat leaf C-expressions of a field `value` occupying `width` inline
    // words. A width-1 field is its own single value. A wider field is a nested
    // record: a record *literal* fuses (its leaves splice in directly, so the
    // sub-object is never built), anything else is splatted from a hoisted temp
    // (its `width` words copied out -- the value-semantics copy of a small
    // existing record). Temp bindings accumulate in `prelude`.
    fn flat_leaves(&self, value: &Expr, width: usize, prelude: &mut Vec<String>) -> Vec<String> {
        if let Some(words) = self.flat_words_for(value)
            && words.len() == width
        {
            return words;
        }
        if width == 1 {
            let ty = &value.annotation().type_info.inferred_type;
            if ty.variables().is_empty()
                && let Some((niche_tag, payload_tag)) = self.one_word_niche(ty)
            {
                let shape = self.runtime_shape(ty, &mut Vec::new()).shape;
                if let Some(leaves) = self.literal_shape_leaves(value, &shape, prelude) {
                    return leaves;
                }
                let temp = format!("_fn{}", MATCH_ID.fetch_add(1, Ordering::Relaxed));
                prelude.push(format!("Value {temp} = {};", self.compile_to_string(value)));
                return vec![format!(
                    "(data_tag({temp}) == {niche_tag} ? ((Value){{0}}) : \
                     (data_tag({temp}) == {payload_tag} ? data_field({temp}, 0) : match_fail()))"
                )];
            }
            return vec![self.compile_to_string(value)];
        }
        // A literal inlined aggregate fuses: splice its own leaves in directly, so
        // the sub-object is never built. A record fuses through its layout; a tuple
        // (only reached here as a flat record's field) through its element widths.
        match strip_ascription(value) {
            Expr::Record(annotation, sub) => {
                if let Some(sub_widths) = self.flat_widths(&annotation.type_info.inferred_type) {
                    let mut leaves = Vec::new();
                    for ((_label, field), w) in sub.fields.iter().zip(sub_widths) {
                        leaves.extend(self.flat_leaves(field, w, prelude));
                    }
                    return leaves;
                }
            }
            Expr::Tuple(annotation, tuple) => {
                if let Some(element_widths) = self.flat_widths(&annotation.type_info.inferred_type)
                {
                    let mut leaves = Vec::new();
                    for (element, w) in tuple.elements.iter().zip(element_widths) {
                        leaves.extend(self.flat_leaves(element, w, prelude));
                    }
                    return leaves;
                }
            }
            // An inlined sum literal: `[tag, active variant's leaves, zero padding]`
            // to the union width. Padding zeros keep the blind tracer correct.
            Expr::Inject(annotation, inject) => {
                let arguments: Vec<&Expr> = inject.arguments.iter().map(|a| &**a).collect();
                if let Some(leaves) = self.fuse_inlined_sum(
                    &annotation.type_info.inferred_type,
                    &inject.constructor,
                    &arguments,
                    width,
                    prelude,
                ) {
                    return leaves;
                }
            }
            // A saturated constructor application `C a1..an` reaches codegen as an
            // Apply spine, NOT an `Inject` (only a syntactic literal stays an
            // `Inject`), so fuse it too. Without this, `field := C arg` builds the
            // box via the worker call and then splats it -- a strict loss vs. keeping
            // the field boxed. Peel the spine; fuse only when the head is a known
            // constructor of this inlined sum and the application is saturated.
            application @ Expr::Apply(..) => {
                let mut arguments: Vec<&Expr> = Vec::new();
                let mut head: &Expr = application;
                while let Expr::Apply(_, inner) = head {
                    arguments.push(&inner.argument);
                    head = &inner.function;
                }
                arguments.reverse();
                if let Expr::Variable(_, Identifier::Global(constructor)) = head {
                    if let Some(leaves) = self.fuse_inlined_sum(
                        &application.annotation().type_info.inferred_type,
                        constructor,
                        &arguments,
                        width,
                        prelude,
                    ) {
                        return leaves;
                    }
                }
            }
            Expr::Variable(annotation, Identifier::Global(constructor)) => {
                if let Some(leaves) = self.fuse_inlined_sum(
                    &annotation.type_info.inferred_type,
                    constructor,
                    &[],
                    width,
                    prelude,
                ) {
                    return leaves;
                }
            }
            _ => {}
        }
        // Non-literal: hoist to a temp and splat its `width` words.
        let temp = format!("_fr{}", MATCH_ID.fetch_add(1, Ordering::Relaxed));
        prelude.push(format!("Value {temp} = {};", self.compile_to_string(value)));
        if self
            .sum_layout(&value.annotation().type_info.inferred_type)
            .is_some()
        {
            // A boxed sum -> the inline union: tag from the header, then the active
            // variant's fields (its count is `data_len`), zero-padding the rest.
            let mut leaves = vec![format!("VInt(data_tag({temp}))")];
            for k in 0..width - 1 {
                leaves.push(format!(
                    "(({k}) < data_len({temp}) ? data_field({temp}, {k}) : ((Value){{0}}))"
                ));
            }
            leaves
        } else {
            (0..width).map(|k| format!("proj({temp}, {k})")).collect()
        }
    }

    fn constructor_shape_leaves(
        &self,
        constructor: &QualifiedName,
        arguments: &[&Expr],
        payload_words: usize,
        variants: &[Vec<RuntimeShape>],
        prelude: &mut Vec<String>,
    ) -> Option<Vec<String>> {
        if self.newtype_constructors.contains(constructor)
            || !self.constructor_tags.contains_key(constructor)
        {
            return None;
        }
        let tag = self.constructor_tag(constructor);
        let variant = variants.get(tag as usize)?;
        if arguments.len() != variant.len() {
            return None;
        }
        let mut leaves = vec![format!("VInt({tag})")];
        for (argument, shape) in arguments.iter().zip(variant) {
            leaves.extend(self.literal_shape_leaves(argument, shape, prelude)?);
        }
        while leaves.len() < 1 + payload_words {
            leaves.push("((Value){0})".to_string());
        }
        (leaves.len() == 1 + payload_words).then_some(leaves)
    }

    fn niche_constructor_shape_leaves(
        &self,
        constructor: &QualifiedName,
        arguments: &[&Expr],
        niche_tag: usize,
        payload_tag: usize,
        payload_fields: &[RuntimeShape],
        prelude: &mut Vec<String>,
    ) -> Option<Vec<String>> {
        // Not every `Global` in constructor position is a constructor -- a plain
        // top-level CAF that merely evaluates to one (`Perhaps.empty`) reaches here
        // too, and has no tag. Decline rather than panic, exactly as
        // `constructor_shape_leaves` does; the caller falls back to splatting the
        // value through a temp.
        let Some(&tag) = self.constructor_tags.get(constructor) else {
            return None;
        };
        let tag = tag as usize;
        if tag == niche_tag && arguments.is_empty() {
            let words = payload_fields.iter().map(RuntimeShape::stored_words).sum();
            return Some(vec!["((Value){0})".to_string(); words]);
        }
        if tag == payload_tag && arguments.len() == payload_fields.len() {
            let mut leaves = Vec::new();
            for (argument, shape) in arguments.iter().zip(payload_fields) {
                leaves.extend(self.literal_shape_leaves(argument, shape, prelude)?);
            }
            return Some(leaves);
        }
        None
    }

    fn canonical_product_leaves(path: &str, shape: &RuntimeShape, out: &mut Vec<String>) {
        match shape {
            RuntimeShape::Leaf => out.push(path.to_string()),
            RuntimeShape::Product(fields) => {
                for (index, field) in fields.iter().enumerate() {
                    Self::canonical_product_leaves(&format!("proj({path}, {index})"), field, out);
                }
            }
            // A dynamically-tagged canonical sum needs variant-dependent traversal.
            // Known constructor applications are handled by
            // `constructor_shape_leaves`; other sums keep the runtime fallback.
            RuntimeShape::Sum { .. } | RuntimeShape::NicheSum { .. } => {}
        }
    }

    fn literal_shape_leaves(
        &self,
        value: &Expr,
        shape: &RuntimeShape,
        prelude: &mut Vec<String>,
    ) -> Option<Vec<String>> {
        if matches!(shape, RuntimeShape::Product(_))
            && let Some(words) = self.flat_words_for(value)
            && words.len() == shape.stored_words()
        {
            return Some(words);
        }
        match (strip_ascription(value), shape) {
            (_, RuntimeShape::Leaf) => Some(vec![self.compile_to_string(value)]),
            (Expr::Record(_, record), RuntimeShape::Product(fields))
                if record.fields.len() == fields.len() =>
            {
                let mut leaves = Vec::new();
                for ((_, field), shape) in record.fields.iter().zip(fields) {
                    leaves.extend(self.literal_shape_leaves(field, shape, prelude)?);
                }
                Some(leaves)
            }
            (Expr::Record(annotation, record), RuntimeShape::Product(_)) => {
                let widths = self.flat_widths(&annotation.type_info.inferred_type)?;
                (widths.iter().sum::<usize>() == shape.stored_words()).then_some(())?;
                let mut leaves = Vec::new();
                for ((_, field), width) in record.fields.iter().zip(widths) {
                    leaves.extend(self.flat_leaves(field, width, prelude));
                }
                (leaves.len() == shape.stored_words()).then_some(leaves)
            }
            (Expr::Tuple(_, tuple), RuntimeShape::Product(fields))
                if tuple.elements.len() == fields.len() =>
            {
                let mut leaves = Vec::new();
                for (element, shape) in tuple.elements.iter().zip(fields) {
                    leaves.extend(self.literal_shape_leaves(element, shape, prelude)?);
                }
                Some(leaves)
            }
            (
                Expr::Inject(_, inject),
                RuntimeShape::NicheSum {
                    niche_tag,
                    payload_tag,
                    payload_fields,
                    ..
                },
            ) => {
                let arguments = inject.arguments.iter().map(|a| &**a).collect::<Vec<_>>();
                self.niche_constructor_shape_leaves(
                    &inject.constructor,
                    &arguments,
                    *niche_tag,
                    *payload_tag,
                    payload_fields,
                    prelude,
                )
            }
            (
                Expr::Inject(_, inject),
                RuntimeShape::Sum {
                    payload_words,
                    variants,
                },
            ) => {
                let arguments = inject.arguments.iter().map(|a| &**a).collect::<Vec<_>>();
                self.constructor_shape_leaves(
                    &inject.constructor,
                    &arguments,
                    *payload_words,
                    variants,
                    prelude,
                )
            }
            (
                application @ Expr::Apply(..),
                RuntimeShape::NicheSum {
                    niche_tag,
                    payload_tag,
                    payload_fields,
                    ..
                },
            ) => {
                let mut arguments = Vec::new();
                let mut head = application;
                while let Expr::Apply(_, inner) = head {
                    arguments.push(&*inner.argument);
                    head = &inner.function;
                }
                arguments.reverse();
                let Expr::Variable(_, Identifier::Global(constructor)) = head else {
                    return None;
                };
                self.niche_constructor_shape_leaves(
                    constructor,
                    &arguments,
                    *niche_tag,
                    *payload_tag,
                    payload_fields,
                    prelude,
                )
            }
            (
                application @ Expr::Apply(..),
                RuntimeShape::Sum {
                    payload_words,
                    variants,
                },
            ) => {
                let mut arguments = Vec::new();
                let mut head = application;
                while let Expr::Apply(_, inner) = head {
                    arguments.push(&*inner.argument);
                    head = &inner.function;
                }
                arguments.reverse();
                let Expr::Variable(_, Identifier::Global(constructor)) = head else {
                    return None;
                };
                self.constructor_shape_leaves(
                    constructor,
                    &arguments,
                    *payload_words,
                    variants,
                    prelude,
                )
            }
            (
                Expr::Variable(_, Identifier::Global(constructor)),
                RuntimeShape::NicheSum {
                    niche_tag,
                    payload_tag,
                    payload_fields,
                    ..
                },
            ) => self.niche_constructor_shape_leaves(
                constructor,
                &[],
                *niche_tag,
                *payload_tag,
                payload_fields,
                prelude,
            ),
            (
                Expr::Variable(_, Identifier::Global(constructor)),
                RuntimeShape::Sum {
                    payload_words,
                    variants,
                },
            ) => self.constructor_shape_leaves(constructor, &[], *payload_words, variants, prelude),
            (_, RuntimeShape::Product(_)) => {
                // A non-literal product is still statically splattable. Evaluate it
                // once, after the array and index, then recursively project its
                // canonical fields according to the complete runtime shape.
                let temp = format!("_fw{}", MATCH_ID.fetch_add(1, Ordering::Relaxed));
                prelude.push(format!("Value {temp} = {};", self.compile_to_string(value)));
                let mut leaves = Vec::new();
                Self::canonical_product_leaves(&temp, shape, &mut leaves);
                (leaves.len() == shape.stored_words()).then_some(leaves)
            }
            _ => None,
        }
    }

    /// Resolve a projection rooted in a split local or flattened capture to its
    /// physical words. This is the local/closure counterpart of
    /// `flat_array_region`.
    fn flat_value_region(
        &self,
        projection: &phase::Projection<Closed>,
    ) -> Option<(Vec<String>, usize, Type, RuntimeShape)> {
        let (root, selectors) = projection_root_and_selectors(projection);
        let words = self.flat_words_for(root)?;
        let mut current_type = root.annotation().type_info.inferred_type.clone();
        let mut offset = 0;
        for selector in &selectors {
            let (next_type, field_offset) =
                self.runtime_projection_field(&current_type, selector)?;
            offset += field_offset;
            current_type = next_type;
        }
        let shape = self.runtime_shape(&current_type, &mut Vec::new()).shape;
        (offset + shape.stored_words() <= words.len()).then_some((
            words,
            offset,
            current_type,
            shape,
        ))
    }

    // Resolve a projection into a flat record to `(base, offset, width)`: the C
    // expression for the enclosing flat object, the projected field's word
    // offset, and its flattened width. Nested projections into flat records
    // accumulate their offsets, so `arr.b.y` reaches one word with no
    // intermediate object materialised. `None` if the base is not a flat record.
    fn flat_place(&self, projection: &phase::Projection<Closed>) -> Option<(String, usize, usize)> {
        let ProductElement::Ordinal(index) = projection.select else {
            return None;
        };
        let base_type = &projection.base.annotation().type_info.inferred_type;
        let widths = self.flat_widths(base_type)?;
        let offset: usize = widths[..index].iter().sum();
        let width = widths[index];
        // Reach through a base that is itself a flat projection (accumulating
        // offsets), so `r.b.c` -- even through an inlined tuple field -- is one load.
        if let Expr::Project(_, inner) = strip_ascription(&projection.base) {
            if let Some((base, base_offset, _)) = self.flat_place(inner) {
                return Some((base, base_offset + offset, width));
            }
        }
        // The base is not a flat projection. A record value is always a flat object,
        // so offset into it; a standalone TUPLE is boxed (only a tuple *inlined in a
        // record* is flat, and that is the reach-through case above) -- leave it.
        // `flat_widths` above already proved this is a nominal record. Generic
        // records appear as `Type::Apply` (`Entry α β`), while monomorphic records
        // appear as `Type::Constructor`. Both use the same flattened object
        // representation and must therefore use the same offset/copy-out path.
        match base_type {
            Type::Constructor(_) | Type::Apply { .. } => {
                Some((self.compile_to_string(&projection.base), offset, width))
            }
            _ => None,
        }
    }

    fn flat_array_region(
        &self,
        expression: &Expr,
    ) -> Option<(String, String, usize, Type, RuntimeShape)> {
        let (root, selectors) = match strip_ascription(expression) {
            Expr::Project(_, projection) => projection_root_and_selectors(projection),
            root => (root, Vec::new()),
        };
        let (array, index, root_type) = if let Some((array, index, source_type)) =
            self.raw_array_get_source(root)
        {
            let annotated = &root.annotation().type_info.inferred_type;
            (
                self.compile_to_string(array),
                self.compile_to_string(index),
                if source_type.variables().is_empty() {
                    source_type.clone()
                } else if annotated.variables().is_empty() {
                    annotated.clone()
                } else {
                    source_type.clone()
                },
            )
        } else if let Expr::Variable(_, Identifier::Local(LexicalLevel(level))) = root {
            let place = ARRAY_ELEMENT_PLACES.with(|places| places.borrow().get(level).cloned())?;
            let annotated_type = &root.annotation().type_info.inferred_type;
            let element_type = if annotated_type.variables().is_empty() {
                annotated_type.clone()
            } else {
                place.element_type
            };
            (place.array, place.index, element_type)
        } else {
            return None;
        };

        let mut current_type = root_type;
        let mut word_offset = 0;
        for selector in &selectors {
            let (next_type, offset) = self.runtime_projection_field(&current_type, selector)?;
            word_offset += offset;
            current_type = next_type;
        }
        let shape = self.runtime_shape(&current_type, &mut Vec::new()).shape;
        Some((array, index, word_offset, current_type, shape))
    }

    /// See through the erased `Mutable` newtype unwrap that commonly surrounds
    /// the foreign raw get after simplification.
    fn raw_array_get_source<'a>(
        &self,
        expression: &'a Expr,
    ) -> Option<(&'a Expr, &'a Expr, &'a Type)> {
        fn resolve_alias<'a>(mut expression: &'a Expr, aliases: &[(usize, &'a Expr)]) -> &'a Expr {
            loop {
                let Expr::Variable(_, Identifier::Local(LexicalLevel(level))) =
                    strip_ascription(expression)
                else {
                    return expression;
                };
                let Some((_, replacement)) = aliases.iter().rev().find(|(alias, _)| alias == level)
                else {
                    return expression;
                };
                expression = replacement;
            }
        }

        fn go<'a>(
            program: &lambda_lift::Program,
            expression: &'a Expr,
            aliases: &mut Vec<(usize, &'a Expr)>,
        ) -> Option<(&'a Expr, &'a Expr, &'a Type)> {
            let expression = strip_ascription(expression);
            if let Some((array, index)) = raw_array_get_arguments(expression) {
                return Some((
                    resolve_alias(array, aliases),
                    resolve_alias(index, aliases),
                    &expression.annotation().type_info.inferred_type,
                ));
            }

            // IO deforestation often leaves trivial aliases in front of the
            // newtype unwrap (`let i' = i in ...`). They do not carry effects or
            // alter evaluation order, so retain their source operand when
            // recovering the logical array place.
            if let Expr::Let(_, binding) = expression
                && let Identifier::Local(LexicalLevel(alias)) = binding.binder
                && matches!(strip_ascription(&binding.bound), Expr::Variable(..))
            {
                aliases.push((alias, &binding.bound));
                let found = go(program, &binding.body, aliases);
                aliases.pop();
                return found;
            }

            let Expr::Deconstruct(_, deconstruct) = expression else {
                return None;
            };
            let [clause] = deconstruct.match_clauses.as_slice() else {
                return None;
            };
            let bound_level = match &clause.pattern {
                // Newtype erasure may already have reduced `Mutable array` to an
                // irrefutable local bind before this late code-generation pass.
                Pattern::Bind(_, Identifier::Local(level)) => level,
                Pattern::Coproduct(_, constructor) => {
                    let Identifier::Global(name) = &constructor.constructor else {
                        return None;
                    };
                    if !program.newtype_constructors.contains(name.as_ref()) {
                        return None;
                    }
                    let [Pattern::Bind(_, Identifier::Local(level))] =
                        constructor.arguments.as_slice()
                    else {
                        return None;
                    };
                    level
                }
                _ => return None,
            };
            let (array, index) = raw_array_get_arguments(&clause.consequent)?;
            if !matches!(strip_ascription(array), Expr::Variable(_, Identifier::Local(level)) if level == bound_level)
            {
                return None;
            }
            let element_type = mutable_array_element_type(
                &deconstruct.scrutinee.annotation().type_info.inferred_type,
            )?;
            Some((
                &deconstruct.scrutinee,
                resolve_alias(index, aliases),
                element_type,
            ))
        }

        go(self, expression, &mut Vec::new())
    }

    /// Recover the logical `(Mutable_Array, index, replacement)` around the
    /// erased `Mutable` newtype and the trivial aliases introduced by IO
    /// deforestation. This is the write-side counterpart of
    /// `raw_array_get_source`.
    fn raw_array_set_source<'a>(
        &self,
        expression: &'a Expr,
    ) -> Option<(&'a Expr, &'a Expr, &'a Expr)> {
        fn resolve_alias<'a>(mut expression: &'a Expr, aliases: &[(usize, &'a Expr)]) -> &'a Expr {
            loop {
                let Expr::Variable(_, Identifier::Local(LexicalLevel(level))) =
                    strip_ascription(expression)
                else {
                    return expression;
                };
                let Some((_, replacement)) = aliases.iter().rev().find(|(alias, _)| alias == level)
                else {
                    return expression;
                };
                expression = replacement;
            }
        }

        fn go<'a>(
            program: &lambda_lift::Program,
            expression: &'a Expr,
            aliases: &mut Vec<(usize, &'a Expr)>,
        ) -> Option<(&'a Expr, &'a Expr, &'a Expr)> {
            let expression = strip_ascription(expression);
            if let Some((array, index, replacement)) = raw_array_set_arguments(expression) {
                return Some((
                    resolve_alias(array, aliases),
                    resolve_alias(index, aliases),
                    resolve_alias(replacement, aliases),
                ));
            }

            if let Expr::Let(_, binding) = expression
                && let Identifier::Local(LexicalLevel(alias)) = binding.binder
                && matches!(strip_ascription(&binding.bound), Expr::Variable(..))
            {
                aliases.push((alias, &binding.bound));
                let found = go(program, &binding.body, aliases);
                aliases.pop();
                return found;
            }

            let Expr::Deconstruct(_, deconstruct) = expression else {
                return None;
            };
            let [clause] = deconstruct.match_clauses.as_slice() else {
                return None;
            };
            let bound_level = match &clause.pattern {
                Pattern::Bind(_, Identifier::Local(level)) => level,
                Pattern::Coproduct(_, constructor) => {
                    let Identifier::Global(name) = &constructor.constructor else {
                        return None;
                    };
                    if !program.newtype_constructors.contains(name.as_ref()) {
                        return None;
                    }
                    let [Pattern::Bind(_, Identifier::Local(level))] =
                        constructor.arguments.as_slice()
                    else {
                        return None;
                    };
                    level
                }
                _ => return None,
            };
            let (array, index, replacement) = raw_array_set_arguments(&clause.consequent)?;
            if !matches!(strip_ascription(array), Expr::Variable(_, Identifier::Local(level)) if level == bound_level)
            {
                return None;
            }
            Some((
                &deconstruct.scrutinee,
                resolve_alias(index, aliases),
                resolve_alias(replacement, aliases),
            ))
        }

        go(self, expression, &mut Vec::new())
    }

    fn concrete_local_type(expression: &Expr, level: usize) -> Option<Type> {
        let expression = strip_ascription(expression);
        if let Expr::Variable(annotation, Identifier::Local(LexicalLevel(found))) = expression
            && *found == level
            && annotation.type_info.inferred_type.variables().is_empty()
        {
            return Some(annotation.type_info.inferred_type.clone());
        }
        if let Expr::RecordUpdate(annotation, update) = expression
            && matches!(
                strip_ascription(&update.base),
                Expr::Variable(_, Identifier::Local(LexicalLevel(found))) if *found == level
            )
            && annotation.type_info.inferred_type.variables().is_empty()
        {
            return Some(annotation.type_info.inferred_type.clone());
        }
        // Simplification commonly gives an update a short-lived alias for its
        // base. Follow that alias when looking for the ground instantiation of
        // an otherwise-polymorphic raw array read.
        if let Expr::Let(_, binding) = expression
            && matches!(strip_ascription(&binding.bound), Expr::Variable(_, Identifier::Local(LexicalLevel(found))) if *found == level)
            && let Identifier::Local(LexicalLevel(alias)) = binding.binder
            && let Some(concrete) = Self::concrete_local_type(&binding.body, alias)
        {
            return Some(concrete);
        }
        crate::simplify::children(expression)
            .into_iter()
            .find_map(|child| Self::concrete_local_type(child, level))
    }

    fn local_uses_are_flat_array_leaves(
        &self,
        expression: &Expr,
        level: usize,
        element_type: &Type,
    ) -> bool {
        // A branch-local `{ old: ... }` followed by a write to the registered
        // `(array,index)` consumes the old aggregate as a place, not as a value.
        // Inspect only the replacement expressions: their projections may read
        // scalar leaves from the place, while the base itself is deliberately
        // never materialised.
        if let Expr::Let(_, binding) = strip_ascription(expression)
            && let Some((_place, update, _update_level, source_level)) =
                self.registered_same_place_update(&binding.binder, &binding.bound, &binding.body)
            && source_level == level
        {
            return update.fields.iter().all(|field| {
                self.local_uses_are_flat_array_leaves(&field.value, level, element_type)
            });
        }

        // `simplify::children` intentionally treats lifted closure metadata as a
        // leaf, but its environment is a real use of captured locals. A packed
        // place cannot cross that closure boundary: the generated environment
        // needs the canonical value, not just this function's `(array, index)`.
        if let Expr::MakeClosure(_, closure) = expression {
            return self.local_uses_are_flat_array_leaves(
                &closure.environment,
                level,
                element_type,
            );
        }
        if let Expr::Project(_, projection) = expression {
            let (root, selectors) = projection_root_and_selectors(projection);
            if matches!(root, Expr::Variable(_, Identifier::Local(LexicalLevel(n))) if *n == level)
            {
                let annotated_type = &root.annotation().type_info.inferred_type;
                let mut current_type = if annotated_type.variables().is_empty() {
                    annotated_type.clone()
                } else {
                    element_type.clone()
                };
                for selector in selectors {
                    let Some((next, _)) = self.runtime_projection_field(&current_type, &selector)
                    else {
                        return false;
                    };
                    current_type = next;
                }
                return self
                    .runtime_shape(&current_type, &mut Vec::new())
                    .shape
                    .stored_words()
                    == 1;
            }
        }
        if let Expr::Deconstruct(_, deconstruct) = expression {
            if let Some((_array, _index, _offset, matched_type, shape)) =
                self.flat_array_region(&deconstruct.scrutinee)
            {
                // Keep this eligibility test exactly as conservative as
                // `compile_deconstruct`: otherwise the lazy let omits the
                // canonical local, only for the matcher to decline the direct
                // path and emit a reference to that missing local.
                // Plan the clauses exactly as `compile_deconstruct` will. Checking only
                // the shape was too permissive: a clause `collect_array_pattern` declines
                // left the matcher on the canonical path while this had already dropped
                // the canonical local.
                if matched_type.variables().is_empty()
                    && self
                        .array_match_shape(&deconstruct.match_clauses, &shape)
                        .filter(|planned| {
                            self.plan_array_match(
                                &deconstruct.match_clauses,
                                "_probe_a",
                                "_probe_i",
                                _offset,
                                planned,
                            )
                            .is_some()
                        })
                        .is_some()
                {
                    return deconstruct.match_clauses.iter().all(|clause| {
                        self.local_uses_are_flat_array_leaves(
                            &clause.consequent,
                            level,
                            element_type,
                        )
                    });
                }
            }
        }
        match expression {
            Expr::Variable(_, Identifier::Local(LexicalLevel(n))) if *n == level => false,
            _ => crate::simplify::children(expression)
                .into_iter()
                .all(|child| self.local_uses_are_flat_array_leaves(child, level, element_type)),
        }
    }

    /// Plan the in-place read for every clause, or `None` if ANY clause declines.
    ///
    /// This is the single source of truth for "can the matcher read this element
    /// directly": `compile_deconstruct` uses it to decide whether to take the direct
    /// path, and `local_uses_are_flat_array_leaves` uses it to decide whether the
    /// canonical `let` may be elided. They MUST agree -- if the checker is more
    /// permissive, the `let` is dropped and the matcher then emits a reference to the
    /// local that is no longer bound.
    fn plan_array_match(
        &self,
        clauses: &[phase::MatchClause<Closed>],
        array_local: &str,
        index_local: &str,
        offset: usize,
        shape: &RuntimeShape,
    ) -> Option<Vec<(Vec<String>, Vec<(usize, String)>)>> {
        let mut plans = Vec::with_capacity(clauses.len());
        for clause in clauses {
            let mut tests = Vec::new();
            let mut binds = Vec::new();
            if !self.collect_array_pattern(
                &clause.pattern,
                array_local,
                index_local,
                offset,
                shape,
                &mut tests,
                &mut binds,
            ) {
                return None;
            }
            plans.push((tests, binds));
        }
        Some(plans)
    }

    fn array_match_shape(
        &self,
        clauses: &[phase::MatchClause<Closed>],
        fallback: &RuntimeShape,
    ) -> Option<RuntimeShape> {
        if clauses
            .iter()
            .all(|clause| self.array_pattern_supported(&clause.pattern, fallback))
        {
            return Some(fallback.clone());
        }

        // A polymorphic array wrapper can retain `$a` on the raw read even when
        // its consumer is concrete.  Recover that concrete layout from the
        // consumer pattern.  Fully destructured tuples/records are also
        // self-describing, which covers late inlining whose annotations have not
        // yet had the call-site substitution applied.
        let mut shape = None;
        for clause in clauses {
            let candidate = self.pattern_runtime_shape(&clause.pattern)?;
            if !self.array_pattern_supported(&clause.pattern, &candidate)
                || shape
                    .as_ref()
                    .is_some_and(|previous| previous != &candidate)
            {
                return None;
            }
            shape = Some(candidate);
        }
        shape
    }

    fn pattern_runtime_shape(&self, pattern: &phase::Pattern<Closed>) -> Option<RuntimeShape> {
        let inferred = match pattern {
            Pattern::Bind(annotation, _)
            | Pattern::Literally(annotation, _)
            | Pattern::Struct(annotation, _)
            | Pattern::Tuple(annotation, _)
            | Pattern::Coproduct(annotation, _) => &annotation.type_info.inferred_type,
        };
        if inferred.variables().is_empty() {
            return Some(self.runtime_shape(inferred, &mut Vec::new()).shape);
        }
        match pattern {
            Pattern::Bind(..) | Pattern::Literally(..) => Some(RuntimeShape::Leaf),
            Pattern::Struct(_, record) => Some(RuntimeShape::Product(
                record
                    .fields
                    .iter()
                    .map(|(_, field)| self.pattern_runtime_shape(field))
                    .collect::<Option<Vec<_>>>()?,
            )),
            Pattern::Tuple(_, tuple) => Some(RuntimeShape::Product(
                tuple
                    .elements
                    .iter()
                    .map(|element| self.pattern_runtime_shape(element))
                    .collect::<Option<Vec<_>>>()?,
            )),
            // One constructor pattern does not describe the payload capacity of
            // every variant, so a polymorphic sum cannot be reconstructed safely.
            Pattern::Coproduct(..) => None,
        }
    }

    fn array_pattern_supported(
        &self,
        pattern: &phase::Pattern<Closed>,
        shape: &RuntimeShape,
    ) -> bool {
        match (pattern, shape) {
            (Pattern::Bind(_, Identifier::Local(..)), RuntimeShape::Leaf)
            | (Pattern::Literally(..), RuntimeShape::Leaf) => true,
            (Pattern::Struct(_, record), RuntimeShape::Product(fields)) => {
                record.fields.len() == fields.len()
                    && record
                        .fields
                        .iter()
                        .zip(fields)
                        .all(|((_, pattern), shape)| self.array_pattern_supported(pattern, shape))
            }
            (Pattern::Tuple(_, tuple), RuntimeShape::Product(fields)) => {
                tuple.elements.len() == fields.len()
                    && tuple
                        .elements
                        .iter()
                        .zip(fields)
                        .all(|(pattern, shape)| self.array_pattern_supported(pattern, shape))
            }
            (Pattern::Coproduct(_, constructor), _) => {
                let Identifier::Global(name) = &constructor.constructor else {
                    return false;
                };
                if self.newtype_constructors.contains(name.as_ref()) {
                    return matches!(constructor.arguments.as_slice(), [argument]
                        if self.array_pattern_supported(argument, shape));
                }
                let Some(tag) = self.constructor_tags.get(name.as_ref()) else {
                    return false;
                };
                match shape {
                    RuntimeShape::Sum { variants, .. } => {
                        let Some(fields) = variants.get(*tag as usize) else {
                            return false;
                        };
                        constructor.arguments.len() == fields.len()
                            && constructor
                                .arguments
                                .iter()
                                .zip(fields)
                                .all(|(pattern, shape)| {
                                    self.array_pattern_supported(pattern, shape)
                                })
                    }
                    RuntimeShape::NicheSum {
                        niche_tag,
                        payload_tag,
                        payload_fields,
                        ..
                    } => {
                        (*tag as usize == *niche_tag && constructor.arguments.is_empty())
                            || (*tag as usize == *payload_tag
                                && constructor.arguments.len() == payload_fields.len()
                                && constructor.arguments.iter().zip(payload_fields).all(
                                    |(argument, field)| {
                                        self.array_pattern_supported(argument, field)
                                    },
                                ))
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn collect_array_pattern(
        &self,
        pattern: &phase::Pattern<Closed>,
        array: &str,
        index: &str,
        offset: usize,
        shape: &RuntimeShape,
        tests: &mut Vec<String>,
        binds: &mut Vec<(usize, String)>,
    ) -> bool {
        let word =
            |at: usize| format!("flat_array_get_word({array}, (size_t)as_int({index}), {at})");
        match (pattern, shape) {
            (Pattern::Bind(_, Identifier::Local(LexicalLevel(level))), RuntimeShape::Leaf) => {
                binds.push((*level, word(offset)));
                true
            }
            (Pattern::Literally(_, literal), RuntimeShape::Leaf) => {
                tests.push(format!(
                    "val_eq({}, {})",
                    word(offset),
                    self.compile_constant(literal)
                ));
                true
            }
            (Pattern::Struct(_, record), RuntimeShape::Product(fields))
                if record.fields.len() == fields.len() =>
            {
                let mut field_offset = offset;
                for ((_, pattern), shape) in record.fields.iter().zip(fields) {
                    if !self.collect_array_pattern(
                        pattern,
                        array,
                        index,
                        field_offset,
                        shape,
                        tests,
                        binds,
                    ) {
                        return false;
                    }
                    field_offset += shape.stored_words();
                }
                true
            }
            (Pattern::Tuple(_, tuple), RuntimeShape::Product(fields))
                if tuple.elements.len() == fields.len() =>
            {
                let mut field_offset = offset;
                for (pattern, shape) in tuple.elements.iter().zip(fields) {
                    if !self.collect_array_pattern(
                        pattern,
                        array,
                        index,
                        field_offset,
                        shape,
                        tests,
                        binds,
                    ) {
                        return false;
                    }
                    field_offset += shape.stored_words();
                }
                true
            }
            (Pattern::Coproduct(_, constructor), _) => {
                let Identifier::Global(name) = &constructor.constructor else {
                    return false;
                };
                if self.newtype_constructors.contains(name.as_ref()) {
                    let [argument] = constructor.arguments.as_slice() else {
                        return false;
                    };
                    return self.collect_array_pattern(
                        argument, array, index, offset, shape, tests, binds,
                    );
                }
                let Some(&tag) = self.constructor_tags.get(name.as_ref()) else {
                    return false;
                };
                if let RuntimeShape::NicheSum {
                    niche_tag,
                    payload_tag,
                    niche_offset,
                    payload_fields,
                } = shape
                {
                    if tag as usize == *niche_tag && constructor.arguments.is_empty() {
                        tests.push(format!("{}.w == 0", word(offset + niche_offset)));
                        return true;
                    }
                    if tag as usize == *payload_tag {
                        if constructor.arguments.len() != payload_fields.len() {
                            return false;
                        }
                        tests.push(format!("{}.w != 0", word(offset + niche_offset)));
                        let mut field_offset = offset;
                        for (argument, field) in constructor.arguments.iter().zip(payload_fields) {
                            if !self.collect_array_pattern(
                                argument,
                                array,
                                index,
                                field_offset,
                                field,
                                tests,
                                binds,
                            ) {
                                return false;
                            }
                            field_offset += field.stored_words();
                        }
                        return true;
                    }
                    return false;
                }
                let RuntimeShape::Sum { variants, .. } = shape else {
                    return false;
                };
                let Some(fields) = variants.get(tag as usize) else {
                    return false;
                };
                if constructor.arguments.len() != fields.len() {
                    return false;
                }
                tests.push(format!("as_int({}) == {tag}", word(offset)));
                let mut field_offset = offset + 1;
                for (pattern, shape) in constructor.arguments.iter().zip(fields) {
                    if !self.collect_array_pattern(
                        pattern,
                        array,
                        index,
                        field_offset,
                        shape,
                        tests,
                        binds,
                    ) {
                        return false;
                    }
                    field_offset += shape.stored_words();
                }
                true
            }
            _ => false,
        }
    }

    /// Resolve one record/tuple selector according to the ARRAY element shape,
    /// which may be wider than the record-in-record `FLAT_INLINE_CAP` layout.
    fn runtime_projection_field(
        &self,
        base_type: &Type,
        selector: &ProductElement,
    ) -> Option<(Type, usize)> {
        if let Type::Tuple(tuple) = base_type {
            let ProductElement::Ordinal(index) = selector else {
                return None;
            };
            let selected = tuple.elements().get(*index)?.clone();
            let offset = tuple.elements()[..*index]
                .iter()
                .map(|field| {
                    self.runtime_shape(field, &mut Vec::new())
                        .shape
                        .stored_words()
                })
                .sum();
            return Some((selected, offset));
        }

        let (name, arguments) = match base_type {
            Type::Constructor(name) => (name, Vec::new()),
            Type::Apply { .. } => applied_type(base_type)?,
            _ => return None,
        };
        let TypeDefinition::Record(record) = self.type_definitions.get(name)? else {
            return None;
        };
        let bindings = record
            .type_parameters
            .iter()
            .zip(arguments)
            .map(|(parameter, argument)| (parameter.name.clone(), argument))
            .collect::<HashMap<_, _>>();
        let mut fields = record.fields.iter().collect::<Vec<_>>();
        fields.sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name));
        let index = match selector {
            ProductElement::Ordinal(index) => *index,
            ProductElement::Name(name) => fields.iter().position(|field| &field.name == name)?,
        };
        let selected =
            instantiate_type_expression(&fields.get(index)?.type_signature.body, &bindings)?;
        let offset = fields[..index]
            .iter()
            .map(|field| {
                let ty = instantiate_type_expression(&field.type_signature.body, &bindings)
                    .expect("a named record field uses only its declared parameters");
                self.runtime_shape(&ty, &mut Vec::new())
                    .shape
                    .stored_words()
            })
            .sum();
        Some((selected, offset))
    }

    // Like `collect_pattern`, but the matched value is a region of a flat object:
    // `base[offset .. offset+width]`, or the whole `base` when `whole`. Reads each
    // sub-pattern's type from its annotation to thread offsets through nested flat
    // records; a whole flat sub-record bind copies out, a further destructure
    // reaches through with no copy.
    fn collect_pattern_flat(
        &self,
        pattern: &phase::Pattern<Closed>,
        base: &str,
        offset: usize,
        width: usize,
        whole: bool,
        tests: &mut Vec<String>,
        binds: &mut Vec<(usize, String)>,
    ) {
        // The value as a single canonical word (a scalar, or a pointer to a boxed
        // sub-object): the whole base, or the one word at `offset`.
        let scalar = || {
            if whole {
                base.to_string()
            } else {
                format!("proj({base}, {offset})")
            }
        };
        match pattern {
            Pattern::Bind(annotation, Identifier::Local(LexicalLevel(level))) => {
                let value = if whole {
                    base.to_string()
                } else if width == 1 {
                    let raw = format!("proj({base}, {offset})");
                    self.decode_one_word_niche(&raw, &annotation.type_info.inferred_type)
                        .unwrap_or(raw)
                } else if self
                    .sum_layout(&annotation.type_info.inferred_type)
                    .is_some()
                {
                    // copy an inlined sum out to a boxed constructor (tag at `offset`,
                    // `width-1` payload words follow).
                    format!(
                        "mk_data_inline(proj({base}, {offset}), {}, &as_tuple({base})->elems[{}])",
                        width - 1,
                        offset + 1
                    )
                } else {
                    // copy the inlined sub-record/tuple out to a fresh flat object
                    let parts: Vec<String> = (0..width)
                        .map(|k| format!("proj({base}, {})", offset + k))
                        .collect();
                    format!("mk_tuple({width}, {})", parts.join(", "))
                };
                binds.push((*level, value));
            }
            Pattern::Bind(_, other) => panic!("pattern binder must be a local: {other:?}"),

            Pattern::Literally(_, literal) => {
                tests.push(format!(
                    "val_eq({}, {})",
                    scalar(),
                    self.compile_constant(literal)
                ));
            }

            Pattern::Struct(annotation, the) => {
                match self.flat_widths(&annotation.type_info.inferred_type) {
                    Some(widths) => {
                        // A record is always a flat object. Locate that object and
                        // where this record's words start in it: itself (whole), a
                        // boxed pointer read out (a width-1 boxed field), or inline
                        // at `offset` (a width>1 inlined field).
                        let (object, start) = if whole {
                            (base.to_string(), 0)
                        } else if width == 1 {
                            (format!("proj({base}, {offset})"), 0)
                        } else {
                            (base.to_string(), offset)
                        };
                        let mut field_offset = start;
                        for ((_label, field), w) in the.fields.iter().zip(widths) {
                            self.collect_pattern_flat(
                                field,
                                &object,
                                field_offset,
                                w,
                                false,
                                tests,
                                binds,
                            );
                            field_offset += w;
                        }
                    }
                    None => {
                        // Polymorphic record: a boxed record, fields by ordinal.
                        let value = scalar();
                        for (index, (_label, field)) in the.fields.iter().enumerate() {
                            self.collect_pattern_flat(
                                field,
                                &format!("proj({value}, {index})"),
                                0,
                                1,
                                true,
                                tests,
                                binds,
                            );
                        }
                    }
                }
            }

            Pattern::Tuple(annotation, the) => {
                // A tuple is flat only when inlined in a flat record (width > 1,
                // not whole): its elements are regions of `base`. Otherwise it is a
                // boxed tuple, matched by ordinal projection.
                if !whole && width > 1 {
                    let element_widths = self
                        .flat_widths(&annotation.type_info.inferred_type)
                        .expect("an inlined tuple field has a tuple type");
                    let mut element_offset = offset;
                    for (element, w) in the.elements.iter().zip(element_widths) {
                        self.collect_pattern_flat(
                            element,
                            base,
                            element_offset,
                            w,
                            false,
                            tests,
                            binds,
                        );
                        element_offset += w;
                    }
                } else {
                    let value = scalar();
                    for (index, element) in the.elements.iter().enumerate() {
                        self.collect_pattern_flat(
                            element,
                            &format!("proj({value}, {index})"),
                            0,
                            1,
                            true,
                            tests,
                            binds,
                        );
                    }
                }
            }

            Pattern::Coproduct(annotation, the) => {
                let Identifier::Global(constructor) = &the.constructor else {
                    panic!(
                        "constructor pattern head must be a global: {:?}",
                        the.constructor
                    );
                };
                if self.newtype_constructors.contains(constructor) {
                    let value = scalar();
                    self.collect_pattern_flat(&the.arguments[0], &value, 0, 1, true, tests, binds);
                } else if !whole
                    && width == 1
                    && let Some((niche_tag, payload_tag)) =
                        self.one_word_niche(&annotation.type_info.inferred_type)
                {
                    let tag = self.constructor_tag(constructor) as usize;
                    let raw = format!("proj({base}, {offset})");
                    if tag == niche_tag && the.arguments.is_empty() {
                        tests.push(format!("{raw}.w == 0"));
                    } else if tag == payload_tag && the.arguments.len() == 1 {
                        tests.push(format!("{raw}.w != 0"));
                        self.collect_pattern_flat(
                            &the.arguments[0],
                            &raw,
                            0,
                            1,
                            true,
                            tests,
                            binds,
                        );
                    } else {
                        tests.push("false".to_string());
                    }
                } else if !whole && width > 1 {
                    // Inlined sum: the tag is the immediate at `offset`, its active
                    // variant's payload the words after it.
                    let layout = self
                        .sum_layout(&annotation.type_info.inferred_type)
                        .expect("an inlined sum field has a sum type");
                    let tag = self.constructor_tag(constructor);
                    let variant = layout.variant_widths[tag as usize].clone();
                    tests.push(format!("as_int(proj({base}, {offset})) == {tag}"));
                    let mut argument_offset = offset + 1;
                    for (argument, w) in the.arguments.iter().zip(variant) {
                        self.collect_pattern_flat(
                            argument,
                            base,
                            argument_offset,
                            w,
                            false,
                            tests,
                            binds,
                        );
                        argument_offset += w;
                    }
                } else {
                    // Boxed sum (standalone whole, or a width-1 pointer field).
                    let value = scalar();
                    tests.push(format!(
                        "data_tag({value}) == {}",
                        self.constructor_tag(constructor)
                    ));
                    for (index, argument) in the.arguments.iter().enumerate() {
                        self.collect_pattern_flat(
                            argument,
                            &format!("data_field({value}, {index})"),
                            0,
                            1,
                            true,
                            tests,
                            binds,
                        );
                    }
                }
            }
        }
    }

    // The runtime tag for a constructor: its position within its sum type's
    // constructor list, recorded by `lambda_lift`. Every `Inject`/`Coproduct`
    // names a real sum-type constructor, so a miss is a compiler invariant break.
    fn constructor_tag(&self, constructor: &QualifiedName) -> u64 {
        *self
            .constructor_tags
            .get(constructor)
            .unwrap_or_else(|| panic!("no constructor tag for {constructor}"))
    }

    // A record is a positional product, exactly like a tuple: its fields are
    // held in a canonical order (sorted by name at construction) and projection
    // is already lowered to `Ordinal`, so the field labels carry no runtime
    // weight -- we just emit the values in field order.
    fn compile_record(
        &self,
        annotation: &CaptureInfo,
        the: &phase::Record<Closed>,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        // Flat path: when the record has a nested inlined field (some width > 1),
        // build ONE object whose body is the fields' flattened leaves. A record
        // with only width-1 fields falls through to the identical tuple lowering
        // below, so non-nested records stay byte-identical.
        if self.flat_records_enabled() {
            if let Some(widths) = self.flat_widths(&annotation.type_info.inferred_type) {
                if widths.iter().any(|&w| w > 1) {
                    let total: usize = widths.iter().sum();
                    let mut prelude = Vec::new();
                    let mut leaves = Vec::new();
                    for ((_label, value), width) in the.fields.iter().zip(&widths) {
                        leaves.extend(self.flat_leaves(value, *width, &mut prelude));
                    }
                    write!(code, "({{ ")?;
                    for binding in &prelude {
                        write!(code, "{binding} ")?;
                    }
                    write!(code, "mk_tuple({total}")?;
                    for leaf in &leaves {
                        write!(code, ", {leaf}")?;
                    }
                    return write!(code, "); }})");
                }
            }
        }

        let mut written = if the.fields.len() <= 4 {
            write!(code, "mk_tuple{}(", the.fields.len())?;
            false
        } else {
            write!(code, "mk_tuple({}", the.fields.len())?;
            true
        };
        for (_label, value) in &the.fields {
            if written {
                write!(code, ", ")?;
            }
            written = true;
            self.compile_expr(value, code)?;
        }
        write!(code, ")")
    }

    fn compile_record_update(
        &self,
        _annotation: &CaptureInfo,
        update: &ast::RecordUpdate<CaptureInfo, Identifier>,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
        write!(code, "({{ Value _rub{id} = ")?;
        self.compile_expr(&update.base, code)?;
        write!(code, "; ")?;

        let mut replacements = Vec::with_capacity(update.fields.len());
        for (field_index, field) in update.fields.iter().enumerate() {
            let temp = format!("_ru{id}_{field_index}");
            write!(code, "Value {temp} = ")?;
            self.compile_expr(&field.value, code)?;
            write!(code, "; ")?;
            replacements.push(temp);
        }

        // Closure conversion may replace the update expression's annotation
        // while preserving the base expression's concrete nominal record type.
        let root_type = &update.base.annotation().type_info.inferred_type;
        let widths = self
            .flat_widths(root_type)
            .unwrap_or_else(|| panic!("record update base layout: {root_type:?}"));
        let total: usize = widths.iter().sum();
        let base_leaves = (0..total)
            .map(|offset| format!("proj(_rub{id}, {offset})"))
            .collect();
        let leaves = self.record_update_leaves(update, &[], root_type, base_leaves, &replacements);
        write!(code, "mk_tuple({total}")?;
        for leaf in leaves {
            write!(code, ", {leaf}")?;
        }
        write!(code, "); }})")
    }

    fn canonical_update_leaves(&self, value: &str, ty: &Type, width: usize) -> Vec<String> {
        if width == 1 {
            if let Some(encoded) = self.encode_one_word_niche(value, ty) {
                return vec![encoded];
            }
            return vec![value.to_string()];
        }
        if self.sum_layout(ty).is_some() {
            let mut leaves = vec![format!("VInt(data_tag({value}))")];
            for index in 0..width - 1 {
                leaves.push(format!("(({index}) < data_len({value}) ? data_field({value}, {index}) : ((Value){{0}}))"));
            }
            leaves
        } else {
            (0..width)
                .map(|index| format!("proj({value}, {index})"))
                .collect()
        }
    }

    fn record_update_leaves(
        &self,
        update: &ast::RecordUpdate<CaptureInfo, Identifier>,
        prefix: &[usize],
        ty: &Type,
        mut base_leaves: Vec<String>,
        replacements: &[String],
    ) -> Vec<String> {
        let widths = self.flat_widths(ty).expect("dotted update record layout");
        let total: usize = widths.iter().sum();
        if base_leaves.len() == 1 && total > 1 {
            let base = &base_leaves[0];
            base_leaves = (0..total)
                .map(|index| format!("proj({base}, {index})"))
                .collect();
        }
        let mut result = Vec::with_capacity(total);
        let mut offset = 0;
        for (index, width) in widths.into_iter().enumerate() {
            let mut path = prefix.to_vec();
            path.push(index);
            let field_type = self
                .runtime_projection_field(ty, &ProductElement::Ordinal(index))
                .expect("typed dotted update field")
                .0;
            if let Some((replacement_index, _)) = update
                .fields
                .iter()
                .enumerate()
                .find(|(_, field)| field.indices == path)
            {
                result.extend(self.canonical_update_leaves(
                    &replacements[replacement_index],
                    &field_type,
                    width,
                ));
            } else if update
                .fields
                .iter()
                .any(|field| field.indices.starts_with(&path))
            {
                result.extend(self.record_update_leaves(
                    update,
                    &path,
                    &field_type,
                    base_leaves[offset..offset + width].to_vec(),
                    replacements,
                ));
            } else {
                result.extend(base_leaves[offset..offset + width].iter().cloned());
            }
            offset += width;
        }
        result
    }

    fn compile_projection(
        &self,
        annotation: &CaptureInfo,
        the: &phase::Projection<Closed>,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        // Flat path: a projection into a flat record reaches a computed word
        // offset (nested projections accumulate, so `r.b.c` is one load); pulling
        // out a whole inlined sub-aggregate copies it out to a fresh object -- a
        // record/tuple to a tuple, an inlined sum to a boxed constructor.
        if self.flat_records_enabled() {
            if let Some((words, offset, selected_type, shape)) = self.flat_value_region(the) {
                if matches!(shape, RuntimeShape::Leaf) {
                    return write!(code, "{}", words[offset]);
                }
                if shape.stored_words() == 1
                    && let Some(decoded) =
                        self.decode_one_word_niche(&words[offset], &selected_type)
                {
                    return write!(code, "{decoded}");
                }
                if matches!(shape, RuntimeShape::Product(_)) {
                    return write!(
                        code,
                        "{}",
                        Self::tuple_from_words(&words[offset..offset + shape.stored_words()])
                    );
                }
            }
            if direct_array_enabled()
                && let Some((array, index, offset, selected_type, shape)) =
                    self.flat_array_region(&Expr::Project(annotation.clone(), the.clone()))
            {
                let raw =
                    format!("flat_array_get_word({array}, (size_t)as_int({index}), {offset})");
                if matches!(shape, RuntimeShape::Leaf) {
                    return write!(code, "{raw}");
                }
                if shape.stored_words() == 1
                    && let Some(decoded) = self.decode_one_word_niche(&raw, &selected_type)
                {
                    return write!(code, "{decoded}");
                }
            }
            if let Some((base, offset, width)) = self.flat_place(the) {
                if width == 1 {
                    let raw = format!("proj({base}, {offset})");
                    if let Some(decoded) =
                        self.decode_one_word_niche(&raw, &annotation.type_info.inferred_type)
                    {
                        return write!(code, "{decoded}");
                    }
                    return write!(code, "proj({base}, {offset})");
                }
                if self
                    .sum_layout(&annotation.type_info.inferred_type)
                    .is_some()
                {
                    return write!(
                        code,
                        "mk_data_inline(proj({base}, {offset}), {}, &as_tuple({base})->elems[{}])",
                        width - 1,
                        offset + 1
                    );
                }
                write!(code, "mk_tuple({width}")?;
                for k in 0..width {
                    write!(code, ", proj({base}, {})", offset + k)?;
                }
                return write!(code, ")");
            }
        }

        match &the.select {
            ProductElement::Ordinal(i) => {
                write!(code, "proj(")?;
                self.compile_expr(&the.base, code)?;
                write!(code, ", {i})")
            }
            // Record projections are lowered to ordinals before codegen.
            ProductElement::Name(_id) => panic!("named projections are lowered to ordinals"),
        }
    }

    // `deconstruct scrutinee into <clauses>` compiles to a right-nested ternary
    // over the clauses: each clause's refutable tests (guarding its position in
    // the product/coproduct) gate a statement expression that binds its pattern
    // variables and yields the consequent. The scrutinee is evaluated once into a
    // fresh temporary. An exhausted match hits the runtime's `match_fail`.
    fn compile_deconstruct(
        &self,
        the: &phase::Deconstruct<Closed>,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);

        // Match a packed ARRAY element in place.  A let-bound raw get records
        // its (array,index) pair in `ARRAY_ELEMENT_PLACES`; matching that value
        // can then read the tag and scalar fields directly from the backing
        // storage instead of first rebuilding a canonical tuple/data object.
        if direct_array_enabled()
            && let Some((array, index, offset, element_type, fallback_shape)) =
                self.flat_array_region(&the.scrutinee)
            && element_type.variables().is_empty()
        {
            if std::env::var_os("DUMP_DIRECT_READ").is_some() {
                eprintln!(
                    "[direct-read] scrutinee={} ground={} fallback={fallback_shape:?}",
                    the.scrutinee.annotation().type_info.inferred_type,
                    the.scrutinee
                        .annotation()
                        .type_info
                        .inferred_type
                        .variables()
                        .is_empty(),
                );
            }
            // Plan EVERY clause before emitting anything. `collect_array_pattern` can
            // decline a clause even when `array_match_shape` accepted the shape, and this
            // used to only `debug_assert!` it -- so a release build emitted the direct path
            // anyway with an empty bind list, and the clause body referenced a local that
            // the lazy `let` had already elided ("use of undeclared identifier lN").
            // Declining here restores the canonical path, and
            // `local_uses_are_flat_array_leaves` runs the same planning so the `let` is
            // kept whenever we end up needing it.
            let plan = self
                .array_match_shape(&the.match_clauses, &fallback_shape)
                .and_then(|shape| {
                    let array_local = format!("_ma{id}");
                    let index_local = format!("_mi{id}");
                    let plans = self.plan_array_match(
                        &the.match_clauses,
                        &array_local,
                        &index_local,
                        offset,
                        &shape,
                    )?;
                    Some((array_local, index_local, plans))
                });
            if let Some((array_local, index_local, plans)) = plan {
                write!(
                    code,
                    "({{ Value {array_local} = {array}; Value {index_local} = {index}; "
                )?;

                for (clause, (tests, binds)) in the.match_clauses.iter().zip(&plans) {
                    if tests.is_empty() {
                        write!(code, "true")?;
                    } else {
                        write!(code, "{}", tests.join(" && "))?;
                    }
                    write!(code, " ? ({{ ")?;
                    for (level, path) in binds {
                        write!(code, "Value l{level} = {path}; ")?;
                    }
                    self.compile_expr(&clause.consequent, code)?;
                    write!(code, "; }}) : ")?;
                }

                return write!(code, "match_fail(); }})");
            }
        }

        // A multiword sum projected out of a flat record is already a readable
        // region (tag followed by payload words).  If it is consumed immediately
        // by a constructor match, inspect that region directly instead of calling
        // `mk_data_inline` merely so `data_tag`/`data_field` can unpack it again.
        if let Expr::Project(_, projection) = strip_ascription(&the.scrutinee) {
            if let Some((base, offset, width)) = self.flat_place(projection) {
                if (width > 1
                    || self
                        .one_word_niche(&the.scrutinee.annotation().type_info.inferred_type)
                        .is_some())
                    && the
                        .match_clauses
                        .iter()
                        .all(|clause| !matches!(clause.pattern, Pattern::Bind(..)))
                {
                    let flat_local = format!("_flat{id}");
                    write!(code, "({{ Value {flat_local} = {base}; ")?;
                    for clause in &the.match_clauses {
                        let mut tests = Vec::new();
                        let mut binds = Vec::new();
                        self.collect_pattern_flat(
                            &clause.pattern,
                            &flat_local,
                            offset,
                            width,
                            false,
                            &mut tests,
                            &mut binds,
                        );
                        if tests.is_empty() {
                            write!(code, "true")?;
                        } else {
                            write!(code, "{}", tests.join(" && "))?;
                        }
                        write!(code, " ? ({{ ")?;
                        for (level, path) in &binds {
                            write!(code, "Value l{level} = {path}; ")?;
                        }
                        self.compile_expr(&clause.consequent, code)?;
                        write!(code, "; }}) : ")?;
                    }
                    return write!(code, "match_fail(); }})");
                }
            }
        }

        let scrutinee = format!("_scrut{id}");

        write!(code, "({{ Value {scrutinee} = ")?;
        self.compile_expr(&the.scrutinee, code)?;
        write!(code, "; ")?;

        for clause in &the.match_clauses {
            let mut tests = Vec::new();
            let mut binds = Vec::new();
            if self.flat_records_enabled() {
                self.collect_pattern_flat(
                    &clause.pattern,
                    &scrutinee,
                    0,
                    1,
                    true,
                    &mut tests,
                    &mut binds,
                );
            } else {
                self.collect_pattern(&clause.pattern, &scrutinee, &mut tests, &mut binds);
            }

            if tests.is_empty() {
                write!(code, "true")?;
            } else {
                write!(code, "{}", tests.join(" && "))?;
            }
            write!(code, " ? ({{ ")?;
            for (level, path) in &binds {
                write!(code, "Value l{level} = {path}; ")?;
            }
            self.compile_expr(&clause.consequent, code)?;
            write!(code, "; }}) : ")?;
        }

        write!(code, "match_fail(); }})")
    }

    // Walk a pattern against a C expression `path` for the value it matches,
    // accumulating boolean `tests` (the refutable checks) and `binds` (each
    // pattern variable's `Local` slot paired with the path that reaches it).
    fn collect_pattern(
        &self,
        pattern: &phase::Pattern<Closed>,
        path: &str,
        tests: &mut Vec<String>,
        binds: &mut Vec<(usize, String)>,
    ) {
        match pattern {
            Pattern::Bind(_, Identifier::Local(LexicalLevel(level))) => {
                binds.push((*level, path.to_owned()));
            }
            Pattern::Bind(_, other) => panic!("pattern binder must be a local: {other:?}"),

            Pattern::Literally(_, literal) => {
                tests.push(format!(
                    "val_eq({path}, {})",
                    self.compile_constant(literal)
                ));
            }

            Pattern::Tuple(_, the) => {
                for (index, element) in the.elements.iter().enumerate() {
                    self.collect_pattern(element, &format!("proj({path}, {index})"), tests, binds);
                }
            }

            Pattern::Struct(_, the) => {
                for (index, (_label, field)) in the.fields.iter().enumerate() {
                    self.collect_pattern(field, &format!("proj({path}, {index})"), tests, binds);
                }
            }

            // A constructor pattern: test the integer tag against the
            // constructor's ordinal, then match each argument against field `i`
            // (mirroring `compile_inject`'s layout).
            Pattern::Coproduct(_, the) => {
                let Identifier::Global(constructor) = &the.constructor else {
                    panic!(
                        "constructor pattern head must be a global: {:?}",
                        the.constructor
                    );
                };
                // A newtype pattern is erased: the value IS its single field, so
                // there is no tag to test and the field matches against the
                // scrutinee itself -- `λ(Buffer b). e` lowers to `λb. e`.
                if self.newtype_constructors.contains(constructor) {
                    self.collect_pattern(&the.arguments[0], path, tests, binds);
                } else {
                    tests.push(format!(
                        "data_tag({path}) == {}",
                        self.constructor_tag(constructor)
                    ));
                    for (index, argument) in the.arguments.iter().enumerate() {
                        self.collect_pattern(
                            argument,
                            &format!("data_field({path}, {index})"),
                            tests,
                            binds,
                        );
                    }
                }
            }
        }
    }

    // Application. A saturated application of a primitive builtin lowers to a
    // direct call (`prim_add(x, y)`) -- no intermediate closures, no allocation,
    // no indirection. Everything else is the uniform `apply(closure, argument)`;
    // since a builtin's value is still a curried closure, partial application
    // and higher-order use fall through to this path unchanged.
    fn compile_apply(
        &self,
        annotation: &CaptureInfo,
        the: &phase::Apply<Closed>,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        // Flatten the application spine into (head, args-in-order).
        let mut args: Vec<&Expr> = vec![&the.argument];
        let mut head: &Expr = &the.function;
        while let Expr::Apply(_, inner) = head {
            args.push(&inner.argument);
            head = &inner.function;
        }
        args.reverse();

        // `omg_wtf_bbq` deliberately keeps the ordinary surface type `Text -> a`.
        // Its private foreign worker has extra diagnostic parameters; inject them
        // here, after all transformations, from metadata carried by the call node.
        if args.len() == 1
            && let Expr::Variable(_, Identifier::Global(name)) = head
            && (surface_name(name).ends_with("Root_Prelude_raw_omg_wtf_bbq")
                || surface_name(name).ends_with("Root_Prelude_omg_wtf_bbq"))
        {
            let info = &annotation.type_info;
            let function = info
                .enclosing_term
                .as_ref()
                .map(ToString::to_string)
                .unwrap_or_else(|| "<unknown>".to_owned());
            let file = crate::source_map::path_of(info.parse_info.file)
                .map(|p| p.display().to_string())
                .unwrap_or_else(|| "<unknown>".to_owned());
            write!(
                code,
                "{}_worker({}, {}, VInt({}), VInt({}), ",
                "Root_Prelude_raw_omg_wtf_bbq",
                self.compile_constant(&Literal::Text(function)),
                self.compile_constant(&Literal::Text(file)),
                info.parse_info.location.row,
                info.parse_info.location.column,
            )?;
            self.compile_expr(args[0], code)?;
            return write!(code, ")");
        }

        // A saturated write-only packed-array primitive whose replacement is a
        // structural literal can write its already-evaluated leaves straight into
        // the slot. This avoids constructing a canonical record/sum only for the
        // runtime shape interpreter to immediately dismantle it again.
        if direct_write_enabled()
            && args.len() == 3
            && matches!(
                head,
                Expr::Variable(_, Identifier::Global(..)) | Expr::InvokeBridge(..)
            )
        {
            let name = match head {
                Expr::Variable(_, Identifier::Global(name)) => name.as_ref(),
                Expr::InvokeBridge(_, bridge) => &bridge.qualified_name,
                _ => unreachable!(),
            };
            if surface_name(name).ends_with("Stdlib_Data_Array_Mutable_Array_raw_set_unchecked") {
                let ground = args[2]
                    .annotation()
                    .type_info
                    .inferred_type
                    .variables()
                    .is_empty();
                if std::env::var_os("DUMP_DIRECT_WRITE").is_some() && !ground {
                    eprintln!(
                        "[direct-write-skip] non-ground type={}",
                        args[2].annotation().type_info.inferred_type,
                    );
                }
                if ground {
                    let shape = self
                        .runtime_shape(
                            &args[2].annotation().type_info.inferred_type,
                            &mut Vec::new(),
                        )
                        .shape;
                    let width = shape.stored_words();
                    let mut prelude = Vec::new();
                    let leaves = self.literal_shape_leaves(args[2], &shape, &mut prelude);
                    if std::env::var_os("DUMP_DIRECT_WRITE").is_some() {
                        eprintln!(
                            "[direct-write] type={} node={} width={width} leaves={} prelude={}",
                            args[2].annotation().type_info.inferred_type,
                            match strip_ascription(args[2]) {
                                Expr::Record(..) => "record",
                                Expr::Tuple(..) => "tuple",
                                Expr::Inject(..) => "inject",
                                Expr::Apply(..) => "apply",
                                Expr::Let(..) => "let",
                                Expr::Variable(..) => "variable",
                                _ => "other",
                            },
                            leaves.as_ref().map_or(0, Vec::len),
                            prelude.len(),
                        );
                        for binding in &prelude {
                            eprintln!("[direct-write-prelude] {binding}");
                        }
                    }
                    if let Some(leaves) = leaves
                        && leaves.len() == width
                    {
                        let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
                        write!(code, "({{ Value _wa{id} = ")?;
                        self.compile_expr(args[0], code)?;
                        write!(code, "; Value _wi{id} = ")?;
                        self.compile_expr(args[1], code)?;
                        write!(code, "; ")?;
                        // Prelude bindings evaluate a non-literal replacement exactly
                        // once, after the array and index as required by source order.
                        // Value locals remain visible to the conservative stack scanner
                        // across any allocations performed by later leaf expressions.
                        for binding in &prelude {
                            write!(code, "{binding} ")?;
                        }
                        for (offset, leaf) in leaves.iter().enumerate() {
                            write!(code, "Value _wv{id}_{offset} = {leaf}; ")?;
                        }
                        for offset in 0..leaves.len() {
                            write!(
                                code,
                                "flat_array_set_word(_wa{id}, (size_t)as_int(_wi{id}), {offset}, _wv{id}_{offset}); "
                            )?;
                        }
                        return write!(code, "VUnit(); }})");
                    }
                }
            }
        }

        if let Some((prim, arity)) = builtin_prim(head) {
            if arity == args.len() {
                // `prim_show` is monomorphised: the runtime carries no immediate tag, so
                // codegen picks the leaf (`prim_show_int`/`_char`/`_text`) from the
                // argument's static type. Only primitive types reach here -- compound
                // values are rendered by their `Display` witnesses.
                let prim = if prim == "prim_show" {
                    show_prim(args[0])
                } else {
                    // The arithmetic/ordering/logical prims are monomorphised on the
                    // operands' static type: a Float operand routes to the boxed-double
                    // prim, an Int operand routes `and`/`or`/`xor` to their bitwise
                    // variant, a Text operand routes `=` to the direct slice compare;
                    // everything else keeps the int/generic prim.
                    let operand = &args[0].annotation().type_info.inferred_type;
                    match operand {
                        Type::Base(BaseType::Float) => float_prim(prim).unwrap_or(prim),
                        Type::Base(
                            BaseType::Int | BaseType::Bool | BaseType::Unit | BaseType::Char,
                        ) if prim == "prim_eq" => "prim_word_eq",
                        Type::Base(BaseType::Int) => bitwise_prim(prim).unwrap_or(prim),
                        _ if prim == "prim_eq" && is_text_type(operand) => "prim_text_eq",
                        _otherwise => prim,
                    }
                };
                write!(code, "{prim}(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(code, ", ")?;
                    }
                    self.compile_expr(arg, code)?;
                }
                return write!(code, ")");
            }
        }

        // A *saturated* application of a known-arity function (currently the
        // foreign functions) lowers to a direct call to its uncurried worker --
        // no intermediate closures, no allocation. Under- or over-saturated calls
        // fall through to the curried `apply` path below.
        if let Expr::Variable(_, Identifier::Global(qualified_name)) = head {
            if self.arities.get(qualified_name.as_ref()) == Some(&args.len()) {
                write!(code, "{}_worker(", c_name(qualified_name.as_ref()))?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(code, ", ")?;
                    }
                    self.compile_expr(arg, code)?;
                }
                return write!(code, ")");
            }
        }

        // A closure which is constructed only to be called at this very site does not
        // need a heap lifetime.  Its descriptor and captures can form a closure-shaped
        // frame on the C stack, and the lifted code (or saturated chain worker) can be
        // called directly with that frame as `self`.
        //
        // Recursive closures are safe too, provided `self` is used exclusively as the
        // head of a saturated recursive call: every such call finishes before this C
        // expression returns, so the stack frame is still alive.  A returned, captured,
        // stored, or otherwise passed-around `self` is rejected by
        // `self_references_are_calls` and keeps the ordinary heap closure path.
        if let Some(result) = self.compile_immediate_closure_apply(head, &args, code) {
            return result;
        }

        // Generic path. A multi-argument application of an unknown head (a curried
        // function *value*, e.g. a parameter passed to a higher-order function)
        // goes through `apply_n`, which dispatches straight to the head's
        // uncurried worker when it carries one and is saturated -- skipping the
        // intermediate currying-stage closures -- and otherwise falls back to
        // applying one argument at a time. A single-argument application has no
        // stage to skip, so it stays the leaner `apply`.
        if args.len() >= 2 {
            write!(code, "apply_n(")?;
            self.compile_expr(head, code)?;
            write!(code, ", {}, (Value[]){{", args.len())?;
            for (i, arg) in args.iter().enumerate() {
                if i > 0 {
                    write!(code, ", ")?;
                }
                self.compile_expr(arg, code)?;
            }
            return write!(code, "}})");
        }

        write!(code, "apply(")?;
        self.compile_expr(&the.function, code)?;
        write!(code, ", ")?;
        self.compile_expr(&the.argument, code)?;
        write!(code, ")")
    }

    /// Evaluate a closure's logical captures and return the physical capture
    /// words. Ground record captures are split according to the lifted frame's
    /// layout; scalar and polymorphic captures remain one word.
    fn compile_capture_values(
        &self,
        lifted_name: &QualifiedName,
        elements: &[Rc<Expr>],
        stem: &str,
        code: &mut CodeBuffer,
    ) -> Result<Vec<String>, fmt::Error> {
        let places = self.capture_places(lifted_name);
        if places.len() != elements.len() {
            return Err(fmt::Error);
        }
        let mut values = Vec::new();
        for (capture, (element, place)) in elements.iter().zip(&places).enumerate() {
            if place.width == 1 {
                let name = format!("{stem}_{capture}");
                write!(code, "volatile Value {name} = ")?;
                self.compile_expr(element, code)?;
                write!(code, "; ")?;
                values.push(name);
                continue;
            }

            let shape = self.runtime_shape(&place.ty, &mut Vec::new()).shape;
            let mut prelude = Vec::new();
            let leaves = self
                .literal_shape_leaves(element, &shape, &mut prelude)
                .filter(|leaves| leaves.len() == place.width)
                .ok_or(fmt::Error)?;
            for binding in prelude {
                write!(code, "{binding} ")?;
            }
            for (word, leaf) in leaves.into_iter().enumerate() {
                let name = format!("{stem}_{capture}_{word}");
                write!(code, "volatile Value {name} = {leaf}; ")?;
                values.push(name);
            }
        }
        Ok(values)
    }

    /// Directly call an immediately-applied closure through a stack-resident closure
    /// frame.  Returns `None` whenever the application is partial/over-saturated or
    /// `self` could escape the dynamic extent of the call.
    fn compile_immediate_closure_apply(
        &self,
        head: &Expr,
        args: &[&Expr],
        code: &mut CodeBuffer,
    ) -> Option<fmt::Result> {
        let Expr::MakeClosure(_, closure) = strip_ascription(head) else {
            return None;
        };
        let Expr::Tuple(_, environment) = closure.environment.as_ref() else {
            return None;
        };

        // A saturated curried chain has a flattened worker.  Otherwise only an
        // ordinary one-stage application can directly enter the lifted function.
        let chain_arity = self.chain_heads.get(&closure.lifted_name).copied();
        let (body, recursive_arity, direct_worker) = if chain_arity == Some(args.len()) {
            let worker = self
                .chain_workers
                .iter()
                .find(|worker| worker.head == closure.lifted_name)?;
            (&worker.body, worker.arity, true)
        } else if args.len() == 1 {
            let lifted = self
                .functions
                .iter()
                .find(|function| function.name == closure.lifted_name)?;
            (&lifted.code, 1, false)
        } else {
            return None;
        };

        if !Self::self_references_are_calls(body, recursive_arity) {
            return None;
        }

        let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
        let name = c_name(&closure.lifted_name);

        let (descriptor_worker, descriptor_arity) = match chain_arity {
            Some(arity) => (format!("{name}_uworker"), arity),
            None => ("NULL".to_owned(), 1),
        };

        let result = (|| {
            write!(code, "({{ ")?;
            if environment.elements.is_empty() {
                write!(
                    code,
                    "Value _sf{id} = STATIC_CLOSURE0({name}, {descriptor_worker}, {descriptor_arity}); "
                )?;
            } else {
                let capture_values = self.compile_capture_values(
                    &closure.lifted_name,
                    &environment.elements,
                    &format!("_sv{id}"),
                    code,
                )?;
                let captures = capture_values.len();

                // The collector finds live Values by scanning C stack memory.  With
                // LTO, an ordinary local aggregate could be scalar-replaced into
                // registers across an allocating argument expression; `volatile`
                // keeps every capture materialized in the stack frame for the whole
                // immediate call.
                write!(
                    code,
                    "static const ClosureDesc _sd{id} = {{{name}, {descriptor_worker}, {descriptor_arity}}}; "
                )?;
                write!(
                    code,
                    "volatile struct {{ const ClosureDesc *desc; Value caps[{captures}]; }} _sc{id} = {{&_sd{id}, {{"
                )?;
                for (index, value) in capture_values.iter().enumerate() {
                    if index > 0 {
                        write!(code, ", ")?;
                    }
                    write!(code, "{value}")?;
                }
                write!(code, "}}}}; Value _sf{id} = VObject((void *)&_sc{id}); ")?;
            }

            // Sequence source arguments explicitly.  Apart from preserving language
            // evaluation order, the Value locals keep earlier arguments visible to the
            // conservative stack scanner if a later argument allocates and triggers GC.
            for (index, argument) in args.iter().enumerate() {
                write!(code, "Value _sa{id}_{index} = ")?;
                self.compile_expr(argument, code)?;
                write!(code, "; ")?;
            }

            if direct_worker {
                write!(code, "{name}_uworker(_sf{id}, (Value[]){{")?;
                for index in 0..args.len() {
                    if index > 0 {
                        write!(code, ", ")?;
                    }
                    write!(code, "_sa{id}_{index}")?;
                }
                write!(code, "}}); }})")
            } else {
                write!(code, "{name}(_sf{id}, _sa{id}_0); }})")
            }
        })();
        Some(result)
    }

    /// True when every reference to a recursive closure's `self` is the head of a
    /// saturated recursive call.  Such calls cannot make the closure outlive an
    /// immediate application; every other use (returning it, passing it as data,
    /// capturing it in another closure, storing it, partial application) is an escape.
    fn self_references_are_calls(expression: &Expr, arity: usize) -> bool {
        let expression = strip_ascription(expression);
        if matches!(expression, Expr::Apply(..)) {
            let mut arguments = Vec::new();
            let mut head = expression;
            while let Expr::Apply(_, application) = strip_ascription(head) {
                arguments.push(application.argument.as_ref());
                head = application.function.as_ref();
            }
            if matches!(
                strip_ascription(head),
                Expr::Variable(_, Identifier::SelfRef)
            ) {
                return arguments.len() == arity
                    && arguments
                        .iter()
                        .all(|argument| Self::self_references_are_calls(argument, arity));
            }
        }

        match expression {
            Expr::Variable(_, Identifier::SelfRef) => false,
            Expr::Variable(..) | Expr::InvokeBridge(..) | Expr::Constant(..) => true,
            Expr::RecursiveLambda(_, lambda) => {
                Self::self_references_are_calls(&lambda.lambda.body, arity)
            }
            Expr::Lambda(_, lambda) => Self::self_references_are_calls(&lambda.body, arity),
            Expr::Apply(_, application) => {
                Self::self_references_are_calls(&application.function, arity)
                    && Self::self_references_are_calls(&application.argument, arity)
            }
            Expr::Let(_, binding) => {
                Self::self_references_are_calls(&binding.bound, arity)
                    && Self::self_references_are_calls(&binding.body, arity)
            }
            Expr::Tuple(_, tuple) => tuple
                .elements
                .iter()
                .all(|element| Self::self_references_are_calls(element, arity)),
            Expr::Record(_, record) => record
                .fields
                .iter()
                .all(|(_, field)| Self::self_references_are_calls(field, arity)),
            Expr::RecordUpdate(_, update) => {
                Self::self_references_are_calls(&update.base, arity)
                    && update
                        .fields
                        .iter()
                        .all(|field| Self::self_references_are_calls(&field.value, arity))
            }
            Expr::Inject(_, injection) => injection
                .arguments
                .iter()
                .all(|argument| Self::self_references_are_calls(argument, arity)),
            Expr::Array(_, array) => array
                .elements
                .iter()
                .all(|element| Self::self_references_are_calls(element, arity)),
            Expr::Project(_, projection) => {
                Self::self_references_are_calls(&projection.base, arity)
            }
            Expr::Sequence(_, sequence) => {
                Self::self_references_are_calls(&sequence.this, arity)
                    && Self::self_references_are_calls(&sequence.and_then, arity)
            }
            Expr::Deconstruct(_, deconstruct) => {
                Self::self_references_are_calls(&deconstruct.scrutinee, arity)
                    && deconstruct
                        .match_clauses
                        .iter()
                        .all(|clause| Self::self_references_are_calls(&clause.consequent, arity))
            }
            Expr::If(_, conditional) => {
                Self::self_references_are_calls(&conditional.predicate, arity)
                    && Self::self_references_are_calls(&conditional.consequent, arity)
                    && Self::self_references_are_calls(&conditional.alternate, arity)
            }
            Expr::Interpolate(_, interpolation) => {
                interpolation.0.iter().all(|segment| match segment {
                    Segment::Literal(..) => true,
                    Segment::Expression(expression) => {
                        Self::self_references_are_calls(expression, arity)
                    }
                })
            }
            Expr::Ascription(_, ascription) => {
                Self::self_references_are_calls(&ascription.ascribed_tree, arity)
            }
            Expr::MakeClosure(_, closure) => {
                Self::self_references_are_calls(&closure.environment, arity)
            }
        }
    }

    // A closure value: the lifted function's code paired with a freshly built
    // environment tuple of its captured values. When the closure is the head of a
    // non-recursive curried chain, it also carries its uncurried worker and arity
    // (via `mk_closure_n`), so a saturated `apply_n` runs the chain in one flat
    // frame instead of allocating a currying closure per stage.
    fn compile_closure(&self, the: &ClosureInfo, code: &mut CodeBuffer) -> fmt::Result {
        // The captured values live inline in the closure (a "flat" closure), so
        // emit them directly as arguments to `mk_closure`/`mk_closure_n` -- one
        // heap object, no separate environment tuple. The closure-conversion pass
        // always builds the environment as a tuple, whose elements are exactly the
        // captures in slot order.
        let Expr::Tuple(_, env) = the.environment.as_ref() else {
            panic!("closure environment is always a tuple");
        };
        let name = c_name(&the.lifted_name);
        // The per-function `code`/`worker`/`arity` are identical for every closure of
        // this lifted function, so emit ONE shared static `ClosureDesc`; the heap
        // closure stores just a pointer to it plus the captures (24 B smaller). A
        // curried-chain head carries an uncurried worker + its arity; a plain
        // single-stage closure has `worker = NULL`, `arity = 1`.
        let (worker, arity) = match self.chain_heads.get(&the.lifted_name) {
            Some(&arity) => (format!("{name}_uworker"), arity),
            None => ("NULL".to_owned(), 1),
        };
        // Capture-free: identical + immutable, so a single static instance, no heap
        // allocation at all (mirrors the borrowed-string descriptors).
        if env.elements.is_empty() {
            return write!(code, "STATIC_CLOSURE0({name}, {worker}, {arity})");
        }
        // Per-site static descriptor, then a heap {desc, captures}. Statement-expression
        // scoping keeps each site's `__d` local, so `&__d` binds to this site's descriptor
        // even when a captured expression is itself a closure with its own `__d`.
        let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
        write!(code, "({{ ")?;
        let capture_values = self.compile_capture_values(
            &the.lifted_name,
            &env.elements,
            &format!("_cv{id}"),
            code,
        )?;
        let n = capture_values.len();
        write!(
            code,
            "static const ClosureDesc __d = {{{name}, {worker}, {arity}}}; "
        )?;
        if n <= 4 {
            write!(code, "mk_closure_d{n}(&__d")?;
        } else {
            write!(code, "mk_closure_dn(&__d, {n}")?;
        }
        for value in capture_values {
            write!(code, ", {value}")?;
        }
        write!(code, "); }})")
    }

    // String interpolation concatenates its segments: literal text verbatim,
    // embedded expressions rendered through `prim_show` (matching the Scheme
    // backend's `string-append` + `show`).
    fn compile_interpolate(
        &self,
        segments: &[Segment<CaptureInfo, Identifier>],
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        write!(code, "prim_str_concat({}", segments.len())?;
        for segment in segments {
            write!(code, ", ")?;
            match segment {
                Segment::Literal(_, literal) => write!(code, "{}", self.compile_constant(literal))?,
                Segment::Expression(expr) => {
                    // The parser already wraps each interpolated expression in `display`, so the
                    // segment is a `Text`-typed term -- emit it directly (a redundant `prim_show`
                    // here would just re-copy the slice).
                    self.compile_expr(expr, code)?;
                }
            }
        }
        write!(code, ")")
    }

    fn compile_sequence(
        &self,
        the: &phase::Sequence<Closed>,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        write!(code, "(")?;
        self.compile_expr(&the.this, code)?;
        write!(code, ", ")?;
        self.compile_expr(&the.and_then, code)?;
        write!(code, ")")
    }

    fn compile_if(&self, the: &phase::IfThenElse<Closed>, code: &mut CodeBuffer) -> fmt::Result {
        write!(code, "(as_bool(")?;
        self.compile_expr(&the.predicate, code)?;
        write!(code, ") ? ")?;
        self.compile_expr(&the.consequent, code)?;
        write!(code, " : ")?;
        self.compile_expr(&the.alternate, code)?;
        write!(code, ")")
    }

    fn compile_var(&self, var: &Identifier) -> String {
        match var {
            // A local bound to a flat array element may have had its `let` ELIDED in
            // favour of an (array, index) place, so `l{level}` names nothing. Every
            // consumer that reads leaves out of the place resolves it itself; this is
            // the fallback for the ones that genuinely need the value -- rebuild the
            // canonical element rather than emit a dangling identifier.
            //
            // Without this, a path that declines the in-place read (e.g. the multiword
            // `_flat` projection matcher, whose `flat_place` compiles the base as a plain
            // local) emitted "use of undeclared identifier lN" and the program did not
            // compile at all.
            Identifier::Local(LexicalLevel(level)) => FLAT_VALUE_PLACES
                .with(|places| places.borrow().get(level).cloned())
                .map(|place| Self::tuple_from_words(&place.words))
                .or_else(|| {
                    ARRAY_ELEMENT_PLACES
                        .with(|places| places.borrow().get(level).cloned())
                        .filter(|place| !place.array.is_empty() && !place.index.is_empty())
                        .map(|place| {
                            format!(
                                "flat_array_get({}, (size_t)as_int({}))",
                                place.array, place.index
                            )
                        })
                })
                .unwrap_or_else(|| format!("l{level}")),
            Identifier::Captured(capture) => {
                let index = capture.index();
                Self::current_capture_place(index).map_or_else(
                    || format!("env_get(self, {index})"),
                    |place| {
                        if place.width == 1 {
                            format!("env_get(self, {})", place.offset)
                        } else {
                            let words = (0..place.width)
                                .map(|word| format!("env_get(self, {})", place.offset + word))
                                .collect::<Vec<_>>();
                            Self::tuple_from_words(&words)
                        }
                    },
                )
            }
            Identifier::SelfRef => "self".to_owned(),
            Identifier::Global(qualified_name) => c_name(qualified_name),
        }
    }

    fn compile_constant(&self, the: &Literal) -> String {
        match the {
            Literal::Int(x) => format!("VInt({x})"),
            // A Float literal is a fixed, immortal boxed double: emit ONE `.rodata`
            // STATIC_FLOAT box (like a static Text) rather than heap-allocating on every
            // mention. `{x:?}` keeps the decimal point, so the C `double` literal is
            // valid (`1.0`, not `1`).
            Literal::Float(x) => format!("STATIC_FLOAT({x:?})"),
            // A string literal is a `Text` -- the stdlib DU `Text ::= Text Bytes`, which
            // newtype-erases to a `Bytes`, which erases to an OBJ_SLICE. So emit an
            // immortal .rodata Text: a `static const` OBJ_BYTES body holding the bytes,
            // plus a `static const` OBJ_SLICE over it, both `MARM_ETERNAL` so the GC
            // never touches them. Zero copy, zero per-use allocation, valid-by-
            // construction (no runtime UTF-8 check -- the source is known-good).
            // `sizeof("...")` sizes the body (escapes handled by the C compiler); the
            // slice length excludes the trailing NUL. `static` locals in a statement
            // expression have static storage duration -> they land in .rodata.
            Literal::Text(x) => {
                // The `Text` may hold characters that are special in a C string literal
                // (quotes, backslashes, newlines from source escapes), so re-escape it.
                // `sizeof` then still counts the C-decoded byte length, sizing the body
                // and the slice correctly.
                let x = c_string_escape(x);
                format!(
                    "({{ static const struct {{ GcHeader gch; char b[sizeof(\"{x}\")]; }} \
                     __marm_b = {{{{sizeof(\"{x}\"), 0, OBJ_BYTES, MARM_ETERNAL}}, \"{x}\"}}; \
                     static const struct {{ GcHeader gch; Slice s; }} \
                     __marm_s = {{{{sizeof(Slice), 0, OBJ_SLICE, MARM_ETERNAL}}, \
                     {{(void *)__marm_b.b, (const uint8_t *)__marm_b.b, \
                     sizeof(\"{x}\") - 1}}}}; \
                     VObject((void *)&__marm_s.s); }})"
                )
            }
            Literal::Bool(x) => format!("VBool({x})"),
            Literal::Unit => "VUnit()".to_owned(),
            Literal::Char(x) => c_char_literal(*x),
        }
    }

    // `let l = bound in body` is a GCC statement expression: bind a local, then
    // yield the body's value. Only `Local` binders occur here (see closed.rs).
    fn same_place_operand(left: &Expr, right: &Expr) -> bool {
        match (strip_ascription(left), strip_ascription(right)) {
            (Expr::Variable(_, left), Expr::Variable(_, right)) => match (left, right) {
                (Identifier::Local(left), Identifier::Local(right)) => left.0 == right.0,
                (Identifier::Captured(left), Identifier::Captured(right)) => {
                    left.index() == right.index()
                }
                (Identifier::SelfRef, Identifier::SelfRef) => true,
                (Identifier::Global(left), Identifier::Global(right)) => left == right,
                _ => false,
            },
            (Expr::Constant(_, Literal::Int(left)), Expr::Constant(_, Literal::Int(right))) => {
                left == right
            }
            (Expr::Constant(_, Literal::Bool(left)), Expr::Constant(_, Literal::Bool(right))) => {
                left == right
            }
            (Expr::Constant(_, Literal::Unit), Expr::Constant(_, Literal::Unit)) => true,
            (Expr::Project(_, left), Expr::Project(_, right)) => {
                matches!(
                    (&left.select, &right.select),
                    (ProductElement::Ordinal(left), ProductElement::Ordinal(right)) if left == right
                ) && Self::same_place_operand(&left.base, &right.base)
            }
            _ => false,
        }
    }

    fn record_update_from_local<'a>(
        expression: &'a Expr,
        source_level: usize,
    ) -> Option<(&'a ast::RecordUpdate<CaptureInfo, Identifier>, usize)> {
        match strip_ascription(expression) {
            Expr::RecordUpdate(_, update) if matches!(strip_ascription(&update.base), Expr::Variable(_, Identifier::Local(LexicalLevel(level))) if *level == source_level) => {
                Some((update, source_level))
            }
            Expr::Let(_, binding) if matches!(strip_ascription(&binding.bound), Expr::Variable(_, Identifier::Local(LexicalLevel(level))) if *level == source_level) =>
            {
                let Identifier::Local(LexicalLevel(alias)) = binding.binder else {
                    return None;
                };
                Self::record_update_from_local(&binding.body, alias)
            }
            _ => None,
        }
    }

    fn same_place_update<'a>(
        &self,
        body: &'a Expr,
        source_level: usize,
        read_array: &Expr,
        read_index: &Expr,
    ) -> Option<(&'a ast::RecordUpdate<CaptureInfo, Identifier>, usize)> {
        let Expr::Let(_, binding) = strip_ascription(body) else {
            return None;
        };
        let Identifier::Local(LexicalLevel(updated_level)) = binding.binder else {
            return None;
        };
        let (update, update_level) = Self::record_update_from_local(&binding.bound, source_level)?;
        let (write_array, write_index, replacement) = self.raw_array_set_source(&binding.body)?;
        let writes_updated = matches!(
            strip_ascription(replacement),
            Expr::Variable(_, Identifier::Local(LexicalLevel(level))) if *level == updated_level
        );
        (writes_updated
            && Self::same_place_operand(read_array, write_array)
            && Self::same_place_operand(read_index, write_index))
        .then_some((update, update_level))
    }

    /// Recognise the update-and-store pair at the point where it is compiled,
    /// using a packed element place retained by an enclosing raw get. Unlike
    /// `same_place_update`, this does not require the read, update, and write to
    /// be adjacent: a match or conditional may select the branch containing the
    /// update. The pair itself remains adjacent, which keeps evaluation and
    /// control-flow semantics local and obvious.
    fn registered_same_place_update<'a>(
        &self,
        binder: &Identifier,
        bound: &'a Expr,
        body: &'a Expr,
    ) -> Option<(
        ArrayElementPlace,
        &'a ast::RecordUpdate<CaptureInfo, Identifier>,
        usize,
        usize,
    )> {
        let Identifier::Local(LexicalLevel(updated_level)) = binder else {
            return None;
        };
        let (source_level, place, update, update_level) = ARRAY_ELEMENT_PLACES.with(|places| {
            places.borrow().iter().find_map(|(source_level, place)| {
                let (update, update_level) = Self::record_update_from_local(bound, *source_level)?;
                Some((*source_level, place.clone(), update, update_level))
            })
        })?;
        let (write_array, write_index, replacement) = self.raw_array_set_source(body)?;
        let writes_updated = matches!(
            strip_ascription(replacement),
            Expr::Variable(_, Identifier::Local(LexicalLevel(level))) if level == updated_level
        );
        (writes_updated
            && Self::same_place_operand(&place.source_array, write_array)
            && Self::same_place_operand(&place.source_index, write_index))
        .then_some((place, update, update_level, source_level))
    }

    fn record_path_region(
        &self,
        root: &Type,
        indices: &[usize],
    ) -> Option<(usize, Type, RuntimeShape)> {
        let mut current = root.clone();
        let mut offset = 0;
        for index in indices {
            let (next, field_offset) = self.runtime_projection_field_at_fixed_offset(
                &current,
                &ProductElement::Ordinal(*index),
            )?;
            offset += field_offset;
            current = next;
        }
        let shape = self.runtime_shape(&current, &mut Vec::new()).shape;
        Some((offset, current, shape))
    }

    fn record_path_leaf_offset(&self, root: &Type, indices: &[usize]) -> Option<usize> {
        let (offset, _, shape) = self.record_path_region(root, indices)?;
        matches!(shape, RuntimeShape::Leaf).then_some(offset)
    }

    /// Resolve a projection only when every field preceding the selected field
    /// has a statically fixed width. This is deliberately less restrictive than
    /// requiring the whole record to be ground: `{ Length :: Int; Storage :: F a }`
    /// has a fixed offset for `Length` even though the later `Storage` mentions `a`.
    /// Conversely, a field after a naked type parameter remains ineligible because
    /// a caller's layout dictionary may make that parameter wider than one word.
    fn runtime_projection_field_at_fixed_offset(
        &self,
        base_type: &Type,
        selector: &ProductElement,
    ) -> Option<(Type, usize)> {
        if let Type::Tuple(tuple) = base_type {
            let ProductElement::Ordinal(index) = selector else {
                return None;
            };
            let selected = tuple.elements().get(*index)?.clone();
            let mut offset = 0;
            for field in &tuple.elements()[..*index] {
                if !field.variables().is_empty() {
                    return None;
                }
                offset += self
                    .runtime_shape(field, &mut Vec::new())
                    .shape
                    .stored_words();
            }
            return Some((selected, offset));
        }

        let (name, arguments) = match base_type {
            Type::Constructor(name) => (name, Vec::new()),
            Type::Apply { .. } => applied_type(base_type)?,
            _ => return None,
        };
        let TypeDefinition::Record(record) = self.type_definitions.get(name)? else {
            return None;
        };
        let bindings = record
            .type_parameters
            .iter()
            .zip(arguments)
            .map(|(parameter, argument)| (parameter.name.clone(), argument))
            .collect::<HashMap<_, _>>();
        let mut fields = record.fields.iter().collect::<Vec<_>>();
        fields.sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name));
        let index = match selector {
            ProductElement::Ordinal(index) => *index,
            ProductElement::Name(name) => fields.iter().position(|field| &field.name == name)?,
        };
        let selected =
            instantiate_type_expression(&fields.get(index)?.type_signature.body, &bindings)?;
        let mut offset = 0;
        for field in &fields[..index] {
            let ty = instantiate_type_expression(&field.type_signature.body, &bindings)?;
            if !ty.variables().is_empty() {
                return None;
            }
            offset += self
                .runtime_shape(&ty, &mut Vec::new())
                .shape
                .stored_words();
        }
        Some((selected, offset))
    }

    fn compile_same_place_record_update(
        &self,
        level: usize,
        array: &Expr,
        index: &Expr,
        element_type: Type,
        update: &ast::RecordUpdate<CaptureInfo, Identifier>,
        code: &mut CodeBuffer,
    ) -> Option<fmt::Result> {
        let update_type = update.base.annotation().type_info.inferred_type.clone();
        // Prefer the concrete type recovered at the update site. The raw-get
        // annotation can still name a polymorphic wrapper even after layout
        // specialization has fixed the element representation at this call.
        let candidates = if update_type.variables().is_empty() {
            [update_type, element_type]
        } else {
            [element_type, update_type]
        };
        let (element_type, regions) = candidates.into_iter().find_map(|candidate| {
            let regions = update
                .fields
                .iter()
                .map(|field| self.record_path_region(&candidate, &field.indices))
                .collect::<Option<Vec<_>>>()?;
            Some((candidate, regions))
        })?;
        let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
        let array_local = format!("_pa{id}");
        let index_local = format!("_pi{id}");

        // Plan every replacement before touching the output buffer. A structural
        // aggregate is split into leaves; an opaque aggregate is evaluated once
        // and projected. If a sum cannot be split safely, decline the fusion with
        // no partially-emitted C and let the ordinary whole-value path handle it.
        let previous = ARRAY_ELEMENT_PLACES.with(|places| {
            places.borrow_mut().insert(
                level,
                ArrayElementPlace {
                    array: array_local.clone(),
                    index: index_local.clone(),
                    element_type: element_type.clone(),
                    source_array: array.clone(),
                    source_index: index.clone(),
                },
            )
        });
        let plans = update
            .fields
            .iter()
            .zip(&regions)
            .map(|(field, (offset, selected_type, shape))| {
                let mut prelude = Vec::new();
                let leaves = self.literal_shape_leaves(&field.value, shape, &mut prelude)?;
                Some((
                    *offset,
                    self.packed_type_is_immediate(selected_type),
                    prelude,
                    leaves,
                ))
            })
            .collect::<Option<Vec<_>>>();
        ARRAY_ELEMENT_PLACES.with(|places| {
            let mut places = places.borrow_mut();
            if let Some(previous) = previous {
                places.insert(level, previous);
            } else {
                places.remove(&level);
            }
        });
        let plans = plans?;

        let result = (|| {
            write!(code, "({{ Value {array_local} = ")?;
            self.compile_expr(array, code)?;
            write!(code, "; Value {index_local} = ")?;
            self.compile_expr(index, code)?;
            write!(code, "; ")?;

            let mut stores = Vec::new();
            for (field_index, (offset, immediate, prelude, leaves)) in plans.iter().enumerate() {
                for binding in prelude {
                    write!(code, "{binding} ")?;
                }
                for (leaf_index, leaf) in leaves.iter().enumerate() {
                    let temp = format!("_pv{id}_{field_index}_{leaf_index}");
                    write!(code, "Value {temp} = {leaf}; ")?;
                    stores.push((offset + leaf_index, temp, *immediate));
                }
            }
            for (offset, temp, immediate) in stores {
                let setter = if immediate {
                    "flat_array_set_word_immediate"
                } else {
                    "flat_array_set_word"
                };
                write!(
                    code,
                    "{setter}({array_local}, (size_t)as_int({index_local}), {offset}, {temp}); "
                )?;
            }
            write!(code, "VUnit(); }})")
        })();
        Some(result)
    }

    fn flat_record_literal<'a>(
        &self,
        bound: &'a Expr,
    ) -> Option<(Vec<(usize, &'a Expr)>, Vec<String>, Vec<String>)> {
        let mut bindings = Vec::new();
        let mut value = strip_ascription(bound);
        while let Expr::Let(_, binding) = value {
            let Identifier::Local(LexicalLevel(level)) = &binding.binder else {
                return None;
            };
            bindings.push((*level, binding.bound.as_ref()));
            value = strip_ascription(&binding.body);
        }
        if !matches!(value, Expr::Record(..)) {
            return None;
        }

        // Let-floating deliberately preserves wrapper annotations, which can
        // describe an intermediate value. The terminal record node is the
        // representation being constructed and is therefore authoritative.
        let ty = &value.annotation().type_info.inferred_type;
        let width = self.flat_record_width(ty);
        if width == 1 {
            return None;
        }
        let shape = self.runtime_shape(ty, &mut Vec::new()).shape;
        let mut prelude = Vec::new();
        let leaves = self.literal_shape_leaves(value, &shape, &mut prelude)?;
        (leaves.len() == width).then_some((bindings, prelude, leaves))
    }

    fn emit_flat_local(
        &self,
        id: usize,
        bindings: &[(usize, &Expr)],
        prelude: &[String],
        leaves: &[String],
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        write!(
            code,
            "volatile Value _fv{id}[{}] = {{0}}; {{ ",
            leaves.len()
        )?;
        for (level, bound) in bindings {
            write!(code, "Value l{level} = ")?;
            self.compile_expr(bound, code)?;
            write!(code, "; ")?;
        }
        for binding in prelude {
            write!(code, "{binding} ")?;
        }
        for (word, leaf) in leaves.iter().enumerate() {
            write!(code, "_fv{id}[{word}] = {leaf}; ")?;
        }
        write!(code, "}} ")
    }

    fn install_flat_local(level: usize, words: Vec<String>) -> Option<FlatValuePlace> {
        FLAT_VALUE_PLACES.with(|places| places.borrow_mut().insert(level, FlatValuePlace { words }))
    }

    fn restore_flat_local(level: usize, previous: Option<FlatValuePlace>) {
        FLAT_VALUE_PLACES.with(|places| {
            let mut places = places.borrow_mut();
            if let Some(previous) = previous {
                places.insert(level, previous);
            } else {
                places.remove(&level);
            }
        });
    }

    fn compile_let(
        &self,
        Binding {
            binder,
            bound,
            body,
            ..
        }: &phase::Binding<Closed>,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        let Identifier::Local(LexicalLevel(level)) = binder else {
            panic!("let binder is always a local: {binder:?}");
        };

        if direct_array_enabled()
            && let Some((place, update, update_level, _source_level)) =
                self.registered_same_place_update(binder, bound, body)
        {
            let mut fused = CodeBuffer::default();
            if let Some(result) = self.compile_same_place_record_update(
                update_level,
                &place.source_array,
                &place.source_index,
                place.element_type,
                update,
                &mut fused,
            ) {
                result?;
                return write!(code, "{fused}");
            }
        }

        if let Some(words) = self.flat_words_for(bound)
            && words.len() == self.flat_record_width(&bound.annotation().type_info.inferred_type)
        {
            let previous = Self::install_flat_local(*level, words);
            let result = self.compile_expr(body, code);
            Self::restore_flat_local(*level, previous);
            return result;
        }

        if let Some((bindings, prelude, leaves)) = self.flat_record_literal(bound) {
            let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
            write!(code, "({{ ")?;
            self.emit_flat_local(id, &bindings, &prelude, &leaves, code)?;
            let words = (0..leaves.len())
                .map(|word| format!("_fv{id}[{word}]"))
                .collect();
            let previous = Self::install_flat_local(*level, words);
            let result = self.compile_expr(body, code);
            Self::restore_flat_local(*level, previous);
            result?;
            return write!(code, "; }})");
        }

        // Lazy packed-element binding: when every use of the result of an
        // unchecked array read is a scalar projection, retain `(array,index)` as
        // a place and compile those projections to direct word loads. The
        // canonical aggregate is never rebuilt. Both operands are still
        // evaluated exactly once, in source order, before the body.
        let raw_array_source = direct_array_enabled()
            .then(|| self.raw_array_get_source(bound))
            .flatten();
        if let Some((array, index, source_type)) = raw_array_source {
            let annotated = &bound.annotation().type_info.inferred_type;
            let element_type = if source_type.variables().is_empty() {
                source_type.clone()
            } else if annotated.variables().is_empty() {
                annotated.clone()
            } else if let Some(concrete) = Self::concrete_local_type(body, *level) {
                concrete
            } else {
                source_type.clone()
            };
            if let Some((update, update_level)) = self.same_place_update(body, *level, array, index)
                && let Some(result) = self.compile_same_place_record_update(
                    update_level,
                    array,
                    index,
                    element_type.clone(),
                    update,
                    code,
                )
            {
                return result;
            }
            // Register a provisional place while checking the body: pattern
            // eligibility itself resolves local-rooted deconstruct scrutinees
            // through this map.  Restore an outer entry before emitting code.
            let previous = ARRAY_ELEMENT_PLACES.with(|places| {
                places.borrow_mut().insert(
                    *level,
                    ArrayElementPlace {
                        array: String::new(),
                        index: String::new(),
                        element_type: element_type.clone(),
                        source_array: array.clone(),
                        source_index: index.clone(),
                    },
                )
            });
            let supported = self.local_uses_are_flat_array_leaves(body, *level, &element_type);
            ARRAY_ELEMENT_PLACES.with(|places| {
                let mut places = places.borrow_mut();
                if let Some(previous) = previous {
                    places.insert(*level, previous);
                } else {
                    places.remove(level);
                }
            });

            if supported {
                let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
                let array_local = format!("_fa{id}");
                let index_local = format!("_fi{id}");
                write!(code, "({{ Value {array_local} = ")?;
                self.compile_expr(array, code)?;
                write!(code, "; Value {index_local} = ")?;
                self.compile_expr(index, code)?;
                write!(code, "; ")?;
                let previous = ARRAY_ELEMENT_PLACES.with(|places| {
                    places.borrow_mut().insert(
                        *level,
                        ArrayElementPlace {
                            array: array_local,
                            index: index_local,
                            element_type,
                            source_array: array.clone(),
                            source_index: index.clone(),
                        },
                    )
                });
                self.compile_expr(body, code)?;
                ARRAY_ELEMENT_PLACES.with(|places| {
                    let mut places = places.borrow_mut();
                    if let Some(previous) = previous {
                        places.insert(*level, previous);
                    } else {
                        places.remove(level);
                    }
                });
                return write!(code, "; }})");
            }
        }

        write!(code, "({{ Value l{level} = ")?;
        self.compile_expr(bound, code)?;
        write!(code, "; ")?;
        self.compile_expr(body, code)?;
        write!(code, "; }})")
    }

    // -------------------------------------------------------- self-tail loops
    // clang's tail-call optimisation is best-effort and does NOT fire reliably
    // for a self-call nested in a branch/ternary -- it stays a real `bl`, so a
    // deeply self-recursive worker overflows the stack. When a worker tail-calls
    // itself we instead emit its body as `for (;;) { ... }` and rewrite each
    // self-tail-call to "reassign the parameters, then `continue`" -- constant
    // stack, guaranteed, no reliance on the C compiler.

    // Whether `expr`, in tail position, is a saturated self-call to `worker`
    // (which has `arity` parameters) -- the shape that becomes a loop back-edge.
    fn is_self_call(&self, target: SelfCall, arity: usize, expr: &Expr) -> bool {
        let mut count = 0usize;
        let mut head: &Expr = expr;
        while let Expr::Apply(_, inner) = head {
            count += 1;
            head = &inner.function;
        }
        count == arity
            && match target {
                SelfCall::Named(name) => {
                    matches!(head, Expr::Variable(_, Identifier::Global(qn)) if qn.as_ref() == name)
                }
                // A lifted (recursive) lambda calls itself through `self`, the closure
                // it was invoked with; the captures in `self` are loop-invariant, so a
                // saturated tail `self`-call is a genuine loop back-edge.
                SelfCall::SelfRef => matches!(head, Expr::Variable(_, Identifier::SelfRef)),
            }
    }

    // Whether any tail position of `expr` is a self-call -- i.e. whether this
    // worker needs the loop wrapper. Mirrors the tail structure `compile_tail`
    // walks, so the two agree on exactly which positions are tail positions.
    fn has_tail_self_call(&self, target: SelfCall, arity: usize, expr: &Expr) -> bool {
        match expr {
            Expr::Ascription(_, the) => self.has_tail_self_call(target, arity, &the.ascribed_tree),
            Expr::If(_, the) => {
                self.has_tail_self_call(target, arity, &the.consequent)
                    || self.has_tail_self_call(target, arity, &the.alternate)
            }
            Expr::Let(_, the) => self.has_tail_self_call(target, arity, &the.body),
            Expr::Sequence(_, the) => self.has_tail_self_call(target, arity, &the.and_then),
            Expr::Deconstruct(_, the) => the
                .match_clauses
                .iter()
                .any(|clause| self.has_tail_self_call(target, arity, &clause.consequent)),
            _ => self.is_self_call(target, arity, expr),
        }
    }

    // Emit `expr` in tail position as C statements. A saturated self-call becomes
    // the loop back-edge (evaluate the new arguments into temporaries -- they
    // read the *current* frame -- then overwrite the parameters `l0..l{arity-1}`
    // and `continue`); every other tail value becomes `return <expr>;`.
    fn compile_tail(
        &self,
        target: SelfCall,
        arity: usize,
        expr: &Expr,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        match expr {
            Expr::Ascription(_, the) => self.compile_tail(target, arity, &the.ascribed_tree, code),

            Expr::If(_, the) => {
                write!(code, "if (as_bool(")?;
                self.compile_expr(&the.predicate, code)?;
                write!(code, ")) {{ ")?;
                self.compile_tail(target, arity, &the.consequent, code)?;
                write!(code, " }} else {{ ")?;
                self.compile_tail(target, arity, &the.alternate, code)?;
                write!(code, " }}")
            }

            Expr::Let(_, the) => {
                let Identifier::Local(LexicalLevel(level)) = &the.binder else {
                    panic!("let binder is always a local: {:?}", the.binder);
                };
                if direct_array_enabled()
                    && let Some((place, update, update_level, _source_level)) =
                        self.registered_same_place_update(&the.binder, &the.bound, &the.body)
                {
                    let mut fused = CodeBuffer::default();
                    if let Some(result) = self.compile_same_place_record_update(
                        update_level,
                        &place.source_array,
                        &place.source_index,
                        place.element_type,
                        update,
                        &mut fused,
                    ) {
                        result?;
                        return write!(code, "return {fused};");
                    }
                }
                if let Some(words) = self.flat_words_for(&the.bound)
                    && words.len()
                        == self.flat_record_width(&the.bound.annotation().type_info.inferred_type)
                {
                    let previous = Self::install_flat_local(*level, words);
                    let result = self.compile_tail(target, arity, &the.body, code);
                    Self::restore_flat_local(*level, previous);
                    return result;
                }
                if let Some((bindings, prelude, leaves)) = self.flat_record_literal(&the.bound) {
                    let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
                    self.emit_flat_local(id, &bindings, &prelude, &leaves, code)?;
                    let words = (0..leaves.len())
                        .map(|word| format!("_fv{id}[{word}]"))
                        .collect();
                    let previous = Self::install_flat_local(*level, words);
                    let result = self.compile_tail(target, arity, &the.body, code);
                    Self::restore_flat_local(*level, previous);
                    return result;
                }
                if direct_array_enabled()
                    && let Some((array, index, source_type)) = self.raw_array_get_source(&the.bound)
                {
                    let annotated = &the.bound.annotation().type_info.inferred_type;
                    let element_type = if source_type.variables().is_empty() {
                        source_type.clone()
                    } else if annotated.variables().is_empty() {
                        annotated.clone()
                    } else if let Some(concrete) = Self::concrete_local_type(&the.body, *level) {
                        concrete
                    } else {
                        source_type.clone()
                    };
                    if let Some((update, update_level)) =
                        self.same_place_update(&the.body, *level, array, index)
                        && update.fields.iter().all(|field| {
                            self.record_path_leaf_offset(&element_type, &field.indices)
                                .is_some()
                        })
                    {
                        write!(code, "return ")?;
                        self.compile_same_place_record_update(
                            update_level,
                            array,
                            index,
                            element_type.clone(),
                            update,
                            code,
                        )
                        .expect("prevalidated same-place record update")?;
                        return write!(code, ";");
                    }
                    let previous = ARRAY_ELEMENT_PLACES.with(|places| {
                        places.borrow_mut().insert(
                            *level,
                            ArrayElementPlace {
                                array: String::new(),
                                index: String::new(),
                                element_type: element_type.clone(),
                                source_array: array.clone(),
                                source_index: index.clone(),
                            },
                        )
                    });
                    let supported =
                        self.local_uses_are_flat_array_leaves(&the.body, *level, &element_type);
                    ARRAY_ELEMENT_PLACES.with(|places| {
                        let mut places = places.borrow_mut();
                        if let Some(previous) = previous {
                            places.insert(*level, previous);
                        } else {
                            places.remove(level);
                        }
                    });
                    if supported {
                        let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
                        let array_local = format!("_fa{id}");
                        let index_local = format!("_fi{id}");
                        write!(code, "Value {array_local} = ")?;
                        self.compile_expr(array, code)?;
                        write!(code, "; Value {index_local} = ")?;
                        self.compile_expr(index, code)?;
                        write!(code, "; ")?;
                        let previous = ARRAY_ELEMENT_PLACES.with(|places| {
                            places.borrow_mut().insert(
                                *level,
                                ArrayElementPlace {
                                    array: array_local,
                                    index: index_local,
                                    element_type,
                                    source_array: array.clone(),
                                    source_index: index.clone(),
                                },
                            )
                        });
                        let result = self.compile_tail(target, arity, &the.body, code);
                        ARRAY_ELEMENT_PLACES.with(|places| {
                            let mut places = places.borrow_mut();
                            if let Some(previous) = previous {
                                places.insert(*level, previous);
                            } else {
                                places.remove(level);
                            }
                        });
                        return result;
                    }
                }
                write!(code, "Value l{level} = ")?;
                self.compile_expr(&the.bound, code)?;
                write!(code, "; ")?;
                self.compile_tail(target, arity, &the.body, code)
            }

            Expr::Sequence(_, the) => {
                write!(code, "(void)(")?;
                self.compile_expr(&the.this, code)?;
                write!(code, "); ")?;
                self.compile_tail(target, arity, &the.and_then, code)
            }

            Expr::Deconstruct(_, the) => {
                let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);

                // Tail-position counterpart of `compile_deconstruct`'s packed
                // array path. Recursive probe loops commonly match a field of
                // the retained element place before either updating that same
                // slot or continuing; rebuilding the whole element here would
                // defeat both the direct read and the branch-local write.
                if direct_array_enabled()
                    && let Some((array, index, offset, element_type, fallback_shape)) =
                        self.flat_array_region(&the.scrutinee)
                    && element_type.variables().is_empty()
                    && let Some(shape) = self.array_match_shape(&the.match_clauses, &fallback_shape)
                {
                    let array_local = format!("_tma{id}");
                    let index_local = format!("_tmi{id}");
                    write!(
                        code,
                        "{{ Value {array_local} = {array}; Value {index_local} = {index}; "
                    )?;
                    let mut first = true;
                    let mut exhaustive = false;
                    for clause in &the.match_clauses {
                        let mut tests = Vec::new();
                        let mut binds = Vec::new();
                        let supported = self.collect_array_pattern(
                            &clause.pattern,
                            &array_local,
                            &index_local,
                            offset,
                            &shape,
                            &mut tests,
                            &mut binds,
                        );
                        debug_assert!(supported);
                        if !first {
                            write!(code, " else ")?;
                        }
                        first = false;
                        if tests.is_empty() {
                            write!(code, "{{ ")?;
                            exhaustive = true;
                        } else {
                            write!(code, "if ({}) {{ ", tests.join(" && "))?;
                        }
                        for (level, path) in &binds {
                            write!(code, "Value l{level} = {path}; ")?;
                        }
                        self.compile_tail(target, arity, &clause.consequent, code)?;
                        write!(code, " }}")?;
                        if exhaustive {
                            break;
                        }
                    }
                    if !exhaustive {
                        write!(code, " else {{ match_fail(); }}")?;
                    }
                    return write!(code, " }}");
                }

                let scrutinee = format!("_scrut{id}");
                write!(code, "{{ Value {scrutinee} = ")?;
                self.compile_expr(&the.scrutinee, code)?;
                write!(code, "; ")?;
                let mut first = true;
                let mut exhaustive = false;
                for clause in &the.match_clauses {
                    let mut tests = Vec::new();
                    let mut binds = Vec::new();
                    if self.flat_records_enabled() {
                        self.collect_pattern_flat(
                            &clause.pattern,
                            &scrutinee,
                            0,
                            1,
                            true,
                            &mut tests,
                            &mut binds,
                        );
                    } else {
                        self.collect_pattern(&clause.pattern, &scrutinee, &mut tests, &mut binds);
                    }
                    if !first {
                        write!(code, " else ")?;
                    }
                    first = false;
                    if tests.is_empty() {
                        write!(code, "{{ ")?;
                        exhaustive = true;
                    } else {
                        write!(code, "if ({}) {{ ", tests.join(" && "))?;
                    }
                    for (level, path) in &binds {
                        write!(code, "Value l{level} = {path}; ")?;
                    }
                    self.compile_tail(target, arity, &clause.consequent, code)?;
                    write!(code, " }}")?;
                    if exhaustive {
                        break;
                    }
                }
                if !exhaustive {
                    write!(code, " else {{ match_fail(); }}")?;
                }
                write!(code, " }}")
            }

            _ if self.is_self_call(target, arity, expr) => {
                let mut args: Vec<&Expr> = Vec::new();
                let mut head: &Expr = expr;
                while let Expr::Apply(_, inner) = head {
                    args.push(&inner.argument);
                    head = &inner.function;
                }
                args.reverse();
                let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
                write!(code, "{{ ")?;
                for (i, arg) in args.iter().enumerate() {
                    write!(code, "Value _a{id}_{i} = ")?;
                    self.compile_expr(arg, code)?;
                    write!(code, "; ")?;
                }
                for i in 0..arity {
                    write!(code, "l{i} = _a{id}_{i}; ")?;
                }
                write!(code, "continue; }}")
            }

            _ => {
                write!(code, "return ")?;
                self.compile_expr(expr, code)?;
                write!(code, ";")
            }
        }
    }
}
