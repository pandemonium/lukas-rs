use fmt::Write;
use std::cell::RefCell;
use std::rc::Rc;
use std::{collections::HashMap, fmt, fs, io, path};

use std::sync::atomic::{AtomicUsize, Ordering};

use crate::{
    ast::{
        BUILTIN_MODULE_NAME, Binding, Literal, ProductElement, STDLIB_MODULE_NAME, Segment,
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
}

thread_local! {
    /// Lexical locals whose value is represented by a packed array element rather
    /// than an eagerly rebuilt canonical object. Entries are scoped by
    /// `compile_let`; code generation itself is single-threaded.
    static ARRAY_ELEMENT_PLACES: RefCell<HashMap<usize, ArrayElementPlace>> =
        RefCell::new(HashMap::new());
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
// with `_`. The lexer restricts identifiers to alphanumerics and `_`, and
// operators reach `c_name` only as builtins (named via `map_builtin_name`), so
// the join is already a valid C identifier.
fn surface_name(q: &QualifiedName) -> String {
    let mut parts = Vec::with_capacity(2 + q.module.tail.len());
    parts.push(q.module.head.clone());
    parts.extend_from_slice(q.module.tail.as_slice());
    parts.push(q.member.as_str().to_owned());
    parts.join("_")
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
        "prim_show" => ("prim_show", 1),
        "print_endline" => ("prim_print_endline", 1),
        _otherwise => return None,
    })
}

// The monomorphic `prim_show` leaf for `arg`'s static type. `prim_show` is only ever
// applied at a primitive (leaf) type -- the `Display` witnesses for compound types
// recurse through `display`, never calling `prim_show` on a tuple/constructor -- so a
// non-leaf here is a compiler invariant break.
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

        for LiftedFunction { name, code, .. } in &self.functions {
            tracing::trace!("generate_code: {name}");
            writeln!(out, "Value {}(Value self, Value l0) {{", c_name(name))?;
            writeln!(out, "  (void)self; (void)l0;")?;
            write!(out, "  return ")?;
            self.compile_expr(code, out)?;
            writeln!(out, ";\n}}\n")?;
        }

        // Uncurried workers: an N-ary function whose parameters are the flat frame
        // `l0..l{N-1}`. No `self` -- these are closure-free, so their bodies carry
        // no captures. `compile_apply` calls them directly at saturated call sites.
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
            if loopify && self.has_tail_self_call(name, *params, body) {
                write!(out, "\n  for (;;) {{ ")?;
                self.compile_tail(name, *params, body, out)?;
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
            writeln!(
                out,
                "Value {}_uworker(Value self, Value *args) {{",
                c_name(head)
            )?;
            write!(out, "  (void)self;")?;
            for i in 0..*arity {
                write!(out, " Value l{i} = args[{i}];")?;
            }
            write!(out, "\n  return ")?;
            self.compile_expr(body, out)?;
            writeln!(out, ";\n}}\n")?;
        }

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
            Expr::Apply(_, the) => self.compile_apply(the, code),
            Expr::Let(_, the) => self.compile_let(the, code),
            Expr::Tuple(_, the) => self.compile_tuple(&the.elements, code),
            Expr::Record(a, the) => self.compile_record(a, the, code),
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

    fn runtime_shape(&self, ty: &Type, on_path: &mut Vec<QualifiedName>) -> ShapeResult {
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
            Type::Variable(..)
            | Type::Base(..)
            | Type::Arrow { .. }
            | Type::Record(..)
            | Type::Coproduct(..)
            | Type::Array(..) => ShapeResult {
                shape: RuntimeShape::Leaf,
                reaches_enclosing_type: false,
            },
        }
    }

    fn runtime_named_shape(
        &self,
        name: &QualifiedName,
        arguments: &[Type],
        on_path: &mut Vec<QualifiedName>,
    ) -> ShapeResult {
        if on_path.contains(name) {
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

        on_path.push(name.clone());
        let result = match definition {
            TypeDefinition::Record(record) => {
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
        on_path: &mut Vec<QualifiedName>,
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
        match ty {
            Type::Constructor(name) => self.record_layouts.get(name).cloned(),
            Type::Tuple(tuple) => Some(tuple.0.iter().map(|t| self.flat_width(t)).collect()),
            _ => None,
        }
    }

    // The flattened width of `ty` as a single field: its inlined width if that is
    // in `1..=FLAT_INLINE_CAP`, else one pointer word. Matches `type_expr_width`
    // in lambda_lift, so codegen and the layout table agree.
    fn flat_width(&self, ty: &Type) -> usize {
        match self.flat_widths(ty) {
            Some(widths) => {
                let total: usize = widths.iter().sum();
                if (1..=FLAT_INLINE_CAP).contains(&total) {
                    total
                } else {
                    1
                }
            }
            None => 1,
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

    // Compile a sub-expression to a standalone C string (for splicing into an
    // argument list where a `CodeBuffer` write cannot reach).
    fn compile_to_string(&self, expr: &Expr) -> String {
        let mut buf = CodeBuffer::default();
        let _ = self.compile_expr(expr, &mut buf);
        buf.to_string()
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
        if width == 1 {
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
            RuntimeShape::Sum { .. } => {}
        }
    }

    fn literal_shape_leaves(
        &self,
        value: &Expr,
        shape: &RuntimeShape,
        prelude: &mut Vec<String>,
    ) -> Option<Vec<String>> {
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
        match base_type {
            Type::Constructor(_) => Some((self.compile_to_string(&projection.base), offset, width)),
            _ => None,
        }
    }

    /// Recognise a projection chain rooted at
    /// `Mutable_Array.raw_get_unchecked array index` and resolve its final scalar
    /// leaf to an offset in the packed element. This skips `flat_array_get`'s
    /// canonical aggregate rebuild entirely. The fast path is deliberately leaf-
    /// only; a projected aggregate still needs ordinary copy-out semantics.
    fn flat_array_leaf_place(
        &self,
        projection: &phase::Projection<Closed>,
    ) -> Option<(String, String, usize)> {
        let (array, index, offset, _ty, shape) =
            self.flat_array_region(&Expr::Project(CaptureInfo::dummy(), projection.clone()))?;
        matches!(shape, RuntimeShape::Leaf).then_some((array, index, offset))
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
                if annotated.variables().is_empty() {
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
        if let Some(arguments) = raw_array_get_arguments(expression) {
            return Some((
                arguments.0,
                arguments.1,
                &expression.annotation().type_info.inferred_type,
            ));
        }
        let Expr::Deconstruct(_, deconstruct) = strip_ascription(expression) else {
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
                if !self.newtype_constructors.contains(name.as_ref()) {
                    return None;
                }
                let [Pattern::Bind(_, Identifier::Local(level))] = constructor.arguments.as_slice()
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
        Some((&deconstruct.scrutinee, index, element_type))
    }

    fn local_uses_are_flat_array_leaves(
        &self,
        expression: &Expr,
        level: usize,
        element_type: &Type,
    ) -> bool {
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
            if let Some((_array, _index, _offset, _ty, shape)) =
                self.flat_array_region(&deconstruct.scrutinee)
            {
                if self
                    .array_match_shape(&deconstruct.match_clauses, &shape)
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
                let RuntimeShape::Sum { variants, .. } = shape else {
                    return false;
                };
                let Some(tag) = self.constructor_tags.get(name.as_ref()) else {
                    return false;
                };
                let Some(fields) = variants.get(*tag as usize) else {
                    return false;
                };
                constructor.arguments.len() == fields.len()
                    && constructor
                        .arguments
                        .iter()
                        .zip(fields)
                        .all(|(pattern, shape)| self.array_pattern_supported(pattern, shape))
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
                let RuntimeShape::Sum { variants, .. } = shape else {
                    return false;
                };
                let Some(&tag) = self.constructor_tags.get(name.as_ref()) else {
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
                    format!("proj({base}, {offset})")
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
            if direct_array_enabled()
                && let Some((array, index, offset)) = self.flat_array_leaf_place(the)
            {
                return write!(
                    code,
                    "flat_array_get_word({array}, (size_t)as_int({index}), {offset})"
                );
            }
            if let Some((base, offset, width)) = self.flat_place(the) {
                if width == 1 {
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
            && let Some((array, index, offset, _ty, fallback_shape)) =
                self.flat_array_region(&the.scrutinee)
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
            if let Some(shape) = self.array_match_shape(&the.match_clauses, &fallback_shape) {
                let array_local = format!("_ma{id}");
                let index_local = format!("_mi{id}");
                write!(
                    code,
                    "({{ Value {array_local} = {array}; Value {index_local} = {index}; "
                )?;

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

        // A multiword sum projected out of a flat record is already a readable
        // region (tag followed by payload words).  If it is consumed immediately
        // by a constructor match, inspect that region directly instead of calling
        // `mk_data_inline` merely so `data_tag`/`data_field` can unpack it again.
        if let Expr::Project(_, projection) = strip_ascription(&the.scrutinee) {
            if let Some((base, offset, width)) = self.flat_place(projection) {
                if width > 1
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
    fn compile_apply(&self, the: &phase::Apply<Closed>, code: &mut CodeBuffer) -> fmt::Result {
        // Flatten the application spine into (head, args-in-order).
        let mut args: Vec<&Expr> = vec![&the.argument];
        let mut head: &Expr = &the.function;
        while let Expr::Apply(_, inner) = head {
            args.push(&inner.argument);
            head = &inner.function;
        }
        args.reverse();

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
                } else if matches!(
                    args[0].annotation().type_info.inferred_type,
                    Type::Base(BaseType::Float)
                ) {
                    // A Float-typed operand routes the arithmetic/ordering op to its
                    // boxed-double prim; everything else keeps the int/generic prim.
                    float_prim(prim).unwrap_or(prim)
                } else {
                    prim
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
        let n = env.elements.len();
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
        if n == 0 {
            return write!(code, "STATIC_CLOSURE0({name}, {worker}, {arity})");
        }
        // Per-site static descriptor, then a heap {desc, captures}. Statement-expression
        // scoping keeps each site's `__d` local, so `&__d` binds to this site's descriptor
        // even when a captured expression is itself a closure with its own `__d`.
        write!(
            code,
            "({{ static const ClosureDesc __d = {{{name}, {worker}, {arity}}}; "
        )?;
        if n <= 4 {
            write!(code, "mk_closure_d{n}(&__d")?;
        } else {
            write!(code, "mk_closure_dn(&__d, {n}")?;
        }
        for element in &env.elements {
            write!(code, ", ")?;
            self.compile_expr(element, code)?;
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
            Identifier::Local(LexicalLevel(level)) => format!("l{level}"),
            Identifier::Captured(capture) => format!("env_get(self, {})", capture.index()),
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
            Literal::Text(x) => format!(
                "({{ static const struct {{ GcHeader gch; char b[sizeof(\"{x}\")]; }} \
                 __marm_b = {{{{sizeof(\"{x}\"), 0, OBJ_BYTES, MARM_ETERNAL}}, \"{x}\"}}; \
                 static const struct {{ GcHeader gch; Slice s; }} \
                 __marm_s = {{{{sizeof(Slice), 0, OBJ_SLICE, MARM_ETERNAL}}, \
                 {{(void *)__marm_b.b, 0, sizeof(\"{x}\") - 1}}}}; \
                 VObject((void *)&__marm_s.s); }})"
            ),
            Literal::Bool(x) => format!("VBool({x})"),
            Literal::Unit => "VUnit()".to_owned(),
            Literal::Char(x) => format!("VChar('{x}')"),
        }
    }

    // `let l = bound in body` is a GCC statement expression: bind a local, then
    // yield the body's value. Only `Local` binders occur here (see closed.rs).
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
            let element_type = if annotated.variables().is_empty() {
                annotated.clone()
            } else {
                source_type.clone()
            };
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
    fn is_self_call(&self, worker: &QualifiedName, arity: usize, expr: &Expr) -> bool {
        let mut count = 0usize;
        let mut head: &Expr = expr;
        while let Expr::Apply(_, inner) = head {
            count += 1;
            head = &inner.function;
        }
        count == arity
            && matches!(head, Expr::Variable(_, Identifier::Global(qn)) if qn.as_ref() == worker)
    }

    // Whether any tail position of `expr` is a self-call -- i.e. whether this
    // worker needs the loop wrapper. Mirrors the tail structure `compile_tail`
    // walks, so the two agree on exactly which positions are tail positions.
    fn has_tail_self_call(&self, worker: &QualifiedName, arity: usize, expr: &Expr) -> bool {
        match expr {
            Expr::Ascription(_, the) => self.has_tail_self_call(worker, arity, &the.ascribed_tree),
            Expr::If(_, the) => {
                self.has_tail_self_call(worker, arity, &the.consequent)
                    || self.has_tail_self_call(worker, arity, &the.alternate)
            }
            Expr::Let(_, the) => self.has_tail_self_call(worker, arity, &the.body),
            Expr::Sequence(_, the) => self.has_tail_self_call(worker, arity, &the.and_then),
            Expr::Deconstruct(_, the) => the
                .match_clauses
                .iter()
                .any(|clause| self.has_tail_self_call(worker, arity, &clause.consequent)),
            _ => self.is_self_call(worker, arity, expr),
        }
    }

    // Emit `expr` in tail position as C statements. A saturated self-call becomes
    // the loop back-edge (evaluate the new arguments into temporaries -- they
    // read the *current* frame -- then overwrite the parameters `l0..l{arity-1}`
    // and `continue`); every other tail value becomes `return <expr>;`.
    fn compile_tail(
        &self,
        worker: &QualifiedName,
        arity: usize,
        expr: &Expr,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        match expr {
            Expr::Ascription(_, the) => self.compile_tail(worker, arity, &the.ascribed_tree, code),

            Expr::If(_, the) => {
                write!(code, "if (as_bool(")?;
                self.compile_expr(&the.predicate, code)?;
                write!(code, ")) {{ ")?;
                self.compile_tail(worker, arity, &the.consequent, code)?;
                write!(code, " }} else {{ ")?;
                self.compile_tail(worker, arity, &the.alternate, code)?;
                write!(code, " }}")
            }

            Expr::Let(_, the) => {
                let Identifier::Local(LexicalLevel(level)) = &the.binder else {
                    panic!("let binder is always a local: {:?}", the.binder);
                };
                if direct_array_enabled()
                    && let Some((array, index, source_type)) = self.raw_array_get_source(&the.bound)
                {
                    let annotated = &the.bound.annotation().type_info.inferred_type;
                    let element_type = if annotated.variables().is_empty() {
                        annotated.clone()
                    } else {
                        source_type.clone()
                    };
                    let previous = ARRAY_ELEMENT_PLACES.with(|places| {
                        places.borrow_mut().insert(
                            *level,
                            ArrayElementPlace {
                                array: String::new(),
                                index: String::new(),
                                element_type: element_type.clone(),
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
                                },
                            )
                        });
                        let result = self.compile_tail(worker, arity, &the.body, code);
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
                self.compile_tail(worker, arity, &the.body, code)
            }

            Expr::Sequence(_, the) => {
                write!(code, "(void)(")?;
                self.compile_expr(&the.this, code)?;
                write!(code, "); ")?;
                self.compile_tail(worker, arity, &the.and_then, code)
            }

            Expr::Deconstruct(_, the) => {
                let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
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
                    self.compile_tail(worker, arity, &clause.consequent, code)?;
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

            _ if self.is_self_call(worker, arity, expr) => {
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
