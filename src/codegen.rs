use fmt::Write;
use std::cell::RefCell;
use std::rc::Rc;
use std::{fmt, fs, io, path};

use crate::hash::{HashMap, HashSet};

use std::sync::atomic::{AtomicUsize, Ordering};

use crate::{
    ast::{
        self, BUILTIN_MODULE_NAME, Binding, Literal, ProductElement, STDLIB_MODULE_NAME, Segment,
        TypeExpression,
        namer::{QualifiedName, TypeDefinition},
        pattern::Pattern,
    },
    closed::{self, CaptureInfo, Closed, Identifier, LexicalLevel},
    intrinsic::{
        AllocationEffect, ControlFlow, IntrinsicOperation, IntrinsicSemantics, IntrinsicType,
        ResultRepresentation, raw_panic_name,
    },
    lambda_lift::{
        self, ChainWorker, ClosureInfo, CoproductLayout, LiftedFunction, TopLevelBinding, Worker,
    },
    phase,
    typer::{BaseType, Type, TypeInfo, memory_layout_evidence_name},
};

/// The C-level entry point required by the environment that will link the
/// generated translation unit. This is narrower than the compiler's execution
/// profile: code generation only needs to know how control enters the program.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum CEntryPoint {
    #[default]
    Process,
    Wasm,
}

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
const C_INLINE_BUDGET: usize = 32;

fn c_expr_size(expr: &Expr) -> usize {
    let mut count = 0;
    let mut pending = vec![expr];
    while let Some(node) = pending.pop() {
        count += 1;
        pending.extend(
            crate::simplify::children(node)
                .into_iter()
                .map(|child| child.as_ref()),
        );
    }
    count
}

fn c_inline_budget() -> usize {
    std::env::var("MARM_C_INLINE_BUDGET")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(C_INLINE_BUDGET)
}

fn direct_array_enabled() -> bool {
    std::env::var_os("MARM_NO_DIRECT_ARRAY").is_none() && std::env::var_os("MARM_NOFLAT").is_none()
}

/// A loop that allocates nothing never reaches the allocator's poll in
/// `gc_reserve`, so a collection would wait for it forever. That is not an exotic
/// case: a zero-allocation loop is what the optimiser is *trying* to produce, and
/// every unbounded computation reaches back through one of the three loopify sites
/// below.
///
/// But a loop that DOES allocate, or that calls anything which might, already
/// reaches `gc_reserve` at least once per bump run -- polling it again per
/// iteration is pure cost. And it is not small: the flag is atomic precisely so it
/// cannot be hoisted out of the loop, which measured **+10% on `billions`**, whose
/// hot loops are tight and allocate constantly. So the poll goes only where it is
/// the only thing standing between a loop and a hung collector.
///
/// A structural summary proves this per backedge, including calls transitively.
/// It errs towards keeping the poll whenever allocation cannot be established on
/// every route to the backedge. `MARM_NO_POLL` removes it entirely for measurement.
/// The poll itself, amortised. Reading the flag every iteration costs real time --
/// it is atomic precisely so it cannot be hoisted, which measured ~10% on tight
/// loops. A register countdown is far cheaper than a memory read, and checking one
/// iteration in 4096 still bounds the rendezvous at well under a microsecond for
/// any loop tight enough for this to matter.
const POLL: &str = "if (__builtin_expect(--_poll == 0, 0)) { _poll = 4096; gc_poll(); } ";
const POLL_DECL: &str = "unsigned _poll = 4096; ";

fn poll_decl(needs_poll: bool) -> &'static str {
    if back_edge_poll(needs_poll).is_empty() {
        ""
    } else {
        POLL_DECL
    }
}

fn back_edge_poll(needs_poll: bool) -> &'static str {
    if std::env::var_os("MARM_NO_POLL").is_some() {
        return "";
    }
    if needs_poll { POLL } else { "" }
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
    /// One stored word that may legitimately be zero, because a niche sum was
    /// spliced into this position and spells its nullary constructor as zero.
    /// Encodes identically to `Leaf`: the distinction exists only so `zero_niche`
    /// does not offer this word to an enclosing sum.
    ZeroableLeaf,
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
            Self::Leaf | Self::ZeroableLeaf => 1,
            Self::Product(fields) => fields.iter().map(Self::stored_words).sum(),
            Self::NicheSum { payload_fields, .. } => {
                payload_fields.iter().map(Self::stored_words).sum()
            }
            Self::Sum { payload_words, .. } => 1 + payload_words,
        }
    }

    fn encode(&self, out: &mut Vec<i64>) {
        match self {
            Self::Leaf | Self::ZeroableLeaf => out.push(0),
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

    /// Splice this shape into one entry per stored word, the way `compile_record`
    /// splices the value itself. A single-word niche sum is kept whole: reducing it
    /// to a leaf would claim its word can never be zero, when zero is exactly how
    /// that word spells the nullary constructor. An enclosing sum consulting
    /// `zero_niche` would then pick that word to host its own niche and read every
    /// nullary field as its own nullary.
    fn splat_words(self, out: &mut Vec<Self>) {
        match self {
            Self::Product(fields) => {
                for field in fields {
                    field.splat_words(out);
                }
            }
            // The splat has already encoded a niche sum into raw words, so the
            // shape must describe them as leaves -- `flatten` would otherwise read
            // a `Data` that is not there. Every word it occupies may be zero,
            // though, since that is how it spells its nullary constructor.
            niche @ Self::NicheSum { .. } => {
                out.extend(std::iter::repeat_n(
                    Self::ZeroableLeaf,
                    niche.stored_words(),
                ));
            }
            one_word if one_word.stored_words() == 1 => out.push(one_word),
            wide => out.extend(std::iter::repeat_n(Self::Leaf, wide.stored_words())),
        }
    }

    fn zero_niche(&self) -> Option<usize> {
        match self {
            Self::Leaf => Some(0),
            Self::ZeroableLeaf => None,
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
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ImmutableSliceSource {
    Local(usize),
    Captured(usize),
}

struct ImmutableSliceBase {
    source: ImmutableSliceSource,
    value: String,
    name: String,
    aliases: Vec<ImmutableSliceSource>,
}

/// A call to a structurally defined recursive spine transformation whose
/// callback reconstructs the same constructor with the accumulated spine in its
/// recursive field. With exclusive input, the transformation is pointer reversal.
struct OwnedSpineRebuild<'a> {
    input: &'a Expr,
    seed: &'a Expr,
    step_constructor: &'a QualifiedName,
    end_constructor: &'a QualifiedName,
    next_field: usize,
}

#[derive(Clone)]
struct OwnedRecursiveEliminator {
    product_parameter: usize,
    input_parameter: usize,
    combine_parameter: usize,
    combine_call: usize,
}

#[derive(Clone)]
struct OwnedProductDataStep {
    product_arity: usize,
    product_returns: Vec<usize>,
    data_return: usize,
    data_arity: usize,
    data_product_field: usize,
}

thread_local! {
    /// Lexical locals whose value is represented by a packed array element rather
    /// than an eagerly rebuilt canonical object. Entries are scoped by
    /// `compile_let`; code generation itself is single-threaded.
    static ARRAY_ELEMENT_PLACES: RefCell<HashMap<usize, ArrayElementPlace>> =
        RefCell::new(HashMap::default());
    /// Record-valued locals split into their canonical words. A whole-value use
    /// rebuilds the record; projections and other flat consumers read the words.
    static FLAT_VALUE_PLACES: RefCell<HashMap<usize, FlatValuePlace>> =
        RefCell::new(HashMap::default());
    /// Logical closure capture index -> physical range in the flat capture array.
    static CAPTURE_PLACES: RefCell<Vec<CapturePlace>> = RefCell::new(Vec::new());
    /// Saturated `raw_sub` applications in the loop currently being emitted.
    /// Each points at a reusable stack Slice whose lifetime is the loop frame;
    /// heap/return/back-edge barriers materialise it only when it escapes.
    static BORROWED_SLICE_PLACES: RefCell<HashMap<usize, String>> =
        RefCell::new(HashMap::default());
    /// Loop-invariant immutable byte views whose resolved base pointer has been
    /// snapshotted before the loop. A safepoint may mark the Slice but the
    /// non-moving collector and immutable Slice representation cannot change its
    /// `base`, so byte reads can keep using the snapshot across `gc_poll`.
    static IMMUTABLE_SLICE_BASES: RefCell<HashMap<ImmutableSliceSource, String>> =
        RefCell::new(HashMap::default());
    /// Constructor-spine values whose complete reachable spine is exclusively
    /// owned by the current expression. This is deliberately lexical: ownership
    /// is installed for an owned worker parameter, a fresh let, or the recursive
    /// field/whole-value bind of a match on an owned scrutinee, then restored.
    static OWNED_SPINE_LOCALS: RefCell<HashSet<usize>> = RefCell::new(HashSet::default());
    /// Direct workers proven to return a freshly allocated recursive constructor
    /// spine on every path (or its nullary terminator).
    static FRESH_SPINE_WORKERS: RefCell<HashSet<QualifiedName>> = RefCell::new(HashSet::default());
    /// Unary wrappers which can consume an exclusive argument through a
    /// structurally defined recursive spine reconstruction.
    static OWNED_REBUILD_WORKER_VARIANTS: RefCell<HashSet<QualifiedName>> =
        RefCell::new(HashSet::default());
    /// Curried-chain heads with a two-argument step whose second argument is
    /// destructured once and replaced by a tuple of the same arity.
    static OWNED_TUPLE_STEP_WORKERS: RefCell<HashMap<QualifiedName, usize>> =
        RefCell::new(HashMap::default());
    /// Binary product-transforming closures which can also place one recursive
    /// data result into caller-provided storage.
    static OWNED_PRODUCT_DATA_STEP_WORKERS: RefCell<HashMap<QualifiedName, OwnedProductDataStep>> =
        RefCell::new(HashMap::default());
    /// Exact tuple-expression nodes which become in-place replacements while an
    /// owned step-worker variant is emitted: expression address -> (local, arity).
    static OWNED_TUPLE_RETURNS: RefCell<HashMap<usize, (usize, usize)>> =
        RefCell::new(HashMap::default());
    /// Tuple-valued locals exclusively owned by the current worker variant.
    static OWNED_TUPLE_LOCALS: RefCell<HashSet<usize>> = RefCell::new(HashSet::default());
    /// Fresh tuple literals represented by tuple-shaped storage in the current C
    /// stack frame.  Their existing `Value` ABI is preserved, but no heap object
    /// is needed while an ownership-preserving call updates and returns them.
    static VIRTUAL_TUPLE_LITERALS: RefCell<HashMap<usize, String>> =
        RefCell::new(HashMap::default());
    /// Top-level workers with a parameter whose ownership can flow through every
    /// result path. The value lists eligible parameter indices.
    static OWNED_TUPLE_WORKER_VARIANTS: RefCell<HashMap<QualifiedName, Vec<usize>>> =
        RefCell::new(HashMap::default());
    /// Recursive constructor-producing workers with an input spine that can be
    /// overwritten when the caller owns it. The parameter indices are selected
    /// structurally; no source constructor or function name is involved.
    static OWNED_DATA_WORKER_VARIANTS: RefCell<HashMap<QualifiedName, Vec<usize>>> =
        RefCell::new(HashMap::default());
    /// Exact constructor result nodes replaced while an owned-data worker is
    /// emitted: expression address -> owned parameter local.
    static OWNED_DATA_RETURNS: RefCell<HashMap<usize, String>> =
        RefCell::new(HashMap::default());
    /// Combine applications in a recursive eliminator: expression address ->
    /// local holding the exclusively owned input constructor node.
    static OWNED_RECURSIVE_COMBINE_CALLS: RefCell<HashMap<usize, usize>> =
        RefCell::new(HashMap::default());
    static OWNED_RECURSIVE_ELIMINATORS: RefCell<HashMap<QualifiedName, OwnedRecursiveEliminator>> =
        RefCell::new(HashMap::default());
    /// Workers whose result contains an exclusively owned input spine without
    /// publishing another alias to it (for example, prefixing fresh nodes).
    static OWNED_SPINE_PRESERVING_WORKERS: RefCell<HashMap<QualifiedName, Vec<usize>>> =
        RefCell::new(HashMap::default());
    /// Fresh-result wrappers whose exclusive parameter can flow into a nested
    /// owned-data consumer. Variants retain the ordinary ABI and source body.
    static OWNED_SPINE_WORKER_VARIANTS: RefCell<HashMap<QualifiedName, Vec<usize>>> =
        RefCell::new(HashMap::default());
    /// When set, the first copy of a peeled tail loop jumps to its ownership-aware
    /// steady-state loop after assigning the back-edge arguments.
    static TAIL_BACKEDGE_LABEL: RefCell<Option<String>> = const { RefCell::new(None) };
    /// Parameters freshly produced by every backedge of the steady-state loop.
    /// They remain borrowed through the body and become consumable only while
    /// compiling their final occurrence among the backedge arguments.
    static TAIL_BACKEDGE_OWNED_LOCALS: RefCell<HashSet<usize>> =
        RefCell::new(HashSet::default());
    /// Path-linear loop values whose ownership is established at runtime (for
    /// example, an accumulator preserved on one branch and freshly replaced on
    /// another). The map value is a generated C `bool` expression.
    static DYNAMIC_OWNED_SPINE_LOCALS: RefCell<HashMap<usize, String>> =
        RefCell::new(HashMap::default());
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
    let ty = &arg.annotation().type_info.inferred_type;
    match ty {
        Type::Base(BaseType::Int) => "prim_show_int",
        Type::Base(BaseType::Float) => "prim_show_float",
        Type::Base(BaseType::Char) => "prim_show_char",
        // Includes both the legacy base type and the exact stdlib Text newtype.
        _ if is_text_type(ty) => "prim_show_text",
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
            ..
        } if matches!(constructor.as_ref(), Type::Constructor(name) if *name == QualifiedName::builtin("Array")) => {
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
        ..
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
        TypeExpression::Apply(_, application) => Some(Type::application(
            instantiate_type_expression(&application.function, bindings)?,
            instantiate_type_expression(&application.argument, bindings)?,
        )),
        TypeExpression::ConfinementAscription(_, body, _) => {
            instantiate_type_expression(body, bindings)
        }
        TypeExpression::Arrow(_, arrow) => Some(Type::Arrow {
            capture: arrow.capture.clone(),
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

fn expression_name(expr: &Expr) -> Option<&QualifiedName> {
    match strip_ascription(expr) {
        Expr::Variable(_, Identifier::Global(name)) => Some(name.as_ref()),
        Expr::InvokeBridge(_, bridge) => Some(&bridge.qualified_name),
        _ => None,
    }
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
    fn named_application<'a>(expression: &'a Expr) -> Option<(&'a QualifiedName, Vec<&'a Expr>)> {
        let mut head = strip_ascription(expression);
        let mut arguments = Vec::new();
        while let Expr::Apply(_, application) = head {
            arguments.push(application.argument.as_ref());
            head = strip_ascription(&application.function);
        }
        arguments.reverse();
        let Expr::Variable(_, Identifier::Global(name)) = head else {
            return None;
        };
        Some((name.as_ref(), arguments))
    }

    fn local_level(expression: &Expr) -> Option<usize> {
        let Expr::Variable(_, Identifier::Local(LexicalLevel(level))) =
            strip_ascription(expression)
        else {
            return None;
        };
        Some(*level)
    }

    fn local_use_count(expression: &Expr, wanted: usize) -> usize {
        usize::from(Self::local_level(expression) == Some(wanted))
            + crate::simplify::children(expression)
                .into_iter()
                .map(|child| Self::local_use_count(child, wanted))
                .sum::<usize>()
    }

    fn fresh_product_fields_from_recursive_eliminator(
        &self,
        expression: &Expr,
        self_name: &QualifiedName,
        known: &HashSet<QualifiedName>,
        owned: &HashSet<usize>,
    ) -> Vec<usize> {
        let Some((name, arguments)) = Self::named_application(expression) else {
            return Vec::new();
        };
        let Some(variant) =
            OWNED_RECURSIVE_ELIMINATORS.with(|variants| variants.borrow().get(name).cloned())
        else {
            return Vec::new();
        };
        let Some(Expr::MakeClosure(_, closure)) = arguments
            .get(variant.combine_parameter)
            .map(|argument| strip_ascription(argument))
        else {
            return Vec::new();
        };
        let Some(step) = OWNED_PRODUCT_DATA_STEP_WORKERS
            .with(|steps| steps.borrow().get(&closure.lifted_name).cloned())
        else {
            return Vec::new();
        };
        let Some(Expr::Tuple(_, seed)) = arguments
            .get(variant.product_parameter)
            .map(|argument| strip_ascription(argument))
        else {
            return Vec::new();
        };
        seed.elements
            .get(step.data_product_field)
            .is_some_and(|field| {
                self.expression_returns_fresh_spine_with_locals(field, self_name, known, owned)
            })
            .then_some(step.data_product_field)
            .into_iter()
            .collect()
    }

    /// Whether every result path constructs a fresh recursive constructor spine.
    /// Recursive calls to `self_name` are accepted coinductively; calls to workers
    /// already admitted by the fixed point are fresh too. A constructor field is
    /// recursive when its inferred type equals the enclosing constructor value's
    /// type, so this has no knowledge of `List`, `Cons`, or field position.
    fn expression_returns_fresh_spine(
        &self,
        expression: &Expr,
        self_name: &QualifiedName,
        known: &HashSet<QualifiedName>,
    ) -> bool {
        self.expression_returns_fresh_spine_with_locals(
            expression,
            self_name,
            known,
            &HashSet::default(),
        )
    }

    fn expression_returns_fresh_spine_with_locals(
        &self,
        expression: &Expr,
        self_name: &QualifiedName,
        known: &HashSet<QualifiedName>,
        owned: &HashSet<usize>,
    ) -> bool {
        let expression = strip_ascription(expression);
        if Self::local_level(expression).is_some_and(|level| owned.contains(&level)) {
            return true;
        }
        if let Some((constructor, arguments)) = Self::constructor_application(expression) {
            if self.newtype_constructors.contains(constructor) {
                return arguments.len() == 1
                    && (Self::named_application(arguments[0])
                        .is_some_and(|(name, _)| name == self_name || known.contains(name))
                        || self.expression_returns_fresh_spine_with_locals(
                            arguments[0],
                            self_name,
                            known,
                            owned,
                        ));
            }
            if self.constructor_tags.contains_key(constructor) {
                if arguments.is_empty() {
                    return true;
                }
                let result_type = &expression.annotation().type_info.inferred_type;
                let recursive = arguments
                    .iter()
                    .filter(|argument| {
                        &argument.annotation().type_info.inferred_type == result_type
                    })
                    .collect::<Vec<_>>();
                return !recursive.is_empty()
                    && recursive.iter().all(|argument| {
                        Self::named_application(argument)
                            .is_some_and(|(name, _)| name == self_name || known.contains(name))
                            || self.expression_returns_fresh_spine_with_locals(
                                argument, self_name, known, owned,
                            )
                    });
            }
        }

        if let Some((name, arguments)) = Self::named_application(expression) {
            if name == self_name || known.contains(name) {
                return true;
            }
            if let [argument] = arguments.as_slice()
                && self.workers.iter().any(|worker| {
                    worker.name == *name
                        && worker.params == 1
                        && Self::local_use_count(&worker.body, 0) == 1
                        && !self.has_tail_self_call(SelfCall::Named(&worker.name), 1, &worker.body)
                        && self.expression_contains_spine_rebuild(&worker.body)
                })
                && (Self::named_application(argument)
                    .is_some_and(|(producer, _)| known.contains(producer))
                    || self.expression_returns_fresh_spine_with_locals(
                        argument, self_name, known, owned,
                    ))
            {
                return true;
            }
        }

        match expression {
            Expr::Let(_, binding) => {
                let mut inner = owned.clone();
                if self.expression_returns_fresh_spine_with_locals(
                    &binding.bound,
                    self_name,
                    known,
                    owned,
                ) && let Identifier::Local(LexicalLevel(level)) = binding.binder
                {
                    inner.insert(level);
                }
                self.expression_returns_fresh_spine_with_locals(
                    &binding.body,
                    self_name,
                    known,
                    &inner,
                )
            }
            Expr::Sequence(_, sequence) => self.expression_returns_fresh_spine_with_locals(
                &sequence.and_then,
                self_name,
                known,
                owned,
            ),
            Expr::If(_, branch) => {
                self.expression_returns_fresh_spine_with_locals(
                    &branch.consequent,
                    self_name,
                    known,
                    owned,
                ) && self.expression_returns_fresh_spine_with_locals(
                    &branch.alternate,
                    self_name,
                    known,
                    owned,
                )
            }
            Expr::Deconstruct(_, deconstruct) => {
                let scrutinee_owned = self.expression_returns_fresh_spine_with_locals(
                    &deconstruct.scrutinee,
                    self_name,
                    known,
                    owned,
                );
                !deconstruct.match_clauses.is_empty()
                    && deconstruct.match_clauses.iter().all(|clause| {
                        let mut inner = owned.clone();
                        if scrutinee_owned {
                            self.collect_owned_spine_pattern_binders(
                                &clause.pattern,
                                &deconstruct.scrutinee.annotation().type_info.inferred_type,
                                &mut inner,
                            );
                        }
                        if let Pattern::Tuple(_, pattern) = &clause.pattern {
                            for field in self.fresh_product_fields_from_recursive_eliminator(
                                &deconstruct.scrutinee,
                                self_name,
                                known,
                                owned,
                            ) {
                                if let Some(field_pattern) = pattern.elements.get(field) {
                                    self.collect_owned_spine_pattern_binders(
                                        field_pattern,
                                        &field_pattern.annotation().type_info.inferred_type,
                                        &mut inner,
                                    );
                                }
                            }
                        }
                        self.expression_returns_fresh_spine_with_locals(
                            &clause.consequent,
                            self_name,
                            known,
                            &inner,
                        )
                    })
            }
            _ => false,
        }
    }

    fn fresh_spine_workers(&self) -> HashSet<QualifiedName> {
        let mut fresh = HashSet::default();
        loop {
            let additions = self
                .workers
                .iter()
                .filter(|worker| {
                    !fresh.contains(&worker.name)
                        && self.expression_returns_fresh_spine(&worker.body, &worker.name, &fresh)
                })
                .map(|worker| worker.name.clone())
                .collect::<Vec<_>>();
            if additions.is_empty() {
                break;
            }
            fresh.extend(additions);
        }
        fresh
    }

    fn expression_is_fresh_spine(&self, expression: &Expr) -> bool {
        FRESH_SPINE_WORKERS.with(|fresh| {
            let fresh = fresh.borrow();
            Self::named_application(expression).is_some_and(|(name, _)| fresh.contains(name))
        })
    }

    /// Recognize a recursive spine transformation from semantics alone:
    ///
    /// * one worker deconstructs a recursive sum with one terminal constructor
    ///   and one step constructor;
    /// * the terminal branch returns a seed;
    /// * the step branch invokes a callback with the accumulator and every
    ///   non-recursive payload, then tail-recurs on the sole recursive field;
    /// * that callback reconstructs the same step constructor, placing the old
    ///   accumulator in its recursive field.
    ///
    /// No type, constructor, module, or function identity participates.
    fn owned_spine_rebuild<'a>(
        &'a self,
        head: &'a Expr,
        arguments: &[&'a Expr],
    ) -> Option<OwnedSpineRebuild<'a>> {
        if std::env::var_os("MARM_NO_OWNED_SPINES").is_some() || arguments.len() != 3 {
            return None;
        }
        let Expr::Variable(_, Identifier::Global(worker_name)) = strip_ascription(head) else {
            return None;
        };
        let worker = self
            .workers
            .iter()
            .find(|worker| worker.name == **worker_name && worker.params == 3)?;
        let Expr::Deconstruct(_, deconstruct) = strip_ascription(&worker.body) else {
            return None;
        };
        if Self::local_level(&deconstruct.scrutinee) != Some(2)
            || deconstruct.match_clauses.len() != 2
        {
            return None;
        }

        let mut end_constructor = None;
        let mut step = None;
        for clause in &deconstruct.match_clauses {
            let Pattern::Coproduct(_, constructor) = &clause.pattern else {
                return None;
            };
            let Identifier::Global(name) = &constructor.constructor else {
                return None;
            };
            if constructor.arguments.is_empty() {
                if end_constructor.is_some() || Self::local_level(&clause.consequent) != Some(1) {
                    return None;
                }
                end_constructor = Some(name.as_ref());
                continue;
            }

            let binders = constructor
                .arguments
                .iter()
                .map(|pattern| match pattern {
                    Pattern::Bind(_, Identifier::Local(LexicalLevel(level))) => Some(*level),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()?;
            let (called, recursive_arguments) = Self::named_application(&clause.consequent)?;
            if called != worker_name.as_ref()
                || recursive_arguments.len() != 3
                || Self::local_level(recursive_arguments[0]) != Some(0)
            {
                return None;
            }
            let tail_level = Self::local_level(recursive_arguments[2])?;
            let next_field = binders.iter().position(|level| *level == tail_level)?;
            let input_type = &deconstruct.scrutinee.annotation().type_info.inferred_type;
            let recursive_fields = constructor
                .arguments
                .iter()
                .enumerate()
                .filter_map(|(index, pattern)| {
                    (&pattern.annotation().type_info.inferred_type == input_type).then_some(index)
                })
                .collect::<Vec<_>>();
            if recursive_fields.as_slice() != [next_field] {
                return None;
            }

            let mut combine_head = strip_ascription(recursive_arguments[1]);
            let mut combine_arguments = Vec::new();
            while let Expr::Apply(_, application) = combine_head {
                combine_arguments.push(application.argument.as_ref());
                combine_head = strip_ascription(&application.function);
            }
            combine_arguments.reverse();
            if Self::local_level(combine_head) != Some(0)
                || combine_arguments.len() != binders.len()
                || Self::local_level(combine_arguments[0]) != Some(1)
            {
                return None;
            }
            let payload = binders
                .iter()
                .enumerate()
                .filter_map(|(index, level)| (index != next_field).then_some(*level))
                .collect::<Vec<_>>();
            if !combine_arguments[1..]
                .iter()
                .zip(payload)
                .all(|(argument, level)| Self::local_level(argument) == Some(level))
                || step.is_some()
            {
                return None;
            }
            step = Some((name.as_ref(), next_field, binders.len()));
        }

        let end_constructor = end_constructor?;
        let (step_constructor, next_field, fields) = step?;
        let (seed_constructor, seed_arguments) = Self::constructor_application(arguments[1])?;
        if seed_constructor != end_constructor || !seed_arguments.is_empty() {
            return None;
        }
        let Expr::MakeClosure(_, closure) = strip_ascription(arguments[0]) else {
            return None;
        };
        let Expr::Tuple(_, environment) = closure.environment.as_ref() else {
            return None;
        };
        if !environment.elements.is_empty() {
            return None;
        }
        let rebuild = self
            .chain_workers
            .iter()
            .find(|candidate| candidate.head == closure.lifted_name && candidate.arity == fields)?;
        let (rebuilt_constructor, rebuilt_fields) = Self::constructor_application(&rebuild.body)?;
        if rebuilt_constructor != step_constructor || rebuilt_fields.len() != fields {
            return None;
        }
        let mut payload_parameter = 1usize;
        for (index, field) in rebuilt_fields.iter().enumerate() {
            let expected = if index == next_field {
                0
            } else {
                let parameter = payload_parameter;
                payload_parameter += 1;
                parameter
            };
            if Self::local_level(field) != Some(expected) {
                return None;
            }
        }
        Some(OwnedSpineRebuild {
            input: arguments[2],
            seed: arguments[1],
            step_constructor,
            end_constructor,
            next_field,
        })
    }

    fn subspine_result(
        expression: &Expr,
        allowed: &HashSet<usize>,
        recursive_arity: usize,
    ) -> bool {
        let expression = strip_ascription(expression);
        if Self::local_level(expression).is_some_and(|level| allowed.contains(&level)) {
            return true;
        }
        if matches!(expression, Expr::Apply(..)) {
            let mut head = expression;
            let mut arguments = Vec::new();
            while let Expr::Apply(_, application) = head {
                arguments.push(application.argument.as_ref());
                head = strip_ascription(&application.function);
            }
            arguments.reverse();
            if matches!(head, Expr::Variable(_, Identifier::SelfRef))
                && arguments.len() == recursive_arity
            {
                return arguments
                    .iter()
                    .all(|argument| Self::subspine_result(argument, allowed, recursive_arity));
            }
        }
        match expression {
            Expr::Let(_, binding) => {
                let mut inner = allowed.clone();
                if Self::subspine_result(&binding.bound, allowed, recursive_arity)
                    && let Identifier::Local(LexicalLevel(level)) = binding.binder
                {
                    inner.insert(level);
                }
                Self::subspine_result(&binding.body, &inner, recursive_arity)
            }
            Expr::If(_, branch) => {
                Self::subspine_result(&branch.consequent, allowed, recursive_arity)
                    && Self::subspine_result(&branch.alternate, allowed, recursive_arity)
            }
            Expr::Deconstruct(_, deconstruct)
                if Self::local_level(&deconstruct.scrutinee)
                    .is_some_and(|level| allowed.contains(&level)) =>
            {
                let scrutinee_type = &deconstruct.scrutinee.annotation().type_info.inferred_type;
                deconstruct.match_clauses.iter().all(|clause| {
                    let mut inner = allowed.clone();
                    Self::collect_same_type_pattern_binders(
                        &clause.pattern,
                        scrutinee_type,
                        &mut inner,
                    );
                    Self::subspine_result(&clause.consequent, &inner, recursive_arity)
                })
            }
            _ => false,
        }
    }

    fn closure_preserves_owned_subspine(&self, closure: &ClosureInfo, arity: usize) -> bool {
        let body = if arity == 1 {
            let Some(function) = self
                .functions
                .iter()
                .find(|function| function.name == closure.lifted_name)
            else {
                return false;
            };
            &function.code
        } else {
            let Some(worker) = self
                .chain_workers
                .iter()
                .find(|worker| worker.head == closure.lifted_name && worker.arity == arity)
            else {
                return false;
            };
            &worker.body
        };
        let allowed = (0..arity).collect::<HashSet<_>>();
        Self::subspine_result(body, &allowed, arity)
    }

    fn expression_preserves_owned_spine(
        &self,
        expression: &Expr,
        owner: usize,
        self_name: &QualifiedName,
    ) -> bool {
        let expression = strip_ascription(expression);
        if Self::local_level(expression) == Some(owner) {
            return true;
        }
        if let Some((name, arguments)) = Self::named_application(expression)
            && name == self_name
            && let Some(argument) = arguments.get(owner)
            && arguments
                .iter()
                .enumerate()
                .all(|(index, other)| index == owner || Self::local_use_count(other, owner) == 0)
            && Self::same_type(expression, argument)
            && self.expression_preserves_owned_spine(argument, owner, self_name)
        {
            return true;
        }
        if let Some((constructor, arguments)) = Self::constructor_application(expression)
            && self.constructor_tags.contains_key(constructor)
        {
            if arguments.is_empty() {
                return true;
            }
            let result_type = &expression.annotation().type_info.inferred_type;
            let recursive = arguments
                .iter()
                .filter(|argument| &argument.annotation().type_info.inferred_type == result_type)
                .collect::<Vec<_>>();
            return !recursive.is_empty()
                && recursive.iter().all(|argument| {
                    self.expression_preserves_owned_spine(argument, owner, self_name)
                })
                && arguments
                    .iter()
                    .filter(|argument| {
                        &argument.annotation().type_info.inferred_type != result_type
                    })
                    .all(|argument| Self::local_use_count(argument, owner) == 0);
        }
        match expression {
            Expr::Let(_, binding) => {
                Self::local_use_count(&binding.bound, owner) == 0
                    && self.expression_preserves_owned_spine(&binding.body, owner, self_name)
            }
            Expr::Sequence(_, sequence) => {
                Self::local_use_count(&sequence.this, owner) == 0
                    && self.expression_preserves_owned_spine(&sequence.and_then, owner, self_name)
            }
            Expr::If(_, branch) => {
                Self::local_use_count(&branch.predicate, owner) == 0
                    && self.expression_preserves_owned_spine(&branch.consequent, owner, self_name)
                    && self.expression_preserves_owned_spine(&branch.alternate, owner, self_name)
            }
            Expr::Deconstruct(_, deconstruct) => {
                Self::local_use_count(&deconstruct.scrutinee, owner) == 0
                    && !deconstruct.match_clauses.is_empty()
                    && deconstruct.match_clauses.iter().all(|clause| {
                        self.expression_preserves_owned_spine(&clause.consequent, owner, self_name)
                    })
            }
            _ => false,
        }
    }

    fn owned_spine_preserving_workers(&self) -> HashMap<QualifiedName, Vec<usize>> {
        self.workers
            .iter()
            .filter_map(|worker| {
                let parameters = (0..worker.params)
                    .filter(|parameter| {
                        Self::local_use_count(&worker.body, *parameter) != 0
                            && self.expression_preserves_owned_spine(
                                &worker.body,
                                *parameter,
                                &worker.name,
                            )
                    })
                    .collect::<Vec<_>>();
                (!parameters.is_empty()).then(|| (worker.name.clone(), parameters))
            })
            .collect()
    }

    fn expression_is_owned_spine(&self, expression: &Expr) -> bool {
        let owned = OWNED_SPINE_LOCALS.with(|current| current.borrow().clone());
        self.expression_is_owned_spine_with_locals(expression, &owned)
    }

    fn owned_product_fields_from_recursive_eliminator(
        &self,
        expression: &Expr,
        owned: &HashSet<usize>,
    ) -> Vec<usize> {
        if std::env::var_os("MARM_NO_PRODUCT_SPINE_PROVENANCE").is_some() {
            return Vec::new();
        }
        let Some((name, arguments)) = Self::named_application(expression) else {
            return Vec::new();
        };
        let Some(variant) =
            OWNED_RECURSIVE_ELIMINATORS.with(|variants| variants.borrow().get(name).cloned())
        else {
            return Vec::new();
        };
        let Some(Expr::MakeClosure(_, closure)) = arguments
            .get(variant.combine_parameter)
            .map(|argument| strip_ascription(argument))
        else {
            return Vec::new();
        };
        let Some(step) = OWNED_PRODUCT_DATA_STEP_WORKERS
            .with(|steps| steps.borrow().get(&closure.lifted_name).cloned())
        else {
            return Vec::new();
        };
        let Some(Expr::Tuple(_, seed)) = arguments
            .get(variant.product_parameter)
            .map(|argument| strip_ascription(argument))
        else {
            return Vec::new();
        };
        seed.elements
            .get(step.data_product_field)
            .is_some_and(|field| self.expression_is_owned_spine_with_locals(field, owned))
            .then_some(step.data_product_field)
            .into_iter()
            .collect()
    }

    /// An owned value may be mentioned more than once inside one call. Passing
    /// one mention to a consuming specialization would then mutate storage that
    /// another argument still aliases. Fresh expressions have no such external
    /// alias; for values derived from an owned local, require every other
    /// argument to be independent of that local.
    fn owned_spine_argument_is_exclusive(&self, arguments: &[&Expr], selected: usize) -> bool {
        let Some(argument) = arguments.get(selected) else {
            return false;
        };
        // Distinct lexical binders can still denote the same owned value after
        // two matches on an erased wrapper. Until provenance is tracked across
        // those binds, consuming either is safe only when it is the call's sole
        // owned argument.
        if arguments.iter().enumerate().any(|(index, other)| {
            index != selected
                && self.expression_is_owned_spine(other)
                && !Self::constructor_application(other)
                    .is_some_and(|(_, fields)| fields.is_empty())
        }) {
            return false;
        }
        OWNED_SPINE_LOCALS.with(|current| {
            current.borrow().iter().all(|level| {
                Self::local_use_count(argument, *level) == 0
                    || arguments.iter().enumerate().all(|(index, other)| {
                        index == selected || Self::local_use_count(other, *level) == 0
                    })
            })
        })
    }

    /// Follow exclusive-spine provenance through the expression's lexical
    /// bindings. Simplification commonly inlines a fresh producer into a loop
    /// backedge as `let x = producer ... in ... x ...`; looking only at the
    /// final expression loses that fact and prevents the steady-state loop from
    /// consuming its freshly produced values.
    fn expression_is_owned_spine_with_locals(
        &self,
        expression: &Expr,
        owned: &HashSet<usize>,
    ) -> bool {
        let expression = strip_ascription(expression);
        if let Some(level) = Self::local_level(expression)
            && owned.contains(&level)
        {
            return true;
        }
        if self.expression_is_fresh_spine(expression) {
            return true;
        }

        if let Expr::Apply(..) = expression {
            let mut head = expression;
            let mut arguments = Vec::new();
            while let Expr::Apply(_, application) = head {
                arguments.push(application.argument.as_ref());
                head = strip_ascription(&application.function);
            }
            arguments.reverse();
            if self.owned_spine_rebuild(head, &arguments).is_some() {
                return true;
            }
            if let Expr::Variable(_, Identifier::Global(name)) = head
                && arguments.len() == 1
                && OWNED_REBUILD_WORKER_VARIANTS
                    .with(|variants| variants.borrow().contains(name.as_ref()))
                && self.expression_is_owned_spine_with_locals(arguments[0], owned)
            {
                return true;
            }
            if let Expr::Variable(_, Identifier::Global(name)) = head
                && let Some(parameters) = OWNED_SPINE_PRESERVING_WORKERS
                    .with(|workers| workers.borrow().get(name.as_ref()).cloned())
                && parameters.into_iter().any(|parameter| {
                    arguments.get(parameter).is_some_and(|argument| {
                        self.expression_is_owned_spine_with_locals(argument, owned)
                    })
                })
            {
                return true;
            }
            if let Expr::MakeClosure(_, closure) = head
                && arguments
                    .iter()
                    .all(|argument| self.expression_is_owned_spine_with_locals(argument, owned))
                && self.closure_preserves_owned_subspine(closure, arguments.len())
            {
                return true;
            }
        }

        if let Some((constructor, arguments)) = Self::constructor_application(expression) {
            if self.newtype_constructors.contains(constructor) {
                return arguments.len() == 1
                    && self.expression_is_owned_spine_with_locals(arguments[0], owned);
            }
            if !self.constructor_tags.contains_key(constructor) {
                return false;
            }
            if arguments.is_empty() {
                return true;
            }
            let result_type = &expression.annotation().type_info.inferred_type;
            let recursive = arguments
                .iter()
                .filter(|argument| &argument.annotation().type_info.inferred_type == result_type);
            let recursive = recursive.collect::<Vec<_>>();
            return !recursive.is_empty()
                && recursive
                    .iter()
                    .all(|argument| self.expression_is_owned_spine_with_locals(argument, owned));
        }
        match expression {
            Expr::Let(_, binding) => {
                let mut inner = owned.clone();
                if self.expression_is_owned_spine_with_locals(&binding.bound, owned)
                    && let Identifier::Local(LexicalLevel(level)) = binding.binder
                {
                    inner.insert(level);
                }
                self.expression_is_owned_spine_with_locals(&binding.body, &inner)
            }
            Expr::Sequence(_, sequence) => {
                self.expression_is_owned_spine_with_locals(&sequence.and_then, owned)
            }
            Expr::If(_, branch) => {
                self.expression_is_owned_spine_with_locals(&branch.consequent, owned)
                    && self.expression_is_owned_spine_with_locals(&branch.alternate, owned)
            }
            Expr::Deconstruct(_, deconstruct) => {
                let scrutinee_owned =
                    self.expression_is_owned_spine_with_locals(&deconstruct.scrutinee, owned);
                !deconstruct.match_clauses.is_empty()
                    && deconstruct.match_clauses.iter().all(|clause| {
                        let mut inner = owned.clone();
                        if scrutinee_owned {
                            self.collect_owned_spine_pattern_binders(
                                &clause.pattern,
                                &deconstruct.scrutinee.annotation().type_info.inferred_type,
                                &mut inner,
                            );
                        }
                        if let Pattern::Tuple(_, pattern) = &clause.pattern {
                            for field in self.owned_product_fields_from_recursive_eliminator(
                                &deconstruct.scrutinee,
                                owned,
                            ) {
                                if let Some(field_pattern) = pattern.elements.get(field) {
                                    self.collect_owned_spine_pattern_binders(
                                        field_pattern,
                                        &field_pattern.annotation().type_info.inferred_type,
                                        &mut inner,
                                    );
                                }
                            }
                        }
                        self.expression_is_owned_spine_with_locals(&clause.consequent, &inner)
                    })
            }
            _ => false,
        }
    }

    fn collect_same_type_pattern_binders(
        pattern: &phase::Pattern<Closed>,
        expected: &Type,
        out: &mut HashSet<usize>,
    ) {
        // Stay on direct recursive edges. A differently typed payload may hide a
        // reference back to the spine, but copying that payload does not acquire
        // ownership of anything inside it.
        if &pattern.annotation().type_info.inferred_type != expected {
            return;
        }
        match pattern {
            Pattern::Bind(annotation, Identifier::Local(LexicalLevel(level))) => {
                debug_assert_eq!(&annotation.type_info.inferred_type, expected);
                out.insert(*level);
            }
            Pattern::Coproduct(_, constructor) => {
                for argument in &constructor.arguments {
                    Self::collect_same_type_pattern_binders(argument, expected, out);
                }
            }
            Pattern::Tuple(_, tuple) => {
                for element in &tuple.elements {
                    Self::collect_same_type_pattern_binders(element, expected, out);
                }
            }
            Pattern::Struct(_, record) => {
                for (_, _, field) in &record.fields {
                    Self::collect_same_type_pattern_binders(field, expected, out);
                }
            }
            Pattern::Literally(..) | Pattern::Bind(..) => {}
        }
    }

    fn collect_owned_spine_pattern_binders(
        &self,
        pattern: &phase::Pattern<Closed>,
        expected: &Type,
        out: &mut HashSet<usize>,
    ) {
        if &pattern.annotation().type_info.inferred_type != expected {
            return;
        }
        if let Pattern::Coproduct(_, constructor) = pattern
            && let Identifier::Global(name) = &constructor.constructor
            && self.newtype_constructors.contains(name.as_ref())
        {
            for argument in &constructor.arguments {
                self.collect_owned_spine_pattern_binders(
                    argument,
                    &argument.annotation().type_info.inferred_type,
                    out,
                );
            }
            return;
        }
        Self::collect_same_type_pattern_binders(pattern, expected, out);
    }

    fn install_owned_spine_locals<I>(levels: I) -> HashSet<usize>
    where
        I: IntoIterator<Item = usize>,
    {
        OWNED_SPINE_LOCALS.with(|owned| {
            let previous = owned.borrow().clone();
            owned.borrow_mut().extend(levels);
            previous
        })
    }

    fn restore_owned_spine_locals(previous: HashSet<usize>) {
        OWNED_SPINE_LOCALS.with(|owned| *owned.borrow_mut() = previous);
    }

    fn max_local_uses_per_path(expression: &Expr, wanted: usize) -> usize {
        let expression = strip_ascription(expression);
        match expression {
            Expr::If(_, branch) => {
                Self::max_local_uses_per_path(&branch.predicate, wanted)
                    + Self::max_local_uses_per_path(&branch.consequent, wanted)
                        .max(Self::max_local_uses_per_path(&branch.alternate, wanted))
            }
            Expr::Deconstruct(_, deconstruct) => {
                Self::max_local_uses_per_path(&deconstruct.scrutinee, wanted)
                    + deconstruct
                        .match_clauses
                        .iter()
                        .map(|clause| Self::max_local_uses_per_path(&clause.consequent, wanted))
                        .max()
                        .unwrap_or(0)
            }
            Expr::Let(_, binding) => {
                Self::max_local_uses_per_path(&binding.bound, wanted)
                    + Self::max_local_uses_per_path(&binding.body, wanted)
            }
            Expr::Sequence(_, sequence) => {
                Self::max_local_uses_per_path(&sequence.this, wanted)
                    + Self::max_local_uses_per_path(&sequence.and_then, wanted)
            }
            _ => {
                usize::from(Self::local_level(expression) == Some(wanted))
                    + crate::simplify::children(expression)
                        .into_iter()
                        .map(|child| Self::max_local_uses_per_path(child, wanted))
                        .sum::<usize>()
            }
        }
    }

    fn owned_local_is_linear(expression: &Expr, wanted: usize) -> bool {
        // Branch alternatives are mutually exclusive. One use in each arm is
        // therefore one dynamic use, and an owned recursive node can remain the
        // destination along either path. Counting the whole syntax tree here
        // used to drop destination ownership at exactly these joins.
        if std::env::var_os("MARM_NO_PATH_LINEAR_OWNERSHIP").is_some() {
            Self::local_use_count(expression, wanted) == 1
        } else {
            Self::max_local_uses_per_path(expression, wanted) <= 1
        }
    }

    fn dynamic_owned_condition(&self, expression: &Expr) -> Option<String> {
        if let Some(level) = Self::local_level(expression)
            && let Some(condition) =
                DYNAMIC_OWNED_SPINE_LOCALS.with(|current| current.borrow().get(&level).cloned())
        {
            return Some(condition);
        }
        self.expression_is_owned_spine(expression)
            .then(|| "true".to_owned())
    }

    fn install_dynamic_owned_spine_locals<I>(entries: I) -> HashMap<usize, String>
    where
        I: IntoIterator<Item = (usize, String)>,
    {
        DYNAMIC_OWNED_SPINE_LOCALS.with(|current| {
            let previous = current.borrow().clone();
            current.borrow_mut().extend(entries);
            previous
        })
    }

    fn restore_dynamic_owned_spine_locals(previous: HashMap<usize, String>) {
        DYNAMIC_OWNED_SPINE_LOCALS.with(|current| *current.borrow_mut() = previous);
    }

    fn expression_contains_spine_rebuild(&self, expression: &Expr) -> bool {
        if let Expr::Apply(..) = strip_ascription(expression) {
            let mut head = strip_ascription(expression);
            let mut arguments = Vec::new();
            while let Expr::Apply(_, application) = head {
                arguments.push(application.argument.as_ref());
                head = strip_ascription(&application.function);
            }
            arguments.reverse();
            if self.owned_spine_rebuild(head, &arguments).is_some() {
                return true;
            }
        }
        crate::simplify::children(expression)
            .into_iter()
            .any(|child| self.expression_contains_spine_rebuild(child))
    }

    fn owned_rebuild_worker_variants(
        &self,
        fresh: &HashSet<QualifiedName>,
    ) -> HashSet<QualifiedName> {
        let candidates = self
            .workers
            .iter()
            .filter(|worker| {
                worker.params == 1
                    && Self::local_use_count(&worker.body, 0) == 1
                    && !self.has_tail_self_call(SelfCall::Named(&worker.name), 1, &worker.body)
                    && self.expression_contains_spine_rebuild(&worker.body)
            })
            .map(|worker| worker.name.clone())
            .collect::<HashSet<_>>();
        let mut selected = HashSet::default();
        fn visit(
            expression: &Expr,
            candidates: &HashSet<QualifiedName>,
            fresh: &HashSet<QualifiedName>,
            selected: &mut HashSet<QualifiedName>,
        ) {
            if let Some((name, arguments)) = lambda_lift::Program::named_application(expression)
                && candidates.contains(name)
                && matches!(arguments.as_slice(), [argument]
                    if lambda_lift::Program::named_application(argument)
                        .is_some_and(|(producer, _)| fresh.contains(producer)))
            {
                selected.insert(name.clone());
            }
            for child in crate::simplify::children(expression) {
                visit(child, candidates, fresh, selected);
            }
        }
        for function in &self.functions {
            visit(&function.code, &candidates, fresh, &mut selected);
        }
        for worker in &self.workers {
            visit(&worker.body, &candidates, fresh, &mut selected);
        }
        for worker in &self.chain_workers {
            visit(&worker.body, &candidates, fresh, &mut selected);
        }
        for global in &self.globals {
            visit(&global.value, &candidates, fresh, &mut selected);
        }
        selected
    }

    fn result_tuple_nodes(expression: &Expr, arity: usize, out: &mut Vec<usize>) -> bool {
        let expression = strip_ascription(expression);
        match expression {
            Expr::Tuple(_, tuple) if tuple.elements.len() == arity => {
                out.push(expression as *const Expr as usize);
                true
            }
            Expr::Let(_, binding) => Self::result_tuple_nodes(&binding.body, arity, out),
            Expr::Sequence(_, sequence) => Self::result_tuple_nodes(&sequence.and_then, arity, out),
            Expr::If(_, branch) => {
                Self::result_tuple_nodes(&branch.consequent, arity, out)
                    && Self::result_tuple_nodes(&branch.alternate, arity, out)
            }
            Expr::Deconstruct(_, deconstruct) => {
                !deconstruct.match_clauses.is_empty()
                    && deconstruct
                        .match_clauses
                        .iter()
                        .all(|clause| Self::result_tuple_nodes(&clause.consequent, arity, out))
            }
            _ => false,
        }
    }

    /// Return the tuple arity and exact result nodes for a two-argument step
    /// which consumes its accumulator only by destructuring it.  Reusing the
    /// accumulator box is then observationally equivalent to returning a fresh
    /// tuple, provided the caller owns that accumulator.
    fn owned_tuple_step(&self, worker: &ChainWorker) -> Option<(usize, Vec<usize>)> {
        if std::env::var_os("MARM_NO_OWNED_TUPLES").is_some() || worker.arity != 2 {
            return None;
        }
        let Expr::Deconstruct(_, deconstruct) = strip_ascription(&worker.body) else {
            return None;
        };
        if Self::local_level(&deconstruct.scrutinee) != Some(1)
            || Self::local_use_count(&worker.body, 1) != 1
            || deconstruct.match_clauses.len() != 1
        {
            return None;
        }
        let clause = &deconstruct.match_clauses[0];
        let Pattern::Tuple(_, tuple) = &clause.pattern else {
            return None;
        };
        let arity = tuple.elements.len();
        if !(1..=4).contains(&arity) {
            return None;
        }
        let mut returns = Vec::new();
        Self::result_tuple_nodes(&clause.consequent, arity, &mut returns)
            .then_some((arity, returns))
    }

    fn owned_tuple_step_workers(&self) -> HashMap<QualifiedName, usize> {
        self.chain_workers
            .iter()
            .filter_map(|worker| {
                self.owned_tuple_step(worker)
                    .map(|(arity, _)| (worker.head.clone(), arity))
            })
            .collect()
    }

    fn owned_product_data_step(&self, worker: &ChainWorker) -> Option<OwnedProductDataStep> {
        if std::env::var_os("MARM_NO_RECURSIVE_ELIMINATOR_OWNERSHIP").is_some()
            || std::env::var_os("MARM_NO_OWNED_DATA").is_some()
        {
            return None;
        }
        let (product_arity, product_returns) = self.owned_tuple_step(worker)?;
        let mut candidates = Vec::new();
        fn collect(
            program: &lambda_lift::Program,
            expression: &Expr,
            out: &mut Vec<(usize, usize)>,
        ) {
            let expression = strip_ascription(expression);
            if let Some((constructor, arguments)) =
                lambda_lift::Program::constructor_application(expression)
                && program.constructor_tags.contains_key(constructor)
                && (1..=4).contains(&arguments.len())
            {
                let result_type = &expression.annotation().type_info.inferred_type;
                if arguments
                    .iter()
                    .any(|argument| &argument.annotation().type_info.inferred_type == result_type)
                {
                    out.push((expression as *const Expr as usize, arguments.len()));
                    return;
                }
            }
            for child in crate::simplify::children(expression) {
                collect(program, child, out);
            }
        }
        collect(self, &worker.body, &mut candidates);
        let [(data_return, data_arity)] = candidates.as_slice() else {
            return None;
        };
        fn contains(expression: &Expr, wanted: usize) -> bool {
            expression as *const Expr as usize == wanted
                || crate::simplify::children(expression)
                    .into_iter()
                    .any(|child| contains(child, wanted))
        }
        fn guaranteed_result(expression: &Expr, wanted: usize) -> bool {
            let expression = strip_ascription(expression);
            if expression as *const Expr as usize == wanted {
                return true;
            }
            match expression {
                Expr::Let(_, binding) => guaranteed_result(&binding.body, wanted),
                Expr::Sequence(_, sequence) => guaranteed_result(&sequence.and_then, wanted),
                Expr::If(_, branch) => {
                    guaranteed_result(&branch.consequent, wanted)
                        && guaranteed_result(&branch.alternate, wanted)
                }
                Expr::Deconstruct(_, deconstruct) => {
                    !deconstruct.match_clauses.is_empty()
                        && deconstruct
                            .match_clauses
                            .iter()
                            .all(|clause| guaranteed_result(&clause.consequent, wanted))
                }
                _ => false,
            }
        }
        fn result_fields(
            expression: &Expr,
            returns: &HashSet<usize>,
            wanted: usize,
            out: &mut Vec<Option<usize>>,
        ) {
            let expression = strip_ascription(expression);
            if returns.contains(&(expression as *const Expr as usize)) {
                let Expr::Tuple(_, tuple) = expression else {
                    out.push(None);
                    return;
                };
                let fields = tuple
                    .elements
                    .iter()
                    .enumerate()
                    .filter_map(|(index, element)| contains(element, wanted).then_some(index))
                    .collect::<Vec<_>>();
                out.push(match fields.as_slice() {
                    [field] if guaranteed_result(&tuple.elements[*field], wanted) => Some(*field),
                    _ => None,
                });
                return;
            }
            for child in crate::simplify::children(expression) {
                result_fields(child, returns, wanted, out);
            }
        }
        let returns = product_returns.iter().copied().collect::<HashSet<_>>();
        let mut fields = Vec::new();
        result_fields(&worker.body, &returns, *data_return, &mut fields);
        if fields.len() != product_returns.len() {
            return None;
        }
        let data_product_field = fields.first().copied().flatten()?;
        if fields
            .iter()
            .any(|field| *field != Some(data_product_field))
        {
            return None;
        }
        Some(OwnedProductDataStep {
            product_arity,
            product_returns,
            data_return: *data_return,
            data_arity: *data_arity,
            data_product_field,
        })
    }

    fn owned_product_data_step_workers(&self) -> HashMap<QualifiedName, OwnedProductDataStep> {
        self.chain_workers
            .iter()
            .filter_map(|worker| {
                self.owned_product_data_step(worker)
                    .map(|step| (worker.head.clone(), step))
            })
            .collect()
    }

    /// Find recursive eliminators by their typed control/data flow. A qualifying
    /// worker deconstructs one recursive input, returns a product seed at its
    /// terminal constructor, and invokes a combine parameter with a recursive
    /// self-result at a step constructor. This is the general catamorphism shape;
    /// no declaration identity is consulted.
    fn owned_recursive_eliminators(
        &self,
        product_variants: &HashMap<QualifiedName, Vec<usize>>,
    ) -> HashMap<QualifiedName, OwnedRecursiveEliminator> {
        let mut variants = HashMap::default();
        for worker in &self.workers {
            let Some(product_parameters) = product_variants.get(&worker.name) else {
                continue;
            };
            let Expr::Deconstruct(_, deconstruct) = strip_ascription(&worker.body) else {
                continue;
            };
            let Some(input_parameter) = Self::local_level(&deconstruct.scrutinee) else {
                continue;
            };
            if deconstruct.match_clauses.len() != 2 {
                continue;
            }
            for product_parameter in product_parameters {
                let mut terminal_ok = false;
                let mut step = None;
                for clause in &deconstruct.match_clauses {
                    let Pattern::Coproduct(_, constructor) = &clause.pattern else {
                        continue;
                    };
                    if constructor.arguments.is_empty() {
                        terminal_ok |=
                            Self::local_level(&clause.consequent) == Some(*product_parameter);
                        continue;
                    }
                    let input_type = &deconstruct.scrutinee.annotation().type_info.inferred_type;
                    let tails = constructor
                        .arguments
                        .iter()
                        .filter(|argument| {
                            &argument.annotation().type_info.inferred_type == input_type
                        })
                        .filter_map(|argument| match argument {
                            Pattern::Bind(_, Identifier::Local(LexicalLevel(level))) => {
                                Some(*level)
                            }
                            _ => None,
                        })
                        .collect::<Vec<_>>();
                    let [tail] = tails.as_slice() else {
                        continue;
                    };

                    let mut combine_head = strip_ascription(&clause.consequent);
                    let combine_call = combine_head as *const Expr as usize;
                    let mut combine_arguments = Vec::new();
                    while let Expr::Apply(_, application) = combine_head {
                        combine_arguments.push(application.argument.as_ref());
                        combine_head = strip_ascription(&application.function);
                    }
                    combine_arguments.reverse();
                    let Some(combine_parameter) = Self::local_level(combine_head) else {
                        continue;
                    };
                    let Some(recursive_result) = combine_arguments.last() else {
                        continue;
                    };
                    let Some((called, recursive_arguments)) =
                        Self::named_application(recursive_result)
                    else {
                        continue;
                    };
                    if called != &worker.name
                        || recursive_arguments.len() != worker.params
                        || Self::local_level(recursive_arguments[input_parameter]) != Some(*tail)
                        || Self::local_level(recursive_arguments[*product_parameter])
                            != Some(*product_parameter)
                        || Self::local_level(recursive_arguments[combine_parameter])
                            != Some(combine_parameter)
                    {
                        continue;
                    }
                    step = Some(OwnedRecursiveEliminator {
                        product_parameter: *product_parameter,
                        input_parameter,
                        combine_parameter,
                        combine_call,
                    });
                }
                if terminal_ok && let Some(step) = step {
                    variants.insert(worker.name.clone(), step);
                }
            }
        }
        variants
    }

    fn same_type(left: &Expr, right: &Expr) -> bool {
        left.annotation().type_info.inferred_type == right.annotation().type_info.inferred_type
    }

    /// Prove that an owned tuple parameter can supply the expression's result.
    /// Calls with an owned result argument use an ownership-aware ABI: a
    /// specialized callee may update it directly, while the generic fallback
    /// computes normally and copies the value into that owned box.
    fn expression_preserves_owned_tuple(
        expression: &Expr,
        owner: usize,
        self_name: &QualifiedName,
    ) -> bool {
        let expression = strip_ascription(expression);
        if Self::local_level(expression) == Some(owner) || matches!(expression, Expr::Tuple(..)) {
            return true;
        }
        if let Expr::Apply(..) = expression {
            let mut head = expression;
            let mut arguments = Vec::new();
            while let Expr::Apply(_, application) = head {
                arguments.push(application.argument.as_ref());
                head = strip_ascription(&application.function);
            }
            arguments.reverse();
            if let Expr::Variable(_, Identifier::Global(name)) = head
                && name.as_ref() == self_name
                && let Some(argument) = arguments.get(owner)
                && arguments.iter().enumerate().all(|(index, other)| {
                    index == owner || Self::local_use_count(other, owner) == 0
                })
                && Self::same_type(expression, argument)
                && Self::expression_preserves_owned_tuple(argument, owner, self_name)
            {
                return true;
            }
            if let Some(last) = arguments.last()
                && Self::local_use_count(head, owner) == 0
                && arguments[..arguments.len() - 1]
                    .iter()
                    .all(|other| Self::local_use_count(other, owner) == 0)
                && Self::same_type(expression, last)
                && Self::expression_preserves_owned_tuple(last, owner, self_name)
            {
                return true;
            }
        }
        match expression {
            Expr::Let(_, binding) => {
                Self::local_use_count(&binding.bound, owner) == 0
                    && Self::expression_preserves_owned_tuple(&binding.body, owner, self_name)
            }
            Expr::Sequence(_, sequence) => {
                Self::local_use_count(&sequence.this, owner) == 0
                    && Self::expression_preserves_owned_tuple(&sequence.and_then, owner, self_name)
            }
            Expr::If(_, branch) => {
                Self::local_use_count(&branch.predicate, owner) == 0
                    && Self::expression_preserves_owned_tuple(&branch.consequent, owner, self_name)
                    && Self::expression_preserves_owned_tuple(&branch.alternate, owner, self_name)
            }
            Expr::Deconstruct(_, deconstruct) => {
                Self::local_use_count(&deconstruct.scrutinee, owner) == 0
                    && !deconstruct.match_clauses.is_empty()
                    && deconstruct.match_clauses.iter().all(|clause| {
                        Self::expression_preserves_owned_tuple(&clause.consequent, owner, self_name)
                    })
            }
            _ => false,
        }
    }

    fn selected_owned_tuple_expression(
        expression: &Expr,
        selected: &HashMap<QualifiedName, Vec<usize>>,
    ) -> bool {
        let expression = strip_ascription(expression);
        if matches!(expression, Expr::Tuple(..)) {
            return true;
        }
        let Expr::Apply(..) = expression else {
            return false;
        };
        let mut head = expression;
        let mut arguments = Vec::new();
        while let Expr::Apply(_, application) = head {
            arguments.push(application.argument.as_ref());
            head = strip_ascription(&application.function);
        }
        arguments.reverse();
        if let Expr::Variable(_, Identifier::Global(name)) = head
            && selected.get(name.as_ref()).is_some_and(|parameters| {
                parameters.iter().any(|parameter| {
                    arguments.get(*parameter).is_some_and(|argument| {
                        Self::same_type(expression, argument)
                            && Self::selected_owned_tuple_expression(argument, selected)
                    })
                })
            })
        {
            return true;
        }
        arguments.last().is_some_and(|last| {
            Self::same_type(expression, last)
                && Self::selected_owned_tuple_expression(last, selected)
        })
    }

    fn collect_owned_tuple_worker_calls(
        expression: &Expr,
        candidates: &HashMap<QualifiedName, Vec<usize>>,
        selected: &HashMap<QualifiedName, Vec<usize>>,
        additions: &mut HashMap<QualifiedName, Vec<usize>>,
    ) {
        if let Some((name, arguments)) = Self::named_application(expression)
            && let Some(parameters) = candidates.get(name)
        {
            for parameter in parameters {
                if arguments.get(*parameter).is_some_and(|argument| {
                    Self::selected_owned_tuple_expression(argument, selected)
                }) {
                    let entry = additions.entry(name.clone()).or_default();
                    if !entry.contains(parameter) {
                        entry.push(*parameter);
                    }
                }
            }
        }
        for child in crate::simplify::children(expression) {
            Self::collect_owned_tuple_worker_calls(child, candidates, selected, additions);
        }
    }

    fn owned_tuple_worker_variants(&self) -> HashMap<QualifiedName, Vec<usize>> {
        if std::env::var_os("MARM_NO_OWNED_TUPLES").is_some() {
            return HashMap::default();
        }
        let candidates = self
            .workers
            .iter()
            .filter_map(|worker| {
                let parameters = (0..worker.params)
                    .filter(|parameter| {
                        Self::local_use_count(&worker.body, *parameter) != 0
                            && Self::expression_preserves_owned_tuple(
                                &worker.body,
                                *parameter,
                                &worker.name,
                            )
                    })
                    .collect::<Vec<_>>();
                (!parameters.is_empty()).then(|| (worker.name.clone(), parameters))
            })
            .collect::<HashMap<_, _>>();
        let mut selected = HashMap::<QualifiedName, Vec<usize>>::default();
        loop {
            let mut additions = HashMap::default();
            for expression in self
                .functions
                .iter()
                .map(|function| &function.code)
                .chain(self.workers.iter().map(|worker| &worker.body))
                .chain(self.chain_workers.iter().map(|worker| &worker.body))
                .chain(self.globals.iter().map(|global| &global.value))
                .chain(std::iter::once(&self.start))
            {
                Self::collect_owned_tuple_worker_calls(
                    expression,
                    &candidates,
                    &selected,
                    &mut additions,
                );
            }
            let mut changed = false;
            for (name, parameters) in additions {
                let entry = selected.entry(name).or_default();
                for parameter in parameters {
                    if !entry.contains(&parameter) {
                        entry.push(parameter);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        selected
    }

    fn expression_is_owned_tuple(&self, expression: &Expr) -> bool {
        let expression = strip_ascription(expression);
        if matches!(expression, Expr::Tuple(..)) {
            return true;
        }
        if let Some(level) = Self::local_level(expression)
            && OWNED_TUPLE_LOCALS.with(|owned| owned.borrow().contains(&level))
        {
            return true;
        }
        let Expr::Apply(..) = expression else {
            return false;
        };
        let mut head = expression;
        let mut arguments = Vec::new();
        while let Expr::Apply(_, application) = head {
            arguments.push(application.argument.as_ref());
            head = strip_ascription(&application.function);
        }
        arguments.reverse();
        if let Expr::Variable(_, Identifier::Global(name)) = head
            && let Some(parameters) = OWNED_TUPLE_WORKER_VARIANTS
                .with(|workers| workers.borrow().get(name.as_ref()).cloned())
            && parameters.into_iter().any(|parameter| {
                arguments.get(parameter).is_some_and(|argument| {
                    Self::same_type(expression, argument)
                        && self.expression_is_owned_tuple(argument)
                })
            })
        {
            return true;
        }
        arguments.last().is_some_and(|last| {
            Self::same_type(expression, last) && self.expression_is_owned_tuple(last)
        })
    }

    /// Find the fresh tuple literal which supplies an ownership-preserving call's
    /// result. This mirrors `expression_is_owned_tuple`, but retains the producer
    /// node so an immediately consuming match can represent it virtually.
    fn owned_tuple_literal<'a>(
        &self,
        expression: &'a Expr,
    ) -> Option<&'a ast::Tuple<CaptureInfo, Identifier>> {
        let expression = strip_ascription(expression);
        if let Expr::Tuple(_, tuple) = expression {
            return Some(tuple);
        }
        let Expr::Apply(..) = expression else {
            return None;
        };
        let mut head = expression;
        let mut arguments = Vec::new();
        while let Expr::Apply(_, application) = head {
            arguments.push(application.argument.as_ref());
            head = strip_ascription(&application.function);
        }
        arguments.reverse();
        if let Expr::Variable(_, Identifier::Global(name)) = head
            && let Some(parameters) = OWNED_TUPLE_WORKER_VARIANTS
                .with(|workers| workers.borrow().get(name.as_ref()).cloned())
            && let Some(tuple) = parameters.into_iter().find_map(|parameter| {
                arguments.get(parameter).and_then(|argument| {
                    (Self::same_type(expression, argument))
                        .then(|| self.owned_tuple_literal(argument))
                        .flatten()
                })
            })
        {
            return Some(tuple);
        }
        arguments.last().and_then(|last| {
            Self::same_type(expression, last)
                .then(|| self.owned_tuple_literal(last))
                .flatten()
        })
    }

    fn owner_pattern<'a>(
        deconstruct: &'a phase::Deconstruct<Closed>,
        clause: &'a phase::MatchClause<Closed>,
        owner: usize,
    ) -> Option<&'a phase::Pattern<Closed>> {
        if Self::local_level(&deconstruct.scrutinee) == Some(owner) {
            return Some(&clause.pattern);
        }
        let Expr::Tuple(_, scrutinee) = strip_ascription(&deconstruct.scrutinee) else {
            return None;
        };
        let Pattern::Tuple(_, pattern) = &clause.pattern else {
            return None;
        };
        scrutinee
            .elements
            .iter()
            .position(|element| Self::local_level(element) == Some(owner))
            .and_then(|index| pattern.elements.get(index))
    }

    /// Find result constructors that can overwrite an exclusively owned input
    /// node. The owner itself must have one use (the match), and the selected
    /// clause must rebuild the same constructor. Other result paths retain their
    /// ordinary representation, so growth and terminator cases stay correct.
    fn owned_data_result_nodes(
        expression: &Expr,
        owner: usize,
        matched: Option<&QualifiedName>,
        out: &mut Vec<usize>,
    ) {
        let expression = strip_ascription(expression);
        if let Some((constructor, arguments)) = Self::constructor_application(expression)
            && !arguments.is_empty()
            && matched.is_some_and(|matched| matched == constructor)
        {
            out.push(expression as *const Expr as usize);
            return;
        }
        match expression {
            Expr::Let(_, binding) => {
                Self::owned_data_result_nodes(&binding.body, owner, matched, out)
            }
            Expr::Sequence(_, sequence) => {
                Self::owned_data_result_nodes(&sequence.and_then, owner, matched, out)
            }
            Expr::If(_, branch) => {
                Self::owned_data_result_nodes(&branch.consequent, owner, matched, out);
                Self::owned_data_result_nodes(&branch.alternate, owner, matched, out);
            }
            Expr::Deconstruct(_, deconstruct) => {
                for clause in &deconstruct.match_clauses {
                    let constructor = Self::owner_pattern(deconstruct, clause, owner)
                        .and_then(|pattern| match pattern {
                            Pattern::Coproduct(_, constructor) => {
                                let Identifier::Global(name) = &constructor.constructor else {
                                    return None;
                                };
                                Some(name.as_ref())
                            }
                            _ => None,
                        })
                        .or(matched);
                    Self::owned_data_result_nodes(&clause.consequent, owner, constructor, out);
                }
            }
            _ => {}
        }
    }

    fn owned_data_worker_variants(&self) -> HashMap<QualifiedName, Vec<usize>> {
        if std::env::var_os("MARM_NO_OWNED_DATA").is_some() {
            return HashMap::default();
        }
        self.workers
            .iter()
            .filter_map(|worker| {
                let parameters = (0..worker.params)
                    .filter(|parameter| {
                        if Self::local_use_count(&worker.body, *parameter) != 1 {
                            return false;
                        }
                        let mut returns = Vec::new();
                        Self::owned_data_result_nodes(&worker.body, *parameter, None, &mut returns);
                        !returns.is_empty()
                    })
                    .collect::<Vec<_>>();
                (!parameters.is_empty()).then(|| (worker.name.clone(), parameters))
            })
            .collect()
    }

    /// Recognize the stricter subset of owned-data rebuilding which can run as
    /// a forward loop.  The result constructor must put a saturated self-call
    /// in its final recursive field, and that call must advance the selected
    /// owner to the recursive binder from the matched input constructor.
    /// Requiring the recursive field to be last preserves field evaluation
    /// order when the recursive call becomes the loop backedge.
    fn owned_data_loop_result(
        expression: &Expr,
        worker: &Worker,
        owner: usize,
        constructor: &QualifiedName,
        recursive_field: usize,
        recursive_binder: usize,
    ) -> bool {
        let expression = strip_ascription(expression);
        if let Some((result_constructor, fields)) = Self::constructor_application(expression) {
            if result_constructor != constructor
                || recursive_field + 1 != fields.len()
                || fields.len() > 4
            {
                return false;
            }
            let Some((called, arguments)) = fields
                .get(recursive_field)
                .and_then(|field| Self::named_application(field))
            else {
                return false;
            };
            return called == &worker.name
                && arguments.len() == worker.params
                && arguments
                    .get(owner)
                    .and_then(|argument| Self::local_level(argument))
                    == Some(recursive_binder);
        }
        match expression {
            Expr::Let(_, binding) => {
                matches!(binding.binder, Identifier::Local(_))
                    && Self::owned_data_loop_result(
                        &binding.body,
                        worker,
                        owner,
                        constructor,
                        recursive_field,
                        recursive_binder,
                    )
            }
            Expr::Sequence(_, sequence) => Self::owned_data_loop_result(
                &sequence.and_then,
                worker,
                owner,
                constructor,
                recursive_field,
                recursive_binder,
            ),
            Expr::If(_, branch) => {
                Self::owned_data_loop_result(
                    &branch.consequent,
                    worker,
                    owner,
                    constructor,
                    recursive_field,
                    recursive_binder,
                ) && Self::owned_data_loop_result(
                    &branch.alternate,
                    worker,
                    owner,
                    constructor,
                    recursive_field,
                    recursive_binder,
                )
            }
            _ => false,
        }
    }

    fn owned_data_loop_clause(
        &self,
        worker: &Worker,
        owner: usize,
        deconstruct: &phase::Deconstruct<Closed>,
        clause: &phase::MatchClause<Closed>,
    ) -> Option<(QualifiedName, usize, usize)> {
        let owner_pattern = Self::owner_pattern(deconstruct, clause, owner)?;
        let owner_type = &owner_pattern.annotation().type_info.inferred_type;
        let Pattern::Coproduct(_, pattern) = owner_pattern else {
            return None;
        };
        let Identifier::Global(constructor) = &pattern.constructor else {
            return None;
        };
        if pattern.arguments.is_empty() || pattern.arguments.len() > 4 {
            return None;
        }
        let recursive = pattern
            .arguments
            .iter()
            .enumerate()
            .filter(|(_, argument)| &argument.annotation().type_info.inferred_type == owner_type)
            .map(|(index, argument)| match argument {
                Pattern::Bind(_, Identifier::Local(LexicalLevel(level))) => Some((index, *level)),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        let [(recursive_field, recursive_binder)] = recursive.as_slice() else {
            return None;
        };
        if !Self::owned_local_is_linear(&clause.consequent, *recursive_binder) {
            return None;
        }
        Self::owned_data_loop_result(
            &clause.consequent,
            worker,
            owner,
            constructor.as_ref(),
            *recursive_field,
            *recursive_binder,
        )
        .then(|| {
            (
                constructor.as_ref().clone(),
                *recursive_field,
                *recursive_binder,
            )
        })
    }

    fn compile_owned_data_loop_fallback(
        &self,
        worker: &Worker,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        write!(code, "{{ Value _od_tail = {}_worker(", c_name(&worker.name))?;
        for parameter in 0..worker.params {
            if parameter != 0 {
                write!(code, ", ")?;
            }
            write!(code, "l{parameter}")?;
        }
        write!(
            code,
            "); if (!_od_started) return _od_tail; \
             set_owned_data_field_fast(_od_parent, _od_parent_field, _od_tail); \
             return _od_root; }}"
        )
    }

    fn compile_owned_data_loop_result(
        &self,
        expression: &Expr,
        worker: &Worker,
        owner: usize,
        constructor: &QualifiedName,
        recursive_field: usize,
        recursive_binder: usize,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        let expression = strip_ascription(expression);
        if let Some((result_constructor, fields)) = Self::constructor_application(expression) {
            debug_assert_eq!(result_constructor, constructor);
            debug_assert_eq!(recursive_field + 1, fields.len());
            let (_, recursive_arguments) = Self::named_application(fields[recursive_field])
                .expect("owned-data loop analysis admitted a non-recursive result field");
            let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
            write!(code, "{{ ")?;
            for (index, field) in fields.iter().take(recursive_field).enumerate() {
                write!(code, "Value _odf{id}_{index} = ")?;
                self.compile_expr(field, code)?;
                write!(code, "; ")?;
            }
            for (index, argument) in recursive_arguments.iter().enumerate() {
                write!(code, "Value _oda{id}_{index} = ")?;
                self.compile_expr(argument, code)?;
                write!(code, "; ")?;
            }
            write!(
                code,
                "if (!_od_started) {{ _od_root = l{owner}; _od_started = true; }} "
            )?;
            write!(
                code,
                "reuse_owned_data{}_fast(l{owner}, {}",
                fields.len(),
                self.constructor_tag(constructor)
            )?;
            for index in 0..fields.len() {
                if index == recursive_field {
                    write!(code, ", _oda{id}_{owner}")?;
                } else {
                    write!(code, ", _odf{id}_{index}")?;
                }
            }
            write!(
                code,
                "); _od_parent = l{owner}; _od_parent_field = {recursive_field}; "
            )?;
            for parameter in 0..worker.params {
                write!(code, "l{parameter} = _oda{id}_{parameter}; ")?;
            }
            return write!(code, "continue; }}");
        }
        match expression {
            Expr::Let(_, binding) => {
                let Identifier::Local(LexicalLevel(level)) = binding.binder else {
                    unreachable!("owned-data loop analysis admitted a non-local let")
                };
                write!(code, "{{ Value l{level} = ")?;
                self.compile_expr(&binding.bound, code)?;
                write!(code, "; ")?;
                self.compile_owned_data_loop_result(
                    &binding.body,
                    worker,
                    owner,
                    constructor,
                    recursive_field,
                    recursive_binder,
                    code,
                )?;
                write!(code, " }}")
            }
            Expr::Sequence(_, sequence) => {
                write!(code, "{{ (void)(")?;
                self.compile_expr(&sequence.this, code)?;
                write!(code, "); ")?;
                self.compile_owned_data_loop_result(
                    &sequence.and_then,
                    worker,
                    owner,
                    constructor,
                    recursive_field,
                    recursive_binder,
                    code,
                )?;
                write!(code, " }}")
            }
            Expr::If(_, branch) => {
                write!(code, "if (as_bool(")?;
                self.compile_expr(&branch.predicate, code)?;
                write!(code, ")) {{ ")?;
                self.compile_owned_data_loop_result(
                    &branch.consequent,
                    worker,
                    owner,
                    constructor,
                    recursive_field,
                    recursive_binder,
                    code,
                )?;
                write!(code, " }} else {{ ")?;
                self.compile_owned_data_loop_result(
                    &branch.alternate,
                    worker,
                    owner,
                    constructor,
                    recursive_field,
                    recursive_binder,
                    code,
                )?;
                write!(code, " }}")
            }
            _ => unreachable!("owned-data loop result changed after analysis"),
        }
    }

    /// Emit an ownership-specialized reconstruction as a forward mutation loop.
    /// Unsupported or terminal clauses delegate the remaining suffix to the
    /// ordinary worker and attach its result to the already rewritten prefix.
    fn compile_owned_data_loop_worker(
        &self,
        worker: &Worker,
        owner: usize,
        code: &mut CodeBuffer,
    ) -> Result<bool, fmt::Error> {
        if std::env::var_os("MARM_NO_OWNED_DATA_LOOPS").is_some() {
            return Ok(false);
        }
        let Expr::Deconstruct(_, deconstruct) = strip_ascription(&worker.body) else {
            return Ok(false);
        };
        let plans = deconstruct
            .match_clauses
            .iter()
            .map(|clause| self.owned_data_loop_clause(worker, owner, deconstruct, clause))
            .collect::<Vec<_>>();
        if plans.iter().all(Option::is_none) {
            return Ok(false);
        }

        let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
        let tuple_plan = if let Expr::Tuple(_, tuple) = strip_ascription(&deconstruct.scrutinee) {
            let locals = (0..tuple.elements.len())
                .map(|index| format!("_od_scrut{id}_{index}"))
                .collect::<Vec<_>>();
            let Some(match_plans) =
                self.plan_direct_tuple_match(&deconstruct.match_clauses, &locals)
            else {
                return Ok(false);
            };
            Some((tuple, locals, match_plans))
        } else {
            None
        };
        write!(
            code,
            "\n  Value _od_root = VInt(0); Value _od_parent = VInt(0); \
             size_t _od_parent_field = 0; bool _od_started = false; for (;;) {{ "
        )?;

        let (scrutinee, match_plans) = if let Some((tuple, locals, match_plans)) = tuple_plan {
            for (local, element) in locals.iter().zip(&tuple.elements) {
                write!(code, "Value {local} = ")?;
                self.compile_expr(element, code)?;
                write!(code, "; ")?;
            }
            (None, Some(match_plans))
        } else {
            let scrutinee = format!("_od_scrut{id}");
            write!(code, "Value {scrutinee} = ")?;
            self.compile_expr(&deconstruct.scrutinee, code)?;
            write!(code, "; ")?;
            (Some(scrutinee), None)
        };

        let mut exhaustive = false;
        for (clause_index, clause) in deconstruct.match_clauses.iter().enumerate() {
            let (tests, binds) = if let Some(match_plans) = &match_plans {
                match_plans[clause_index].clone()
            } else {
                let mut tests = Vec::new();
                let mut binds = Vec::new();
                self.collect_pattern(
                    &clause.pattern,
                    scrutinee.as_deref().expect("single scrutinee"),
                    &mut tests,
                    &mut binds,
                );
                (tests, binds)
            };
            if clause_index != 0 {
                write!(code, " else ")?;
            }
            if tests.is_empty() {
                write!(code, "{{ ")?;
                exhaustive = true;
            } else {
                write!(code, "if ({}) {{ ", tests.join(" && "))?;
            }
            for (level, path) in &binds {
                write!(code, "Value l{level} = {path}; ")?;
            }
            if let Some((constructor, recursive_field, recursive_binder)) = &plans[clause_index] {
                let mut owned_binders = HashSet::default();
                if let Some(pattern) = Self::owner_pattern(deconstruct, clause, owner) {
                    self.collect_owned_spine_pattern_binders(
                        pattern,
                        &pattern.annotation().type_info.inferred_type,
                        &mut owned_binders,
                    );
                }
                let previous = Self::install_owned_spine_locals(owned_binders);
                let result = self.compile_owned_data_loop_result(
                    &clause.consequent,
                    worker,
                    owner,
                    constructor,
                    *recursive_field,
                    *recursive_binder,
                    code,
                );
                Self::restore_owned_spine_locals(previous);
                result?;
            } else {
                self.compile_owned_data_loop_fallback(worker, code)?;
            }
            write!(code, " }}")?;
            if exhaustive {
                break;
            }
        }
        if !exhaustive {
            write!(code, " else {{ match_fail(); }}")?;
        }
        write!(code, " }}\n}}\n\n")?;
        Ok(true)
    }

    /// Prove that two parameters may denote the same recursive node while one
    /// is consumed. Both parameters must be taken apart together, and on every
    /// reachable equal-constructor branch their recursive fields must be passed
    /// in the same positions of the recursive call. The fields are loaded before
    /// that call, so bottom-up replacement cannot invalidate the second view.
    fn owned_data_parameters_are_lockstep(
        &self,
        name: &QualifiedName,
        left: usize,
        right: usize,
    ) -> bool {
        let Some(worker) = self.workers.iter().find(|worker| worker.name == *name) else {
            return false;
        };
        if Self::local_use_count(&worker.body, left) != 1
            || Self::local_use_count(&worker.body, right) != 1
        {
            return false;
        }
        let Expr::Deconstruct(_, deconstruct) = strip_ascription(&worker.body) else {
            return false;
        };
        let Expr::Tuple(_, scrutinee) = strip_ascription(&deconstruct.scrutinee) else {
            return false;
        };
        let Some(left_field) = scrutinee
            .elements
            .iter()
            .position(|element| Self::local_level(element) == Some(left))
        else {
            return false;
        };
        let Some(right_field) = scrutinee
            .elements
            .iter()
            .position(|element| Self::local_level(element) == Some(right))
        else {
            return false;
        };

        deconstruct.match_clauses.iter().all(|clause| {
            let Pattern::Tuple(_, tuple) = &clause.pattern else {
                return false;
            };
            let Some(Pattern::Coproduct(_, left_pattern)) = tuple.elements.get(left_field) else {
                return false;
            };
            let Some(Pattern::Coproduct(_, right_pattern)) = tuple.elements.get(right_field) else {
                return false;
            };
            let (Identifier::Global(left_constructor), Identifier::Global(right_constructor)) =
                (&left_pattern.constructor, &right_pattern.constructor)
            else {
                return false;
            };
            // Aliased values cannot select unequal-constructor clauses.
            if left_constructor != right_constructor {
                return true;
            }
            if left_pattern.arguments.is_empty() && right_pattern.arguments.is_empty() {
                return true;
            }
            let recursive_type = &tuple.elements[left_field]
                .annotation()
                .type_info
                .inferred_type;
            let recursive_binder = |pattern: &phase::Pattern<Closed>| match pattern {
                Pattern::Coproduct(_, constructor) => constructor
                    .arguments
                    .iter()
                    .filter(|argument| {
                        &argument.annotation().type_info.inferred_type == recursive_type
                    })
                    .map(|argument| match argument {
                        Pattern::Bind(_, Identifier::Local(LexicalLevel(level))) => Some(*level),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>(),
                _ => None,
            };
            let Some(left_recursive) = recursive_binder(&tuple.elements[left_field]) else {
                return false;
            };
            let Some(right_recursive) = recursive_binder(&tuple.elements[right_field]) else {
                return false;
            };
            if left_recursive.len() != 1 || right_recursive.len() != 1 {
                return false;
            }
            let left_recursive = left_recursive[0];
            let right_recursive = right_recursive[0];
            if Self::local_use_count(&clause.consequent, left_recursive) != 1
                || Self::local_use_count(&clause.consequent, right_recursive) != 1
            {
                return false;
            }
            fn has_lockstep_call(
                expression: &Expr,
                name: &QualifiedName,
                left: usize,
                right: usize,
                left_recursive: usize,
                right_recursive: usize,
            ) -> bool {
                if let Some((called, arguments)) =
                    lambda_lift::Program::named_application(expression)
                    && called == name
                    && arguments
                        .get(left)
                        .and_then(|arg| lambda_lift::Program::local_level(arg))
                        == Some(left_recursive)
                    && arguments
                        .get(right)
                        .and_then(|arg| lambda_lift::Program::local_level(arg))
                        == Some(right_recursive)
                {
                    return true;
                }
                crate::simplify::children(expression)
                    .into_iter()
                    .any(|child| {
                        has_lockstep_call(child, name, left, right, left_recursive, right_recursive)
                    })
            }
            has_lockstep_call(
                &clause.consequent,
                name,
                left,
                right,
                left_recursive,
                right_recursive,
            )
        })
    }

    fn owned_data_argument_is_exclusive(
        &self,
        name: &QualifiedName,
        arguments: &[&Expr],
        selected: usize,
    ) -> bool {
        if self.owned_spine_argument_is_exclusive(arguments, selected) {
            return true;
        }
        let Some(selected_argument) = arguments.get(selected) else {
            return false;
        };
        let shared_owned_local_is_lockstep = OWNED_SPINE_LOCALS.with(|current| {
            current.borrow().iter().all(|level| {
                Self::local_use_count(selected_argument, *level) == 0
                    || arguments.iter().enumerate().all(|(other, argument)| {
                        other == selected
                            || Self::local_use_count(argument, *level) == 0
                            || self.owned_data_parameters_are_lockstep(name, selected, other)
                    })
            })
        });
        shared_owned_local_is_lockstep
            && arguments.iter().enumerate().all(|(other, argument)| {
                other == selected
                    || !self.expression_is_owned_spine(argument)
                    || Self::constructor_application(argument)
                        .is_some_and(|(_, fields)| fields.is_empty())
                    || self.owned_data_parameters_are_lockstep(name, selected, other)
            })
    }

    fn owned_spine_worker_variants(
        &self,
        fresh: &HashSet<QualifiedName>,
    ) -> HashMap<QualifiedName, Vec<usize>> {
        self.workers
            .iter()
            .filter(|worker| fresh.contains(&worker.name))
            .filter_map(|worker| {
                let parameters = (0..worker.params)
                    .filter(|parameter| Self::local_use_count(&worker.body, *parameter) == 1)
                    .collect::<Vec<_>>();
                (!parameters.is_empty()).then(|| (worker.name.clone(), parameters))
            })
            .collect()
    }

    fn intrinsic_for_name(&self, name: &QualifiedName) -> Option<IntrinsicSemantics> {
        self.term_intrinsics.get(name).copied()
    }

    fn intrinsic_for_expr(&self, expression: &Expr) -> Option<IntrinsicSemantics> {
        self.intrinsic_for_name(expression_name(expression)?)
    }

    fn intrinsic_call<'a>(
        &self,
        expression: &'a Expr,
    ) -> Option<(IntrinsicSemantics, Vec<&'a Expr>)> {
        let mut head = strip_ascription(expression);
        let mut arguments = Vec::new();
        while let Expr::Apply(_, application) = head {
            arguments.push(application.argument.as_ref());
            head = strip_ascription(&application.function);
        }
        arguments.reverse();
        let semantics = self.intrinsic_for_expr(head)?;
        (semantics.arity == arguments.len()).then_some((semantics, arguments))
    }

    fn intrinsic_arguments<'a, const N: usize>(
        &self,
        expression: &'a Expr,
        expected: IntrinsicOperation,
    ) -> Option<[&'a Expr; N]> {
        let (semantics, arguments) = self.intrinsic_call(expression)?;
        (semantics.operation == expected).then(|| arguments.try_into().ok())?
    }

    fn borrowable_slice_arguments<'a>(&self, expression: &'a Expr) -> Option<[&'a Expr; 3]> {
        let (semantics, arguments) = self.intrinsic_call(expression)?;
        let ResultRepresentation::BorrowableSlice {
            owner_argument,
            offset_argument,
            length_argument,
        } = semantics.result
        else {
            return None;
        };
        Some([
            *arguments.get(owner_argument)?,
            *arguments.get(offset_argument)?,
            *arguments.get(length_argument)?,
        ])
    }

    fn mutable_array_element_type<'a>(&self, ty: &'a Type) -> Option<&'a Type> {
        match ty {
            Type::Apply {
                constructor,
                argument,
                ..
            } if matches!(constructor.as_ref(), Type::Constructor(name)
                if self.type_intrinsics.get(name) == Some(&IntrinsicType::MutableArray)) =>
            {
                Some(argument)
            }
            _ => None,
        }
    }

    /// Functions guaranteed to allocate before returning normally.  The seed is
    /// the small set of foreign primitives whose implementation is part of the
    /// runtime ABI; generated direct workers are then propagated to a fixed point.
    /// Unknown/indirect calls remain non-allocating for this proof, which is the
    /// safe direction (their callers retain a poll).
    fn allocation_summaries(&self) -> HashSet<QualifiedName> {
        let mut allocating: HashSet<QualifiedName> = self
            .term_intrinsics
            .iter()
            .filter(|(_, semantics)| semantics.allocation == AllocationEffect::Always)
            .map(|(name, _)| name.clone())
            .collect();
        // A loopified worker that borrows even one slice is conservatively not
        // advertised as allocating. Its raw_sub may have been the only proof,
        // and the worker's own amortised poll counter restarts on each call: a
        // caller repeatedly invoking it for fewer than 4096 inner iterations
        // therefore still needs its own safepoint.
        let scalar_replacing: HashSet<_> = if std::env::var_os("MARM_NO_LOOPIFY").is_none() {
            self.workers
                .iter()
                .filter(|Worker { name, params, body }| {
                    self.has_tail_self_call(SelfCall::Named(name), *params, body)
                        && !self
                            .borrowed_slice_places(SelfCall::Named(name), *params, body)
                            .is_empty()
                })
                .map(|worker| worker.name.clone())
                .collect()
        } else {
            HashSet::default()
        };

        loop {
            let additions: Vec<_> = self
                .workers
                .iter()
                .filter(|worker| {
                    !allocating.contains(&worker.name)
                        && !scalar_replacing.contains(&worker.name)
                        && self.expression_must_allocate(&worker.body, &allocating)
                })
                .map(|worker| worker.name.clone())
                .collect();
            if additions.is_empty() {
                break;
            }
            allocating.extend(additions);
        }
        allocating
    }

    /// True only when every normal evaluation of `expression` crosses a known
    /// allocation.  Branches use conjunction; sequentially evaluated children
    /// use disjunction.  We intentionally do not infer allocation from source
    /// constructors here because later codegen can erase or scalarise them.
    fn expression_must_allocate(
        &self,
        expression: &Expr,
        allocating: &HashSet<QualifiedName>,
    ) -> bool {
        let direct_call_allocates = || {
            let mut arity = 0usize;
            let mut head = expression;
            while let Expr::Apply(_, application) = head {
                arity += 1;
                head = &application.function;
            }
            matches!(head, Expr::Variable(_, Identifier::Global(name))
                if self.arities.get(name.as_ref()) == Some(&arity)
                    && allocating.contains(name.as_ref()))
        };

        match expression {
            Expr::Ascription(_, the) => {
                self.expression_must_allocate(&the.ascribed_tree, allocating)
            }
            Expr::Let(_, the) => {
                self.expression_must_allocate(&the.bound, allocating)
                    || self.expression_must_allocate(&the.body, allocating)
            }
            Expr::Sequence(_, the) => {
                self.expression_must_allocate(&the.this, allocating)
                    || self.expression_must_allocate(&the.and_then, allocating)
            }
            Expr::If(_, the) => {
                self.expression_must_allocate(&the.predicate, allocating)
                    || (self.expression_must_allocate(&the.consequent, allocating)
                        && self.expression_must_allocate(&the.alternate, allocating))
            }
            Expr::Deconstruct(_, the) => {
                self.expression_must_allocate(&the.scrutinee, allocating)
                    || (!the.match_clauses.is_empty()
                        && the.match_clauses.iter().all(|clause| {
                            self.expression_must_allocate(&clause.consequent, allocating)
                        }))
            }
            Expr::Apply(..) if direct_call_allocates() => true,
            _ => crate::simplify::children(expression)
                .into_iter()
                .any(|child| self.expression_must_allocate(child, allocating)),
        }
    }

    /// Prove that each tail self-call (the `continue` emitted by `compile_tail`)
    /// is preceded on that path by a guaranteed allocation.  Exit paths need no
    /// proof.  This is stronger than “the loop may call an allocator”: one cold
    /// allocating branch must not suppress the only safepoint on another cycle.
    fn back_edges_are_safepointed(
        &self,
        target: SelfCall<'_>,
        arity: usize,
        expression: &Expr,
        allocating: &HashSet<QualifiedName>,
        already_allocated: bool,
    ) -> bool {
        if self.is_self_call(target, arity, expression) {
            // `compile_tail` evaluates every new argument before reassigning the
            // loop parameters.  The self-call itself is erased into `continue`,
            // so never count the callee summary here.
            let mut head = expression;
            let mut argument_allocates = false;
            while let Expr::Apply(_, application) = head {
                argument_allocates |=
                    self.expression_must_allocate(&application.argument, allocating);
                head = &application.function;
            }
            return already_allocated || argument_allocates;
        }

        match expression {
            Expr::Ascription(_, the) => self.back_edges_are_safepointed(
                target,
                arity,
                &the.ascribed_tree,
                allocating,
                already_allocated,
            ),
            Expr::Let(_, the) => self.back_edges_are_safepointed(
                target,
                arity,
                &the.body,
                allocating,
                already_allocated || self.expression_must_allocate(&the.bound, allocating),
            ),
            Expr::Sequence(_, the) => self.back_edges_are_safepointed(
                target,
                arity,
                &the.and_then,
                allocating,
                already_allocated || self.expression_must_allocate(&the.this, allocating),
            ),
            Expr::If(_, the) => {
                let before_branch =
                    already_allocated || self.expression_must_allocate(&the.predicate, allocating);
                self.back_edges_are_safepointed(
                    target,
                    arity,
                    &the.consequent,
                    allocating,
                    before_branch,
                ) && self.back_edges_are_safepointed(
                    target,
                    arity,
                    &the.alternate,
                    allocating,
                    before_branch,
                )
            }
            Expr::Deconstruct(_, the) => {
                let before_clause =
                    already_allocated || self.expression_must_allocate(&the.scrutinee, allocating);
                the.match_clauses.iter().all(|clause| {
                    self.back_edges_are_safepointed(
                        target,
                        arity,
                        &clause.consequent,
                        allocating,
                        before_clause,
                    )
                })
            }
            // `compile_tail` returns every other tail expression; there is no
            // back-edge on this path.
            _ => true,
        }
    }

    fn loop_needs_poll(
        &self,
        target: SelfCall<'_>,
        arity: usize,
        expression: &Expr,
        allocating: &HashSet<QualifiedName>,
    ) -> bool {
        !self.back_edges_are_safepointed(target, arity, expression, allocating, false)
    }

    /// Small direct workers called from a generated loop are statically hot even
    /// without PGO.  Clang's default threshold narrowly rejects some of these
    /// after the worker expands an immediately-called local loop (notably the
    /// FNV hash worker), leaving a call and a stack closure in the row path.
    ///
    /// Keep the policy structural: collect saturated direct calls from every
    /// loopified body, then apply a conservative source-IR size budget.  Genuine
    /// self-recursive workers are excluded -- loopification, not recursive
    /// inlining, is what makes those constant-stack.
    fn c_inline_workers(&self) -> HashSet<QualifiedName> {
        if std::env::var_os("MARM_NO_C_INLINE").is_some() {
            return HashSet::default();
        }

        fn collect_calls(
            expression: &Expr,
            arities: &HashMap<QualifiedName, usize>,
            calls: &mut HashSet<QualifiedName>,
        ) {
            if let Expr::Apply(..) = expression {
                let mut arity = 0usize;
                let mut head = expression;
                while let Expr::Apply(_, application) = head {
                    arity += 1;
                    head = &application.function;
                }
                if let Expr::Variable(_, Identifier::Global(name)) = head
                    && arities.get(name.as_ref()) == Some(&arity)
                {
                    calls.insert(name.as_ref().clone());
                }
            }
            for child in crate::simplify::children(expression) {
                collect_calls(child, arities, calls);
            }
        }

        fn collect_back_edge_calls(
            program: &lambda_lift::Program,
            target: SelfCall<'_>,
            arity: usize,
            expression: &Expr,
            calls: &mut HashSet<QualifiedName>,
        ) {
            match expression {
                Expr::Ascription(_, the) => {
                    collect_back_edge_calls(program, target, arity, &the.ascribed_tree, calls)
                }
                Expr::Let(_, the) => {
                    if program.has_tail_self_call(target, arity, &the.body) {
                        collect_calls(&the.bound, &program.arities, calls);
                        collect_back_edge_calls(program, target, arity, &the.body, calls);
                    }
                }
                Expr::Sequence(_, the) => {
                    if program.has_tail_self_call(target, arity, &the.and_then) {
                        collect_calls(&the.this, &program.arities, calls);
                        collect_back_edge_calls(program, target, arity, &the.and_then, calls);
                    }
                }
                Expr::If(_, the) => {
                    let consequent_loops =
                        program.has_tail_self_call(target, arity, &the.consequent);
                    let alternate_loops = program.has_tail_self_call(target, arity, &the.alternate);
                    if consequent_loops || alternate_loops {
                        collect_calls(&the.predicate, &program.arities, calls);
                    }
                    if consequent_loops {
                        collect_back_edge_calls(program, target, arity, &the.consequent, calls);
                    }
                    if alternate_loops {
                        collect_back_edge_calls(program, target, arity, &the.alternate, calls);
                    }
                }
                Expr::Deconstruct(_, the) => {
                    let looping_clauses = the
                        .match_clauses
                        .iter()
                        .filter(|clause| {
                            program.has_tail_self_call(target, arity, &clause.consequent)
                        })
                        .collect::<Vec<_>>();
                    if !looping_clauses.is_empty() {
                        collect_calls(&the.scrutinee, &program.arities, calls);
                        for clause in looping_clauses {
                            collect_back_edge_calls(
                                program,
                                target,
                                arity,
                                &clause.consequent,
                                calls,
                            );
                        }
                    }
                }
                _ if program.is_self_call(target, arity, expression) => {
                    // The arguments execute before the generated `continue`; the
                    // self callee does not.  Inspecting only the arguments also
                    // avoids ever selecting a recursive worker for inlining.
                    let mut head = expression;
                    while let Expr::Apply(_, application) = head {
                        collect_calls(&application.argument, &program.arities, calls);
                        head = &application.function;
                    }
                }
                _ => {}
            }
        }

        let mut hot = HashSet::default();
        for LiftedFunction { code, .. } in &self.functions {
            if self.has_tail_self_call(SelfCall::SelfRef, 1, code) {
                collect_back_edge_calls(self, SelfCall::SelfRef, 1, code, &mut hot);
            }
        }
        for Worker { name, params, body } in &self.workers {
            if self.has_tail_self_call(SelfCall::Named(name), *params, body) {
                collect_back_edge_calls(self, SelfCall::Named(name), *params, body, &mut hot);
            }
        }
        for ChainWorker { arity, body, .. } in &self.chain_workers {
            if self.has_tail_self_call(SelfCall::SelfRef, *arity, body) {
                collect_back_edge_calls(self, SelfCall::SelfRef, *arity, body, &mut hot);
            }
        }

        let budget = c_inline_budget();
        self.workers
            .iter()
            .filter(|Worker { name, params, body }| {
                hot.contains(name)
                    && c_expr_size(body) <= budget
                    && !self.has_tail_self_call(SelfCall::Named(name), *params, body)
            })
            .map(|worker| worker.name.clone())
            .collect()
    }

    fn borrowed_slice_places(
        &self,
        target: SelfCall<'_>,
        arity: usize,
        expression: &Expr,
    ) -> HashMap<usize, String> {
        if std::env::var_os("MARM_NO_BORROWED_SLICES").is_some() {
            return HashMap::default();
        }

        fn collect(
            program: &lambda_lift::Program,
            target: SelfCall<'_>,
            arity: usize,
            expression: &Expr,
            tail: bool,
            places: &mut HashMap<usize, String>,
        ) {
            if tail && program.is_self_call(target, arity, expression) {
                // A slice passed around the back edge must materialise before
                // this frame's reusable slot is overwritten, so borrowing it
                // would only add a tag/barrier round trip.
                return;
            }
            if let Expr::Apply(_, application) = strip_ascription(expression)
                && program.borrowable_slice_arguments(expression).is_some()
            {
                let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
                places.insert(application as *const _ as usize, format!("_bs{id}"));
            }
            match expression {
                Expr::Ascription(_, the) => {
                    collect(program, target, arity, &the.ascribed_tree, tail, places)
                }
                Expr::Let(_, the) => {
                    collect(program, target, arity, &the.bound, false, places);
                    collect(program, target, arity, &the.body, tail, places);
                }
                Expr::Sequence(_, the) => {
                    collect(program, target, arity, &the.this, false, places);
                    collect(program, target, arity, &the.and_then, tail, places);
                }
                Expr::If(_, the) => {
                    collect(program, target, arity, &the.predicate, false, places);
                    collect(program, target, arity, &the.consequent, tail, places);
                    collect(program, target, arity, &the.alternate, tail, places);
                }
                Expr::Deconstruct(_, the) => {
                    collect(program, target, arity, &the.scrutinee, false, places);
                    for clause in &the.match_clauses {
                        collect(program, target, arity, &clause.consequent, tail, places);
                    }
                }
                // A raw slice created inside an opaque tail expression may be
                // part of the returned value. Keep the conservative heap form.
                _ if tail => {}
                _ => {
                    for child in crate::simplify::children(expression) {
                        collect(program, target, arity, child, false, places);
                    }
                }
            }
        }

        let mut places = HashMap::default();
        collect(self, target, arity, expression, true, &mut places);
        places
    }

    fn install_borrowed_slice_places(places: HashMap<usize, String>) -> HashMap<usize, String> {
        BORROWED_SLICE_PLACES.with(|current| std::mem::replace(&mut *current.borrow_mut(), places))
    }

    fn restore_borrowed_slice_places(previous: HashMap<usize, String>) {
        BORROWED_SLICE_PLACES.with(|current| *current.borrow_mut() = previous);
    }

    fn invariant_loop_parameters(
        &self,
        target: SelfCall<'_>,
        arity: usize,
        expression: &Expr,
    ) -> Vec<bool> {
        fn visit(
            program: &lambda_lift::Program,
            target: SelfCall<'_>,
            arity: usize,
            expression: &Expr,
            invariant: &mut [bool],
        ) {
            match expression {
                Expr::Ascription(_, the) => {
                    visit(program, target, arity, &the.ascribed_tree, invariant)
                }
                Expr::If(_, the) => {
                    visit(program, target, arity, &the.consequent, invariant);
                    visit(program, target, arity, &the.alternate, invariant);
                }
                Expr::Let(_, the) => visit(program, target, arity, &the.body, invariant),
                Expr::Sequence(_, the) => visit(program, target, arity, &the.and_then, invariant),
                Expr::Deconstruct(_, the) => {
                    for clause in &the.match_clauses {
                        visit(program, target, arity, &clause.consequent, invariant);
                    }
                }
                _ if program.is_self_call(target, arity, expression) => {
                    let mut arguments = Vec::new();
                    let mut head = expression;
                    while let Expr::Apply(_, application) = head {
                        arguments.push(application.argument.as_ref());
                        head = &application.function;
                    }
                    arguments.reverse();
                    let all_parameters_invariant = vec![true; arity];
                    for (index, argument) in arguments.into_iter().enumerate() {
                        if lambda_lift::Program::immutable_slice_source(
                            argument,
                            &all_parameters_invariant,
                            &HashMap::default(),
                        ) != Some(ImmutableSliceSource::Local(index))
                        {
                            invariant[index] = false;
                        }
                    }
                }
                _ => {}
            }
        }

        let mut invariant = vec![true; arity];
        visit(self, target, arity, expression, &mut invariant);
        invariant
    }

    fn immutable_slice_source(
        expression: &Expr,
        invariant_parameters: &[bool],
        aliases: &HashMap<usize, ImmutableSliceSource>,
    ) -> Option<ImmutableSliceSource> {
        fn provenance(
            expression: &Expr,
            aliases: &HashMap<usize, ImmutableSliceSource>,
        ) -> Option<ImmutableSliceSource> {
            match strip_ascription(expression) {
                Expr::Variable(_, Identifier::Local(LexicalLevel(level))) => aliases
                    .get(level)
                    .copied()
                    .or(Some(ImmutableSliceSource::Local(*level))),
                Expr::Variable(_, Identifier::Captured(capture)) => {
                    Some(ImmutableSliceSource::Captured(capture.index()))
                }
                // Elaboration uses single-arm matches to introduce a type-erased
                // alias. Follow that identity wrapper both in byte reads and on a
                // recursive back-edge.
                Expr::Deconstruct(_, deconstruct)
                    if deconstruct.match_clauses.len() == 1
                        && matches!(
                            &deconstruct.match_clauses[0].pattern,
                            Pattern::Bind(_, Identifier::Local(_))
                        ) =>
                {
                    let source = provenance(&deconstruct.scrutinee, aliases)?;
                    let Pattern::Bind(_, Identifier::Local(LexicalLevel(level))) =
                        &deconstruct.match_clauses[0].pattern
                    else {
                        unreachable!()
                    };
                    let mut nested = aliases.clone();
                    nested.insert(*level, source);
                    provenance(&deconstruct.match_clauses[0].consequent, &nested)
                }
                Expr::Let(_, binding) => {
                    let source = provenance(&binding.bound, aliases)?;
                    let Identifier::Local(LexicalLevel(level)) = binding.binder else {
                        return None;
                    };
                    let mut nested = aliases.clone();
                    nested.insert(level, source);
                    provenance(&binding.body, &nested)
                }
                _ => None,
            }
        }

        match provenance(expression, aliases)? {
            source @ ImmutableSliceSource::Local(level)
                if invariant_parameters.get(level) == Some(&true) =>
            {
                Some(source)
            }
            source @ ImmutableSliceSource::Captured(_) => Some(source),
            _ => None,
        }
    }

    fn immutable_slice_bases(
        &self,
        target: SelfCall<'_>,
        arity: usize,
        expression: &Expr,
    ) -> Vec<ImmutableSliceBase> {
        fn collect(
            program: &lambda_lift::Program,
            expression: &Expr,
            invariant_parameters: &[bool],
            sources: &mut HashSet<ImmutableSliceSource>,
            aliases: &mut HashMap<usize, ImmutableSliceSource>,
            seen_aliases: &mut HashMap<ImmutableSliceSource, HashSet<ImmutableSliceSource>>,
        ) {
            if let Some((semantics, arguments)) = program.intrinsic_call(expression)
                && matches!(
                    semantics.operation,
                    IntrinsicOperation::BytesGetU8 | IntrinsicOperation::BytesGetU64Le
                )
                && let Some(source) = lambda_lift::Program::immutable_slice_source(
                    arguments[0],
                    invariant_parameters,
                    aliases,
                )
            {
                sources.insert(source);
            }

            match strip_ascription(expression) {
                Expr::Ascription(_, the) => collect(
                    program,
                    &the.ascribed_tree,
                    invariant_parameters,
                    sources,
                    aliases,
                    seen_aliases,
                ),
                Expr::Let(_, binding) => {
                    collect(
                        program,
                        &binding.bound,
                        invariant_parameters,
                        sources,
                        aliases,
                        seen_aliases,
                    );
                    let source = lambda_lift::Program::immutable_slice_source(
                        &binding.bound,
                        invariant_parameters,
                        aliases,
                    );
                    let Identifier::Local(LexicalLevel(level)) = binding.binder else {
                        return;
                    };
                    let previous = source.and_then(|source| {
                        seen_aliases
                            .entry(source)
                            .or_default()
                            .insert(ImmutableSliceSource::Local(level));
                        aliases.insert(level, source)
                    });
                    collect(
                        program,
                        &binding.body,
                        invariant_parameters,
                        sources,
                        aliases,
                        seen_aliases,
                    );
                    if let Some(previous) = previous {
                        aliases.insert(level, previous);
                    } else {
                        aliases.remove(&level);
                    }
                }
                Expr::Deconstruct(_, deconstruct) => {
                    collect(
                        program,
                        &deconstruct.scrutinee,
                        invariant_parameters,
                        sources,
                        aliases,
                        seen_aliases,
                    );
                    let source = lambda_lift::Program::immutable_slice_source(
                        &deconstruct.scrutinee,
                        invariant_parameters,
                        aliases,
                    );
                    for clause in &deconstruct.match_clauses {
                        // Ask the existing representation-aware pattern planner
                        // whether this binds the complete value unchanged. In
                        // particular, `Bytes raw` is an erased newtype; ordinary
                        // constructors and tuples produce a field/projection path
                        // and are correctly rejected here.
                        let mut tests = Vec::new();
                        let mut binds = Vec::new();
                        program.collect_pattern(
                            &clause.pattern,
                            "_slice_source",
                            &mut tests,
                            &mut binds,
                        );
                        let bound_level = match binds.as_slice() {
                            [(level, path)] if tests.is_empty() && path == "_slice_source" => {
                                Some(*level)
                            }
                            _ => None,
                        };
                        let previous = source.zip(bound_level).and_then(|(source, level)| {
                            seen_aliases
                                .entry(source)
                                .or_default()
                                .insert(ImmutableSliceSource::Local(level));
                            aliases
                                .insert(level, source)
                                .map(|previous| (level, previous))
                        });
                        collect(
                            program,
                            &clause.consequent,
                            invariant_parameters,
                            sources,
                            aliases,
                            seen_aliases,
                        );
                        if let Some((level, previous)) = previous {
                            aliases.insert(level, previous);
                        } else if let Some(level) = bound_level {
                            aliases.remove(&level);
                        }
                    }
                }
                _ => {
                    for child in crate::simplify::children(expression) {
                        collect(
                            program,
                            child,
                            invariant_parameters,
                            sources,
                            aliases,
                            seen_aliases,
                        );
                    }
                }
            }
        }

        if std::env::var_os("MARM_NO_SLICE_BASE_CACHE").is_some() {
            return Vec::new();
        }
        let invariant_parameters = self.invariant_loop_parameters(target, arity, expression);
        let mut sources = HashSet::default();
        let mut aliases = HashMap::default();
        let mut seen_aliases = HashMap::default();
        collect(
            self,
            expression,
            &invariant_parameters,
            &mut sources,
            &mut aliases,
            &mut seen_aliases,
        );
        let mut sources = sources.into_iter().collect::<Vec<_>>();
        sources.sort();
        sources
            .into_iter()
            .map(|source| {
                let value = match source {
                    ImmutableSliceSource::Local(level) => format!("l{level}"),
                    ImmutableSliceSource::Captured(index) => Self::current_capture_place(index)
                        .map_or_else(
                            || format!("env_get(self, {index})"),
                            |place| {
                                debug_assert_eq!(place.width, 1);
                                format!("env_get(self, {})", place.offset)
                            },
                        ),
                };
                let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
                let mut aliases = seen_aliases
                    .remove(&source)
                    .unwrap_or_default()
                    .into_iter()
                    .collect::<Vec<_>>();
                aliases.sort();
                ImmutableSliceBase {
                    source,
                    value,
                    name: format!("_ib{id}"),
                    aliases,
                }
            })
            .collect()
    }

    fn install_immutable_slice_bases(
        bases: &[ImmutableSliceBase],
    ) -> HashMap<ImmutableSliceSource, String> {
        let mut places = HashMap::default();
        for base in bases {
            places.insert(base.source, base.name.clone());
            for alias in &base.aliases {
                places.insert(*alias, base.name.clone());
            }
        }
        IMMUTABLE_SLICE_BASES.with(|current| std::mem::replace(&mut *current.borrow_mut(), places))
    }

    fn restore_immutable_slice_bases(previous: HashMap<ImmutableSliceSource, String>) {
        IMMUTABLE_SLICE_BASES.with(|current| *current.borrow_mut() = previous);
    }

    fn static_int_initializer(expression: &Expr) -> Option<String> {
        if std::env::var_os("MARM_NO_STATIC_INT_GLOBALS").is_some() {
            return None;
        }
        let Expr::Constant(_, Literal::Int(value)) = strip_ascription(expression) else {
            return None;
        };
        Some(format!("{{((uint64_t)(int64_t){value} << 1) | IMM_TAG}}"))
    }

    // Emit a complete, self-contained C translation unit: every lifted lambda
    // becomes a `Value f(Value self, Value arg)` function, every top-level
    // definition a `Value` global initialised once in `startup`, and `main`
    // runs the program's `start` entry point. Builtin definitions are omitted --
    // the runtime (`c/runtime.c`) provides them.
    pub fn generate_code(&self, out: &mut CodeBuffer) -> fmt::Result {
        self.generate_code_for(out, CEntryPoint::Process)
    }

    pub fn generate_code_for(&self, out: &mut CodeBuffer, entry_point: CEntryPoint) -> fmt::Result {
        let owned_tuple_steps = self.owned_tuple_step_workers();
        let owned_product_data_steps = self.owned_product_data_step_workers();
        let owned_tuple_variants = self.owned_tuple_worker_variants();
        let owned_recursive_eliminators = self.owned_recursive_eliminators(&owned_tuple_variants);
        OWNED_PRODUCT_DATA_STEP_WORKERS
            .with(|current| *current.borrow_mut() = owned_product_data_steps.clone());
        OWNED_RECURSIVE_ELIMINATORS
            .with(|current| *current.borrow_mut() = owned_recursive_eliminators.clone());
        let fresh_spines = self.fresh_spine_workers();
        FRESH_SPINE_WORKERS.with(|current| *current.borrow_mut() = fresh_spines.clone());
        let owned_rebuild_variants = self.owned_rebuild_worker_variants(&fresh_spines);
        let owned_data_variants = self.owned_data_worker_variants();
        let owned_spine_preserving = self.owned_spine_preserving_workers();
        let owned_spine_worker_variants = self.owned_spine_worker_variants(&fresh_spines);
        if std::env::var_os("MARM_DUMP_OWNED_SPINES").is_some() {
            for name in &fresh_spines {
                eprintln!("[owned-spine] fresh {name}");
            }
        }
        OWNED_REBUILD_WORKER_VARIANTS
            .with(|current| *current.borrow_mut() = owned_rebuild_variants.clone());
        OWNED_TUPLE_STEP_WORKERS.with(|current| *current.borrow_mut() = owned_tuple_steps.clone());
        OWNED_TUPLE_WORKER_VARIANTS
            .with(|current| *current.borrow_mut() = owned_tuple_variants.clone());
        OWNED_DATA_WORKER_VARIANTS
            .with(|current| *current.borrow_mut() = owned_data_variants.clone());
        OWNED_SPINE_PRESERVING_WORKERS
            .with(|current| *current.borrow_mut() = owned_spine_preserving);
        OWNED_SPINE_WORKER_VARIANTS
            .with(|current| *current.borrow_mut() = owned_spine_worker_variants.clone());
        OWNED_DATA_RETURNS.with(|current| current.borrow_mut().clear());
        OWNED_RECURSIVE_COMBINE_CALLS.with(|current| current.borrow_mut().clear());
        OWNED_TUPLE_RETURNS.with(|current| current.borrow_mut().clear());
        OWNED_TUPLE_LOCALS.with(|current| current.borrow_mut().clear());
        OWNED_SPINE_LOCALS.with(|current| current.borrow_mut().clear());
        DYNAMIC_OWNED_SPINE_LOCALS.with(|current| current.borrow_mut().clear());
        let c_inline_workers = self.c_inline_workers();
        let allocating = self.allocation_summaries();
        writeln!(out, "#include \"runtime.h\"")?;
        writeln!(out, "#include \"gc.h\"\n")?;

        // Forward declarations, so functions and globals can reference each
        // other (and themselves) regardless of definition order.
        for LiftedFunction { name, .. } in &self.functions {
            writeln!(out, "Value {}(Value self, Value l0);", c_name(name))?;
        }
        for Worker { name, params, .. } in &self.workers {
            let signature = vec!["Value"; *params].join(", ");
            let inline = if c_inline_workers.contains(name) {
                "MARM_ALWAYS_INLINE "
            } else {
                ""
            };
            let intrinsic = self
                .intrinsic_for_name(name)
                .map_or("", IntrinsicSemantics::c_attribute);
            writeln!(
                out,
                "{intrinsic}{inline}Value {}_worker({});",
                c_name(name),
                signature
            )?;
            if owned_rebuild_variants.contains(name) {
                debug_assert_eq!(*params, 1);
                writeln!(out, "Value {}_owned_rebuild_worker(Value);", c_name(name))?;
            }
            if let Some(parameters) = owned_tuple_variants.get(name) {
                for parameter in parameters {
                    writeln!(
                        out,
                        "Value {}_owned_tuple_{}_worker({});",
                        c_name(name),
                        parameter,
                        signature
                    )?;
                }
            }
            if let Some(variant) = owned_recursive_eliminators.get(name) {
                writeln!(
                    out,
                    "Value {}_owned_tuple_{}_data_{}_worker({});",
                    c_name(name),
                    variant.product_parameter,
                    variant.input_parameter,
                    signature
                )?;
            }
            if let Some(parameters) = owned_data_variants.get(name) {
                for parameter in parameters {
                    writeln!(
                        out,
                        "Value {}_owned_data_{}_worker({});",
                        c_name(name),
                        parameter,
                        signature
                    )?;
                }
            }
            if let Some(parameters) = owned_spine_worker_variants.get(name) {
                for parameter in parameters {
                    writeln!(
                        out,
                        "Value {}_owned_spine_{}_worker({});",
                        c_name(name),
                        parameter,
                        signature
                    )?;
                }
            }
        }
        for ChainWorker { head, .. } in &self.chain_workers {
            writeln!(
                out,
                "Value {}_uworker(Value self, Value *args);",
                c_name(head)
            )?;
            if owned_tuple_steps.contains_key(head) {
                writeln!(
                    out,
                    "Value {}_owned_tuple_uworker(Value self, Value *args);",
                    c_name(head)
                )?;
            }
            if owned_product_data_steps.contains_key(head) {
                writeln!(
                    out,
                    "Value {}_owned_tuple_data_uworker(Value self, Value *args, Value owned_data);",
                    c_name(head)
                )?;
            }
        }
        for TopLevelBinding { name, value, .. } in &self.globals {
            if !is_builtin(name) {
                if let Some(initializer) = Self::static_int_initializer(value) {
                    writeln!(out, "static const Value {} = {initializer};", c_name(name))?;
                } else {
                    writeln!(out, "Value {};", c_name(name))?;
                }
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
                    let intrinsic = self
                        .intrinsic_for_name(name)
                        .map_or("", IntrinsicSemantics::c_attribute);
                    writeln!(
                        out,
                        "{intrinsic}extern Value {0}_worker({1});",
                        c_name(name),
                        params
                    )?;
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
                let borrowed = self.borrowed_slice_places(SelfCall::SelfRef, 1, code);
                let immutable_bases = self.immutable_slice_bases(SelfCall::SelfRef, 1, code);
                let borrows_slices = !borrowed.is_empty();
                let mut slots = borrowed.values().cloned().collect::<Vec<_>>();
                slots.sort();
                let previous = Self::install_borrowed_slice_places(borrowed);
                let previous_bases = Self::install_immutable_slice_bases(&immutable_bases);
                let mut body = CodeBuffer::default();
                let result = self.compile_tail(SelfCall::SelfRef, 1, code, &mut body);
                Self::restore_immutable_slice_bases(previous_bases);
                Self::restore_borrowed_slice_places(previous);
                result?;
                let needs_poll =
                    borrows_slices || self.loop_needs_poll(SelfCall::SelfRef, 1, code, &allocating);
                let slots = slots
                    .iter()
                    .map(|slot| format!("_Alignas(MARM_VALUE_ALIGNMENT) Slice {slot}; "))
                    .collect::<String>();
                let bases = immutable_bases
                    .iter()
                    .map(|base| {
                        format!("const uint8_t *{} = slice_ptr({}); ", base.name, base.value)
                    })
                    .collect::<String>();
                write!(
                    out,
                    "  {slots}{bases}{}for (;;) {{ {}{body} }}\n}}\n\n",
                    poll_decl(needs_poll),
                    back_edge_poll(needs_poll)
                )?;
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
            if std::env::var_os("MARM_DUMP_C_INLINE").is_some() {
                eprintln!(
                    "[c-inline] worker {name} nodes={} selected={}",
                    c_expr_size(body),
                    c_inline_workers.contains(name)
                );
            }
            let signature = (0..*params)
                .map(|i| format!("Value l{i}"))
                .collect::<Vec<_>>()
                .join(", ");
            let inline = if c_inline_workers.contains(name) {
                "MARM_ALWAYS_INLINE "
            } else {
                ""
            };
            let intrinsic = self
                .intrinsic_for_name(name)
                .map_or("", IntrinsicSemantics::c_attribute);
            writeln!(
                out,
                "{intrinsic}{inline}Value {}_worker({}) {{",
                c_name(name),
                signature
            )?;
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
                let borrowed = self.borrowed_slice_places(SelfCall::Named(name), *params, body);
                let immutable_bases =
                    self.immutable_slice_bases(SelfCall::Named(name), *params, body);
                let borrows_slices = !borrowed.is_empty();
                let mut slots = borrowed.values().cloned().collect::<Vec<_>>();
                slots.sort();
                let previous = Self::install_borrowed_slice_places(borrowed);
                let previous_bases = Self::install_immutable_slice_bases(&immutable_bases);
                let mut emitted = CodeBuffer::default();
                let result = self.compile_tail(SelfCall::Named(name), *params, body, &mut emitted);
                Self::restore_immutable_slice_bases(previous_bases);
                Self::restore_borrowed_slice_places(previous);
                result?;
                let needs_poll = borrows_slices
                    || self.loop_needs_poll(SelfCall::Named(name), *params, body, &allocating);
                let slots = slots
                    .iter()
                    .map(|slot| format!("_Alignas(MARM_VALUE_ALIGNMENT) Slice {slot}; "))
                    .collect::<String>();
                let bases = immutable_bases
                    .iter()
                    .map(|base| {
                        format!("const uint8_t *{} = slice_ptr({}); ", base.name, base.value)
                    })
                    .collect::<String>();
                write!(
                    out,
                    "\n  {slots}{bases}{}for (;;) {{ {}{emitted} }}\n}}\n\n",
                    poll_decl(needs_poll),
                    back_edge_poll(needs_poll)
                )?;
            } else {
                let never_returns = self
                    .intrinsic_for_name(name)
                    .is_some_and(|semantics| semantics.control_flow == ControlFlow::NeverReturns);
                if never_returns {
                    write!(out, "\n  ")?;
                    self.compile_expr(body, out)?;
                    writeln!(out, ";\n  MARM_UNREACHABLE();\n}}\n")?;
                } else {
                    write!(out, "\n  return ")?;
                    self.compile_expr(body, out)?;
                    writeln!(out, ";\n}}\n")?;
                }
            }
        }

        // Ownership-specialized entries are ordinary workers with one tuple
        // parameter marked exclusive. Calls and returns propagate that fact;
        // no source function or data type is named by this transformation.
        for Worker { name, params, body } in &self.workers {
            let Some(parameters) = owned_tuple_variants.get(name) else {
                continue;
            };
            let signature = (0..*params)
                .map(|i| format!("Value l{i}"))
                .collect::<Vec<_>>()
                .join(", ");
            for parameter in parameters {
                writeln!(
                    out,
                    "Value {}_owned_tuple_{}_worker({}) {{",
                    c_name(name),
                    parameter,
                    signature
                )?;
                for i in 0..*params {
                    write!(out, "  (void)l{i};")?;
                }
                let previous = OWNED_TUPLE_LOCALS.with(|owned| {
                    let previous = owned.borrow().clone();
                    owned.borrow_mut().insert(*parameter);
                    previous
                });
                write!(out, "\n  return ")?;
                let result = self.compile_expr(body, out);
                OWNED_TUPLE_LOCALS.with(|owned| *owned.borrow_mut() = previous);
                result?;
                writeln!(out, ";\n}}\n")?;
            }
        }

        // A recursive eliminator may own both its product accumulator and its
        // recursive input. Each combine call receives the consumed input node as
        // storage for one nested recursive-data result.
        for Worker { name, params, body } in &self.workers {
            let Some(variant) = owned_recursive_eliminators.get(name) else {
                continue;
            };
            let signature = (0..*params)
                .map(|i| format!("Value l{i}"))
                .collect::<Vec<_>>()
                .join(", ");
            writeln!(
                out,
                "Value {}_owned_tuple_{}_data_{}_worker({}) {{",
                c_name(name),
                variant.product_parameter,
                variant.input_parameter,
                signature
            )?;
            for i in 0..*params {
                write!(out, "  (void)l{i};")?;
            }
            let previous_tuple = OWNED_TUPLE_LOCALS.with(|owned| {
                let previous = owned.borrow().clone();
                owned.borrow_mut().insert(variant.product_parameter);
                previous
            });
            let previous_spine = Self::install_owned_spine_locals([variant.input_parameter]);
            let previous_calls = OWNED_RECURSIVE_COMBINE_CALLS.with(|calls| {
                let previous = calls.borrow().clone();
                calls
                    .borrow_mut()
                    .insert(variant.combine_call, variant.input_parameter);
                previous
            });
            write!(out, "\n  return ")?;
            let result = self.compile_expr(body, out);
            OWNED_RECURSIVE_COMBINE_CALLS.with(|calls| *calls.borrow_mut() = previous_calls);
            Self::restore_owned_spine_locals(previous_spine);
            OWNED_TUPLE_LOCALS.with(|owned| *owned.borrow_mut() = previous_tuple);
            result?;
            writeln!(out, ";\n}}\n")?;
        }

        // A structurally rebuilding recursive worker may consume an exclusive
        // input spine. Each branch which returns the same constructor writes its
        // completed fields back into that node; recursive calls receive the owned
        // tail and do the same. Growth branches simply allocate as before.
        for worker in &self.workers {
            let Worker { name, params, body } = worker;
            let Some(parameters) = owned_data_variants.get(name) else {
                continue;
            };
            let signature = (0..*params)
                .map(|i| format!("Value l{i}"))
                .collect::<Vec<_>>()
                .join(", ");
            for parameter in parameters {
                writeln!(
                    out,
                    "Value {}_owned_data_{}_worker({}) {{",
                    c_name(name),
                    parameter,
                    signature
                )?;
                for i in 0..*params {
                    write!(out, "  (void)l{i};")?;
                }
                if self.compile_owned_data_loop_worker(worker, *parameter, out)? {
                    continue;
                }
                let mut returns = Vec::new();
                Self::owned_data_result_nodes(body, *parameter, None, &mut returns);
                let previous_returns = OWNED_DATA_RETURNS.with(|current| {
                    let previous = current.borrow().clone();
                    current.borrow_mut().extend(
                        returns
                            .into_iter()
                            .map(|node| (node, format!("l{parameter}"))),
                    );
                    previous
                });
                let previous_owned = Self::install_owned_spine_locals([*parameter]);
                write!(out, "\n  return ")?;
                let result = self.compile_expr(body, out);
                Self::restore_owned_spine_locals(previous_owned);
                OWNED_DATA_RETURNS.with(|current| *current.borrow_mut() = previous_returns);
                result?;
                writeln!(out, ";\n}}\n")?;
            }
        }

        for Worker { name, params, body } in &self.workers {
            let Some(parameters) = owned_spine_worker_variants.get(name) else {
                continue;
            };
            let signature = (0..*params)
                .map(|i| format!("Value l{i}"))
                .collect::<Vec<_>>()
                .join(", ");
            for parameter in parameters {
                writeln!(
                    out,
                    "Value {}_owned_spine_{}_worker({}) {{",
                    c_name(name),
                    parameter,
                    signature
                )?;
                for i in 0..*params {
                    write!(out, "  (void)l{i};")?;
                }
                let previous = Self::install_owned_spine_locals([*parameter]);
                write!(out, "\n  return ")?;
                let result = self.compile_expr(body, out);
                Self::restore_owned_spine_locals(previous);
                result?;
                writeln!(out, ";\n}}\n")?;
            }
        }

        for Worker { name, params, body } in &self.workers {
            if !owned_rebuild_variants.contains(name) {
                continue;
            }
            debug_assert_eq!(*params, 1);
            writeln!(
                out,
                "Value {}_owned_rebuild_worker(Value l0) {{",
                c_name(name)
            )?;
            writeln!(out, "  (void)l0;")?;
            let previous = Self::install_owned_spine_locals([0]);
            write!(out, "  return ")?;
            let result = self.compile_expr(body, out);
            Self::restore_owned_spine_locals(previous);
            result?;
            writeln!(out, ";\n}}\n")?;
        }

        // Chain workers: the uncurried entry a chain-head closure carries, run by
        // `apply_n` when the head is applied to exactly `arity` arguments. `self`
        // is the head closure (so `env_get(self, i)` still reads the chain's
        // captures); the flattened parameters arrive in `args[0..arity]`, which we
        // name `l0..l{arity-1}` to match the frame the flattened body expects.
        for ChainWorker { head, arity, body } in &self.chain_workers {
            if std::env::var_os("MARM_DUMP_C_INLINE").is_some() {
                eprintln!("[c-inline] uworker {head} nodes={}", c_expr_size(body));
            }
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
                let borrowed = self.borrowed_slice_places(SelfCall::SelfRef, *arity, body);
                let immutable_bases = self.immutable_slice_bases(SelfCall::SelfRef, *arity, body);
                let borrows_slices = !borrowed.is_empty();
                let mut slots = borrowed.values().cloned().collect::<Vec<_>>();
                slots.sort();
                let previous = Self::install_borrowed_slice_places(borrowed);
                let previous_bases = Self::install_immutable_slice_bases(&immutable_bases);
                let fresh_backedge =
                    self.fresh_backedge_parameters(SelfCall::SelfRef, *arity, body);
                let dynamic_parameters = if std::env::var_os("MARM_NO_DYNAMIC_OWNERSHIP").is_some()
                {
                    Vec::new()
                } else {
                    (0..*arity)
                        .filter(|parameter| Self::max_local_uses_per_path(body, *parameter) <= 1)
                        .collect::<Vec<_>>()
                };
                let previous_dynamic = Self::install_dynamic_owned_spine_locals(
                    dynamic_parameters
                        .iter()
                        .map(|parameter| (*parameter, format!("_own{parameter}"))),
                );
                let mut emitted = CodeBuffer::default();
                let mut first = CodeBuffer::default();
                if fresh_backedge.is_empty() {
                    self.compile_tail(SelfCall::SelfRef, *arity, body, &mut emitted)?;
                } else {
                    let label = format!("_owned_loop{}", MATCH_ID.fetch_add(1, Ordering::Relaxed));
                    let previous_label =
                        TAIL_BACKEDGE_LABEL.with(|current| current.replace(Some(label.clone())));
                    let first_result =
                        self.compile_tail(SelfCall::SelfRef, *arity, body, &mut first);
                    TAIL_BACKEDGE_LABEL.with(|current| *current.borrow_mut() = previous_label);
                    first_result?;
                    let previous_owned = TAIL_BACKEDGE_OWNED_LOCALS.with(|current| {
                        std::mem::replace(
                            &mut *current.borrow_mut(),
                            fresh_backedge.iter().copied().collect(),
                        )
                    });
                    let steady_result =
                        self.compile_tail(SelfCall::SelfRef, *arity, body, &mut emitted);
                    TAIL_BACKEDGE_OWNED_LOCALS
                        .with(|current| *current.borrow_mut() = previous_owned);
                    steady_result?;
                    write!(first, " {label}: ;")?;
                }
                Self::restore_dynamic_owned_spine_locals(previous_dynamic);
                Self::restore_immutable_slice_bases(previous_bases);
                Self::restore_borrowed_slice_places(previous);
                let needs_poll = borrows_slices
                    || self.loop_needs_poll(SelfCall::SelfRef, *arity, body, &allocating);
                let slots = slots
                    .iter()
                    .map(|slot| format!("_Alignas(MARM_VALUE_ALIGNMENT) Slice {slot}; "))
                    .collect::<String>();
                let bases = immutable_bases
                    .iter()
                    .map(|base| {
                        format!("const uint8_t *{} = slice_ptr({}); ", base.name, base.value)
                    })
                    .collect::<String>();
                let ownership_flags = dynamic_parameters
                    .iter()
                    .map(|parameter| format!("bool _own{parameter} = false; "))
                    .collect::<String>();
                write!(
                    out,
                    "\n  {slots}{bases}{ownership_flags}{}{{ {first} }} for (;;) {{ {}{emitted} }}\n}}\n\n",
                    poll_decl(needs_poll),
                    back_edge_poll(needs_poll)
                )?;
            } else {
                write!(out, "\n  return ")?;
                self.compile_expr(body, out)?;
                writeln!(out, ";\n}}\n")?;
            }
        }

        // A binary closure may receive an exclusively owned tuple as its second
        // argument. Its specialized entry has the same closure ABI, but terminal
        // tuple results replace that box after computing every new field.
        for worker @ ChainWorker { head, arity, body } in &self.chain_workers {
            let Some((tuple_arity, returns)) = self.owned_tuple_step(worker) else {
                continue;
            };
            debug_assert_eq!(*arity, 2);
            CAPTURE_PLACES.with(|places| *places.borrow_mut() = self.capture_places(head));
            writeln!(
                out,
                "Value {}_owned_tuple_uworker(Value self, Value *args) {{",
                c_name(head)
            )?;
            write!(out, "  (void)self;")?;
            for i in 0..*arity {
                write!(out, " Value l{i} = args[{i}];")?;
            }
            let previous = OWNED_TUPLE_RETURNS.with(|current| {
                let previous = current.borrow().clone();
                current.borrow_mut().extend(
                    returns
                        .into_iter()
                        .map(|node| (node, (1usize, tuple_arity))),
                );
                previous
            });
            write!(out, "\n  return ")?;
            let result = self.compile_expr(body, out);
            OWNED_TUPLE_RETURNS.with(|current| *current.borrow_mut() = previous);
            result?;
            writeln!(out, ";\n}}\n")?;
        }

        for ChainWorker { head, arity, body } in &self.chain_workers {
            let Some(step) = owned_product_data_steps.get(head) else {
                continue;
            };
            debug_assert_eq!(*arity, 2);
            CAPTURE_PLACES.with(|places| *places.borrow_mut() = self.capture_places(head));
            writeln!(
                out,
                "Value {}_owned_tuple_data_uworker(Value self, Value *args, Value owned_data) {{",
                c_name(head)
            )?;
            writeln!(
                out,
                "  if (data_len(owned_data) != {}) return apply_n_owned_last(self, {}, args);",
                step.data_arity, arity
            )?;
            write!(out, "  (void)self;")?;
            for i in 0..*arity {
                write!(out, " Value l{i} = args[{i}];")?;
            }
            write!(out, " Value _owned_data = owned_data;")?;
            let previous_tuples = OWNED_TUPLE_RETURNS.with(|current| {
                let previous = current.borrow().clone();
                current.borrow_mut().extend(
                    step.product_returns
                        .iter()
                        .map(|node| (*node, (1usize, step.product_arity))),
                );
                previous
            });
            let previous_data = OWNED_DATA_RETURNS.with(|current| {
                let previous = current.borrow().clone();
                current
                    .borrow_mut()
                    .insert(step.data_return, "_owned_data".to_owned());
                previous
            });
            write!(out, "\n  return ")?;
            let result = self.compile_expr(body, out);
            OWNED_DATA_RETURNS.with(|current| *current.borrow_mut() = previous_data);
            OWNED_TUPLE_RETURNS.with(|current| *current.borrow_mut() = previous_tuples);
            result?;
            writeln!(out, ";\n}}\n")?;
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
            if is_builtin(name) || Self::static_int_initializer(value).is_some() {
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
            .filter(|binding| {
                !is_builtin(&binding.name) && Self::static_int_initializer(&binding.value).is_none()
            })
            .map(|binding| &binding.name)
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

        match entry_point {
            CEntryPoint::Process => writeln!(out, "int main(void) {{")?,
            CEntryPoint::Wasm => {
                writeln!(out, "static bool marmelade_started = false;")?;
                writeln!(out, "void marmelade_start(void) {{")?;
                writeln!(out, "  if (marmelade_started) return;")?;
                writeln!(out, "  marmelade_started = true;")?;
            }
        }
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
        match entry_point {
            CEntryPoint::Process => writeln!(out, "  return 0;\n}}")?,
            CEntryPoint::Wasm => {
                // Emscripten cannot expose pointers held in Wasm locals to a
                // conservative collector. Once the program call has returned,
                // persistent state is in the precise global-root table and a full
                // collection is sound. Future Wasm event wrappers use the same
                // boundary discipline.
                writeln!(out, "  gc_collect();")?;
                writeln!(out, "}}")?;
            }
        }
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
            Expr::Apply(a, the) => {
                let combine_owner = OWNED_RECURSIVE_COMBINE_CALLS
                    .with(|calls| calls.borrow().get(&(expr as *const Expr as usize)).copied());
                if let Some(owner) = combine_owner {
                    return self.compile_owned_recursive_combine(expr, owner, code);
                }
                let owned = OWNED_DATA_RETURNS.with(|returns| {
                    returns
                        .borrow()
                        .get(&(expr as *const Expr as usize))
                        .cloned()
                });
                if let Some(owner) = owned {
                    let (constructor, arguments) = Self::constructor_application(expr)
                        .expect("owned data result is a constructor application");
                    self.compile_owned_data_application(&owner, constructor, &arguments, code)
                } else {
                    self.compile_apply(a, the, code)
                }
            }
            Expr::Let(_, the) => self.compile_let(the, code),
            Expr::Tuple(_, the) => {
                let virtual_tuple = VIRTUAL_TUPLE_LITERALS.with(|tuples| {
                    tuples
                        .borrow()
                        .get(&(the as *const ast::Tuple<CaptureInfo, Identifier> as usize))
                        .cloned()
                });
                if let Some(local) = virtual_tuple {
                    return write!(code, "VBorrowedTuple((void *){local}.elems)");
                }
                let owned = OWNED_TUPLE_RETURNS.with(|returns| {
                    returns
                        .borrow()
                        .get(&(expr as *const Expr as usize))
                        .copied()
                });
                if let Some((local, arity)) = owned {
                    debug_assert_eq!(arity, the.elements.len());
                    self.compile_owned_tuple_replace(local, &the.elements, code)
                } else {
                    self.compile_tuple(&the.elements, code)
                }
            }
            Expr::Record(a, the) => self.compile_record(a, the, code),
            Expr::RecordUpdate(a, the) => self.compile_record_update(a, the, code),
            Expr::Inject(_, the) => {
                let owned = OWNED_DATA_RETURNS.with(|returns| {
                    returns
                        .borrow()
                        .get(&(expr as *const Expr as usize))
                        .cloned()
                });
                if let Some(owner) = owned {
                    self.compile_owned_data_replace(&owner, the, code)
                } else {
                    self.compile_inject(the, code)
                }
            }
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

    fn compile_owned_recursive_combine(
        &self,
        expression: &Expr,
        owner: usize,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        let mut head = strip_ascription(expression);
        let mut arguments = Vec::new();
        while let Expr::Apply(_, application) = head {
            arguments.push(application.argument.as_ref());
            head = strip_ascription(&application.function);
        }
        arguments.reverse();
        write!(code, "apply_n_owned_last_data(")?;
        self.compile_expr(head, code)?;
        write!(code, ", {}, (Value[]){{", arguments.len())?;
        for (index, argument) in arguments.iter().enumerate() {
            if index != 0 {
                write!(code, ", ")?;
            }
            self.compile_expr(argument, code)?;
        }
        write!(code, "}}, l{owner})")
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

    fn compile_owned_tuple_replace(
        &self,
        local: usize,
        elements: &[Rc<Expr>],
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
        write!(code, "({{ ")?;
        for (index, element) in elements.iter().enumerate() {
            write!(code, "Value _otr{id}_{index} = ")?;
            self.compile_expr(element, code)?;
            write!(code, "; ")?;
        }
        write!(code, "reuse_owned_tuple{}_fast(l{local}", elements.len())?;
        for index in 0..elements.len() {
            write!(code, ", _otr{id}_{index}")?;
        }
        write!(code, "); }})")
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
        if let Some(shape) = self.flat_array_record_adapter_shape(element) {
            return (shape.len() <= FLAT_MAX_SHAPE).then_some(shape);
        }
        let result = self.runtime_shape(element, &mut Vec::new());
        let mut encoded = Vec::new();
        result.shape.encode(&mut encoded);
        (encoded.len() <= FLAT_MAX_SHAPE).then_some(encoded)
    }

    /// A nominal polymorphic record has a fixed canonical ABI, while a packed
    /// array instantiates its fields and may use a narrower/wider ground layout.
    /// Encode both sides at that boundary. `SHAPE_ABI_RECORD` is interpreted by
    /// the runtime as pairs of `(canonical field shape, packed field shape)`.
    fn flat_array_record_adapter_shape(&self, element: &Type) -> Option<Vec<i64>> {
        let (name, arguments) = match element {
            Type::Constructor(name) => (name, Vec::new()),
            Type::Apply { .. } => applied_type(element)?,
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
        let abi_widths = self.flat_widths(element)?;
        if fields.len() != abi_widths.len() {
            return None;
        }

        let mut pairs = Vec::with_capacity(fields.len());
        let mut differs = false;
        for (field, abi_width) in fields.into_iter().zip(abi_widths) {
            let field_type = instantiate_type_expression(&field.type_signature.body, &bindings)?;
            let packed = self.runtime_shape(&field_type, &mut Vec::new()).shape;
            let abi = Self::record_abi_field_shape(abi_width, &packed);
            differs |= abi != packed;
            pairs.push((abi, packed));
        }
        if !differs {
            return None;
        }

        let mut encoded = vec![-3, pairs.len() as i64];
        for (abi, packed) in pairs {
            abi.encode(&mut encoded);
            packed.encode(&mut encoded);
        }
        Some(encoded)
    }

    fn record_abi_field_shape(abi_width: usize, packed: &RuntimeShape) -> RuntimeShape {
        if abi_width == 1 {
            // A one-word field in the fixed record ABI is the canonical value
            // itself. Its ground instantiation can also occupy one packed word,
            // but a one-word product or niche sum has a different representation.
            RuntimeShape::Leaf
        } else if abi_width == packed.stored_words() {
            packed.clone()
        } else {
            match packed {
                // A niche is a packed-layout choice. The fixed record ABI retains
                // the ordinary tag word and union payload.
                RuntimeShape::NicheSum {
                    niche_tag,
                    payload_tag,
                    payload_fields,
                    ..
                } => {
                    let variant_count = 1 + (*niche_tag).max(*payload_tag);
                    let mut variants = vec![Vec::new(); variant_count];
                    variants[*payload_tag] = payload_fields.clone();
                    debug_assert!(variants[*niche_tag].is_empty());
                    RuntimeShape::Sum {
                        payload_words: abi_width - 1,
                        variants,
                    }
                }
                // Wider fixed fields are emitted as canonical flat words.
                _ => RuntimeShape::Product(vec![RuntimeShape::Leaf; abi_width]),
            }
        }
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
        let instantiated = arguments
            .iter()
            .cloned()
            .fold(Type::Constructor(name.clone()), Type::application);
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
        let instantiated = arguments
            .iter()
            .cloned()
            .fold(Type::Constructor(name.clone()), Type::application);
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
                let reaches_enclosing_type =
                    children.iter().any(|child| child.reaches_enclosing_type);
                let children = children
                    .into_iter()
                    .map(|child| child.shape)
                    .collect::<Vec<_>>();

                // A record nested in another shaped value cannot use the
                // top-level ABI adapter. If its fixed canonical field layout
                // differs from its ground packed layout, keep the record as one
                // boxed leaf. Describing the packed shape here would make
                // `flatten` read the canonical tuple with the wrong offsets.
                let abi_differs = self.flat_widths(&instantiated).is_some_and(|widths| {
                    widths.iter().zip(&children).any(|(width, packed)| {
                        Self::record_abi_field_shape(*width, packed) != *packed
                    })
                });

                // `compile_record` itself splats a record whenever any nested field
                // is wider than one word. A shaped array must then describe that
                // canonical value as the already-flat tuple it actually is;
                // otherwise `flatten` would try to descend into an intermediate
                // tuple that was deliberately never allocated.
                let splatted = self
                    .flat_widths(&instantiated)
                    .is_some_and(|widths| widths.iter().any(|width| *width > 1));

                if abi_differs {
                    ShapeResult {
                        reaches_enclosing_type: false,
                        shape: RuntimeShape::Leaf,
                    }
                } else {
                    ShapeResult {
                        reaches_enclosing_type,
                        shape: RuntimeShape::Product(if splatted {
                            let mut words = Vec::new();
                            for child in children {
                                child.splat_words(&mut words);
                            }
                            words
                        } else {
                            children
                        }),
                    }
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
            "mk_tuple(1, ({{ _Alignas(MARM_VALUE_ALIGNMENT) static const struct {{ GcHeader gch; int64_t s[{words}]; }} __ml = \
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

    fn compile_owned_data_replace(
        &self,
        owner: &str,
        the: &phase::Injection<Closed>,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        let arguments = the
            .arguments
            .iter()
            .map(|argument| &**argument)
            .collect::<Vec<_>>();
        self.compile_owned_data_application(owner, &the.constructor, &arguments, code)
    }

    fn compile_owned_data_application(
        &self,
        owner: &str,
        constructor: &QualifiedName,
        arguments: &[&Expr],
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        let arity = arguments.len();
        debug_assert!((1..=4).contains(&arity));
        let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
        write!(code, "({{ ")?;
        for (index, argument) in arguments.iter().enumerate() {
            write!(code, "Value _od{id}_{index} = ")?;
            self.compile_expr(argument, code)?;
            write!(code, "; ")?;
        }
        write!(
            code,
            "reuse_owned_data{arity}_fast({owner}, {}",
            self.constructor_tag(constructor)
        )?;
        for index in 0..arity {
            write!(code, ", _od{id}_{index}")?;
        }
        write!(code, "); }})")
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
                let place = CapturePlace { offset, width };
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
            // A nominal record has one ABI for every instantiation. In particular,
            // a field declared as a type parameter occupies one boxed word even when
            // a caller supplies a ground sum whose own inline width is larger. Generic
            // producers and consumers otherwise disagree about all following offsets,
            // and projecting the parameter yields the sum's raw tag instead of its
            // boxed value. `record_layouts` was computed from the declaration with
            // exactly this fixed-layout rule, so it is the authority here.
            Type::Constructor(name) => self.record_layouts.get(name).cloned(),
            Type::Apply { .. } => {
                let (name, _) = applied_type(ty)?;
                self.record_layouts.get(&name).cloned()
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
        if on_path.contains(ty) {
            return 1;
        }
        // A ground unary sum may use a one-word zero niche directly inside a
        // canonical flat record. Parametric sums retain their fixed tagged
        // representation: `Perhaps (Perhaps a)` must still distinguish
        // `This Nope` from `Nope` until the payload type is known.
        if ty.variables().is_empty()
            && let Some((_niche_tag, _payload_tag)) = self.one_word_niche_on_path(ty, on_path)
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

    // The fixed inline layout of a coproduct type (peeling `Perhaps τ` to
    // `Perhaps`). `None` for records, sums whose recursion knot cannot be cut to
    // a pointer within the cap, and everything else.
    /// Splat a boxed sum value into the `width` words of an inline union.
    ///
    /// The tag word, then the ACTIVE variant's fields flattened. A field whose own
    /// flat width is one word is the boxed node's field as it stands; a wider one is
    /// itself a flat aggregate, stored boxed, so its words are projected out. Which
    /// variant is active is a runtime question, and two variants can put different
    /// fields in the same word, so each word switches on the tag.
    ///
    /// Reading `data_field` straight across -- one word per constructor field -- is
    /// wrong the moment any field is wider than a word: it puts the aggregate's
    /// POINTER where the layout wants its first word, and pads the rest with zeroes.
    fn sum_splat_leaves(&self, value: &str, layout: &CoproductLayout, width: usize) -> Vec<String> {
        let mut leaves = vec![format!("VInt(data_tag({value}))")];
        for slot in 0..width.saturating_sub(1) {
            let mut arms: Vec<(usize, String)> = Vec::new();
            for (tag, fields) in layout.variant_widths.iter().enumerate() {
                let mut offset = 0;
                for (index, &field_width) in fields.iter().enumerate() {
                    if slot < offset + field_width {
                        arms.push((
                            tag,
                            if field_width == 1 {
                                format!("data_field({value}, {index})")
                            } else {
                                format!("proj(data_field({value}, {index}), {})", slot - offset)
                            },
                        ));
                        break;
                    }
                    offset += field_width;
                }
            }
            let every_variant_agrees = arms.len() == layout.variant_widths.len()
                && arms.iter().all(|(_, arm)| *arm == arms[0].1);
            leaves.push(if every_variant_agrees {
                arms[0].1.clone()
            } else {
                arms.iter()
                    .rev()
                    .fold("((Value){0})".to_string(), |otherwise, (tag, arm)| {
                        format!("(data_tag({value}) == {tag} ? {arm} : {otherwise})")
                    })
            });
        }
        leaves
    }

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
        self.one_word_niche_on_path(ty, &[])
    }

    fn one_word_niche_on_path(&self, ty: &Type, on_path: &[Type]) -> Option<(usize, usize)> {
        // A niche only matters for a sum accepted by fixed-layout analysis. Carry
        // the caller's record-expansion path into runtime-shape analysis as well:
        // starting it from an empty path can reopen a record-mediated recursion
        // knot such as State -> Transition -> State.
        self.sum_layout(ty)?;
        let mut runtime_path = on_path.to_vec();
        let RuntimeShape::NicheSum {
            niche_tag,
            payload_tag,
            payload_fields,
            ..
        } = self.runtime_shape(ty, &mut runtime_path).shape
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
    /// Peel a constructor application down to its constructor and arguments:
    /// `Inject` (the elaborated form), a saturated `Apply` chain onto a global, or a
    /// bare global for a nullary constructor. `None` for anything else.
    fn constructor_application<'e>(value: &'e Expr) -> Option<(&'e QualifiedName, Vec<&'e Expr>)> {
        match strip_ascription(value) {
            Expr::Inject(_, inject) => Some((
                &inject.constructor,
                inject.arguments.iter().map(|a| &**a).collect(),
            )),
            application @ Expr::Apply(..) => {
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
                Some((constructor, arguments))
            }
            Expr::Variable(_, Identifier::Global(constructor)) => Some((constructor, Vec::new())),
            _ => None,
        }
    }

    /// The single word a one-word niche field stores for a LITERAL constructor: the
    /// zero word for the niche constructor, the payload's own compiled value for the
    /// payload constructor.
    ///
    /// Deliberately the BOXED form -- the same word `encode_one_word_niche` produces
    /// with `data_field(v, 0)`, and the same word `decode_one_word_niche` reads back.
    /// Splatting the payload STRUCTURALLY instead is wrong here: when the payload is
    /// itself an inlined sum (`Perhaps Colour`, where `Colour` is a nullary enum) its
    /// structural word is the sum's TAG, and every reader would rebuild `This <tag>`
    /// and then dereference the tag as though it were the value.
    fn literal_niche_word(
        &self,
        value: &Expr,
        niche_tag: usize,
        payload_tag: usize,
    ) -> Option<String> {
        let (constructor, arguments) = Self::constructor_application(value)?;
        let tag = *self.constructor_tags.get(constructor)? as usize;
        if tag == niche_tag && arguments.is_empty() {
            return Some("((Value){0})".to_string());
        }
        if tag == payload_tag && arguments.len() == 1 {
            return Some(self.compile_to_string(arguments[0]));
        }
        None
    }

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
                if let Some(word) = self.literal_niche_word(value, niche_tag, payload_tag) {
                    return vec![word];
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
                    for ((_, _label, field), w) in sub.fields.iter().zip(sub_widths) {
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
        if let Some(layout) = self.sum_layout(&value.annotation().type_info.inferred_type) {
            // A boxed sum -> the inline union.
            self.sum_splat_leaves(&temp, layout, width)
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
            // A zeroable leaf is a leaf to everything but niche selection.
            RuntimeShape::Leaf | RuntimeShape::ZeroableLeaf => out.push(path.to_string()),
            RuntimeShape::Product(fields) => {
                for (index, field) in fields.iter().enumerate() {
                    Self::canonical_product_leaves(&format!("proj({path}, {index})"), field, out);
                }
            }
            // A sum stored in ONE word is a leaf as far as word extraction goes: the
            // parent object's slot holds exactly that word, so it is projected like any
            // other field. The shape still says `Sum` because the collector needs the
            // variant structure -- only the splatting does not.
            RuntimeShape::Sum { .. } | RuntimeShape::NicheSum { .. }
                if shape.stored_words() == 1 =>
            {
                out.push(path.to_string())
            }
            // A WIDER sum is spliced across several words, and which words those are
            // depends on the variant -- so it needs variant-dependent traversal that
            // this static walk cannot do. Known constructor applications are handled by
            // `constructor_shape_leaves`; the rest fall out of the caller's length
            // check and keep the runtime fallback.
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
                for ((_, _, field), shape) in record.fields.iter().zip(fields) {
                    leaves.extend(self.literal_shape_leaves(field, shape, prelude)?);
                }
                Some(leaves)
            }
            (Expr::Record(annotation, record), RuntimeShape::Product(_)) => {
                let widths = self.flat_widths(&annotation.type_info.inferred_type)?;
                (widths.iter().sum::<usize>() == shape.stored_words()).then_some(())?;
                let mut leaves = Vec::new();
                for ((_, _, field), width) in record.fields.iter().zip(widths) {
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
    ) -> Option<(Vec<String>, usize, usize, Type, RuntimeShape)> {
        let (root, selectors) = projection_root_and_selectors(projection);
        let words = self.flat_words_for(root)?;
        let mut current_type = root.annotation().type_info.inferred_type.clone();
        let mut offset = 0;
        let mut width = words.len();
        for (step, selector) in selectors.iter().enumerate() {
            let ProductElement::Ordinal(index) = selector else {
                return None;
            };
            let widths = self.flat_widths(&current_type)?;
            let (next_type, _) = self.runtime_projection_field(&current_type, selector)?;
            let field_offset = widths[..*index].iter().sum::<usize>();
            width = *widths.get(*index)?;
            // A product field kept in ONE word is a POINTER to a separate object, so
            // offsets cannot be accumulated across it -- even when that product itself
            // contains only one word. The latter still has a `mk_tuple1` box; treating
            // its parent's slot as the field inside that box turns `outer.Inner.Value`
            // into `outer.Inner` and hands the record object to consumers expecting
            // `Value`. Give up and let `flat_place` compile the dereference as a new
            // base. `flat_place` already guards this; without the same guard here,
            // projections through split locals/captures cross a boxed field boundary.
            if step + 1 < selectors.len() {
                if width == 1 && self.flat_widths(&next_type).is_some() {
                    return None;
                }
            }
            offset += field_offset;
            current_type = next_type;
        }
        let shape = self.runtime_shape(&current_type, &mut Vec::new()).shape;
        (offset + width <= words.len()).then_some((words, offset, width, current_type, shape))
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
        // Reach through a base that is itself an inlined flat projection,
        // accumulating offsets so `r.b.c` is one load. A one-word record field
        // is a pointer to its own object, however, so projection must stop there
        // and compile that inner dereference as the new base.
        if let Expr::Project(_, inner) = strip_ascription(&projection.base) {
            if let Some((base, base_offset, base_width)) = self.flat_place(inner)
                && base_width > 1
            {
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
            if let Some([array, index]) = program
                .intrinsic_arguments::<2>(expression, IntrinsicOperation::PackedArrayGetUnchecked)
            {
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
            let [array, index] = program.intrinsic_arguments::<2>(
                &clause.consequent,
                IntrinsicOperation::PackedArrayGetUnchecked,
            )?;
            if !matches!(strip_ascription(array), Expr::Variable(_, Identifier::Local(level)) if level == bound_level)
            {
                return None;
            }
            let element_type = program.mutable_array_element_type(
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
            if let Some([array, index, replacement]) = program
                .intrinsic_arguments::<3>(expression, IntrinsicOperation::PackedArraySetUnchecked)
            {
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
            let [array, index, replacement] = program.intrinsic_arguments::<3>(
                &clause.consequent,
                IntrinsicOperation::PackedArraySetUnchecked,
            )?;
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
                    .map(|(_, _, field)| self.pattern_runtime_shape(field))
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
                        .all(|((_, _, pattern), shape)| {
                            self.array_pattern_supported(pattern, shape)
                        })
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
                for ((_, _, pattern), shape) in record.fields.iter().zip(fields) {
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
                        for ((_, _label, field), w) in the.fields.iter().zip(widths) {
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
                        for (index, (_, _label, field)) in the.fields.iter().enumerate() {
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
    /// The physical words a flat record literal stores, field by field.
    ///
    /// THE single producer of a flat record's body. `compile_record` builds the object
    /// out of these words and `flat_record_literal` spreads the same words across a
    /// split local's slots, so the two cannot disagree about how a field is spelled --
    /// which they did: the record path niche-encoded a one-word sum field while the
    /// split-local path splatted it STRUCTURALLY through `literal_shape_leaves`, so the
    /// same `{ First := This Red }` became `Root_Red` in an object and `VInt(1)` in a
    /// local, and every reader decoded whichever it got as the other.
    fn record_literal_leaves(
        &self,
        record_type: &Type,
        the: &phase::Record<Closed>,
        prelude: &mut Vec<String>,
    ) -> Option<Vec<String>> {
        let widths = self.flat_widths(record_type)?;
        (widths.len() == the.fields.len()).then_some(())?;
        let mut leaves = Vec::new();
        for ((_, _label, value), width) in the.fields.iter().zip(&widths) {
            leaves.extend(self.flat_leaves(value, *width, prelude));
        }
        (leaves.len() == widths.iter().sum::<usize>()).then_some(leaves)
    }

    fn compile_record(
        &self,
        annotation: &CaptureInfo,
        the: &phase::Record<Closed>,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        // Flat path: build ONE object whose body is the fields' flattened leaves.
        //
        // This runs for EVERY record with a known layout, not only for one with a
        // nested inlined field (some width > 1). It has to: `flat_leaves` is also what
        // niche-ENCODES a one-word sum field (`Nope` becomes the zero word), and every
        // reader -- `flat_place` in `compile_projection`, `collect_pattern_flat`,
        // `canonical_update_leaves` -- decodes a width-1 field that way. When
        // construction skipped the flat path it stored the BOXED sum instead and the
        // reader decoded a pointer as though it were a niche, so a record field holding
        // `Nope` read back as `This <garbage>`.
        //
        // Records with no niche field stay byte-identical: `flat_leaves` of a width-1
        // non-niche field is the field's own compiled expression, and `tuple_from_words`
        // picks the same `mk_tupleN` the fallback below would.
        if self.flat_records_enabled()
            && let Some(leaves) = {
                let mut probe = Vec::new();
                let found = self.record_literal_leaves(
                    &annotation.type_info.inferred_type,
                    the,
                    &mut probe,
                );
                found.map(|leaves| (probe, leaves))
            }
        {
            let (prelude, leaves) = leaves;
            let total = leaves.len();
            // A record wider than its field count has an inlined aggregate in it: keep
            // the general `mk_tuple(n, ...)` builder it already used.
            let build = if total > the.fields.len() {
                format!("mk_tuple({total}, {})", leaves.join(", "))
            } else {
                Self::tuple_from_words(&leaves)
            };
            if prelude.is_empty() {
                return write!(code, "{build}");
            }
            write!(code, "({{ ")?;
            for binding in &prelude {
                write!(code, "{binding} ")?;
            }
            return write!(code, "{build}; }})");
        }

        let mut written = if the.fields.len() <= 4 {
            write!(code, "mk_tuple{}(", the.fields.len())?;
            false
        } else {
            write!(code, "mk_tuple({}", the.fields.len())?;
            true
        };
        for (_, _label, value) in &the.fields {
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
        if let Some(layout) = self.sum_layout(ty) {
            self.sum_splat_leaves(value, layout, width)
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
                let rebuilt = self.record_update_leaves(
                    update,
                    &path,
                    &field_type,
                    base_leaves[offset..offset + width].to_vec(),
                    replacements,
                );
                if rebuilt.len() == width {
                    result.extend(rebuilt);
                } else {
                    // The field is BOXED: this record keeps one word for it (a
                    // pointer), but the sub-record's own layout is wider, so the
                    // recursion unpacked the pointee and rebuilt all of its words.
                    // Box them back up, or they spill into the slots of the fields
                    // that follow and every later offset is wrong.
                    result.push(format!(
                        "mk_tuple({}, {})",
                        rebuilt.len(),
                        rebuilt.join(", ")
                    ));
                }
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
            if let Some((words, offset, width, selected_type, shape)) = self.flat_value_region(the)
            {
                // A one-word field is stored in canonical form. In particular, a
                // one-field record occupies one pointer word; rebuilding it with
                // `mk_tuple1` would add a second, spurious box.
                if width == 1 {
                    if let Some(decoded) =
                        self.decode_one_word_niche(&words[offset], &selected_type)
                    {
                        return write!(code, "{decoded}");
                    }
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
                        Self::tuple_from_words(&words[offset..offset + width])
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

        // Carry a fresh tuple through an ownership-preserving call as a virtual
        // aggregate when its result is consumed here. The tuple-shaped stack
        // object keeps the normal Value ABI, and its fields remain visible to the
        // conservative root scan during allocations. Tuple-pattern arms read the
        // fields directly; a whole-value arm materialises a heap tuple lazily.
        if std::env::var_os("MARM_NO_VIRTUAL_TUPLES").is_none()
            && !matches!(strip_ascription(&the.scrutinee), Expr::Tuple(..))
            && let Some(tuple) = self.owned_tuple_literal(&the.scrutinee)
            && (1..=4).contains(&tuple.elements.len())
        {
            let owned_product_fields = OWNED_SPINE_LOCALS.with(|owned| {
                self.owned_product_fields_from_recursive_eliminator(&the.scrutinee, &owned.borrow())
            });
            let aggregate = format!("_vtuple{id}");
            let locals = (0..tuple.elements.len())
                .map(|index| format!("{aggregate}.elems[{index}]"))
                .collect::<Vec<_>>();
            if let Some(plans) = self.plan_direct_tuple_match(&the.match_clauses, &locals) {
                write!(
                    code,
                    "({{ _Alignas(MARM_VALUE_ALIGNMENT) struct {{ GcHeader gch; Value elems[{}]; }} {aggregate} = \
                     {{{{{}, 0, OBJ_TUPLE, MARM_ETERNAL, 0}}, {{0}}}}; ",
                    tuple.elements.len(),
                    tuple.elements.len() * std::mem::size_of::<u64>()
                )?;
                for (index, element) in tuple.elements.iter().enumerate() {
                    write!(code, "{aggregate}.elems[{index}] = ")?;
                    self.compile_expr(element, code)?;
                    write!(code, "; ")?;
                }
                let key = tuple as *const ast::Tuple<CaptureInfo, Identifier> as usize;
                let previous = VIRTUAL_TUPLE_LITERALS
                    .with(|tuples| tuples.borrow_mut().insert(key, aggregate.clone()));
                write!(code, "Value _vresult{id} = ")?;
                let result = self.compile_expr(&the.scrutinee, code);
                VIRTUAL_TUPLE_LITERALS.with(|tuples| {
                    let mut tuples = tuples.borrow_mut();
                    if let Some(previous) = previous {
                        tuples.insert(key, previous);
                    } else {
                        tuples.remove(&key);
                    }
                });
                result?;
                write!(code, "; (void)_vresult{id}; ")?;
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
                    let mut owned_binders = HashSet::default();
                    if let Pattern::Tuple(_, pattern) = &clause.pattern {
                        for field in &owned_product_fields {
                            if let Some(field_pattern) = pattern.elements.get(*field) {
                                self.collect_owned_spine_pattern_binders(
                                    field_pattern,
                                    &field_pattern.annotation().type_info.inferred_type,
                                    &mut owned_binders,
                                );
                            }
                        }
                    }
                    owned_binders
                        .retain(|level| Self::owned_local_is_linear(&clause.consequent, *level));
                    let previous = Self::install_owned_spine_locals(owned_binders);
                    let result = self.compile_expr(&clause.consequent, code);
                    Self::restore_owned_spine_locals(previous);
                    result?;
                    write!(code, "; }}) : ")?;
                }
                return write!(code, "match_fail(); }})");
            }
        }

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

        // A comma-separated scrutinee is an ordinary tuple in the AST. When every
        // clause either takes that tuple apart or binds it as a whole, keep its
        // elements in separate C locals instead of allocating `mk_tupleN(...)` only
        // to project it again. A whole-value clause reconstructs the tuple inside
        // that branch, after it has actually matched.
        // Planning precedes emission so an unsupported clause leaves the canonical
        // boxed-tuple path untouched.
        if let Expr::Tuple(_, tuple) = strip_ascription(&the.scrutinee)
            && !tuple.elements.is_empty()
        {
            let locals = (0..tuple.elements.len())
                .map(|index| format!("_scrut{id}_{index}"))
                .collect::<Vec<_>>();
            if let Some(plans) = self.plan_direct_tuple_match(&the.match_clauses, &locals) {
                write!(code, "({{ ")?;
                for (local, element) in locals.iter().zip(&tuple.elements) {
                    write!(code, "Value {local} = ")?;
                    self.compile_expr(element, code)?;
                    write!(code, "; ")?;
                }
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
                    let mut owned_binders = HashSet::default();
                    if let Pattern::Tuple(_, pattern) = &clause.pattern {
                        for (element, field_pattern) in tuple.elements.iter().zip(&pattern.elements)
                        {
                            if self.expression_is_owned_spine(element) {
                                self.collect_owned_spine_pattern_binders(
                                    field_pattern,
                                    &element.annotation().type_info.inferred_type,
                                    &mut owned_binders,
                                );
                            }
                        }
                    }
                    owned_binders
                        .retain(|level| Self::owned_local_is_linear(&clause.consequent, *level));
                    let previous = Self::install_owned_spine_locals(owned_binders);
                    let result = self.compile_expr(&clause.consequent, code);
                    Self::restore_owned_spine_locals(previous);
                    result?;
                    write!(code, "; }}) : ")?;
                }
                return write!(code, "match_fail(); }})");
            }
        }

        // Generic constructor scalar replacement. The simplifier has already
        // cancelled the simplest `C(args)`/`C(patterns)` pairs, but deliberately
        // leaves nested and literal subpatterns plus whole-value fallbacks alone.
        // Keep every constructor field in a C local while those clauses inspect it;
        // only a fallback that binds the complete value materialises the Data box.
        // This is based solely on constructor identity and arity -- no knowledge of
        // List, Perhaps, or any other source-level type is involved.
        if let Some((constructor, arguments)) = Self::constructor_application(&the.scrutinee)
            && !arguments.is_empty()
            && self.constructor_tags.contains_key(constructor)
            && !self.newtype_constructors.contains(constructor)
        {
            let locals = (0..arguments.len())
                .map(|index| format!("_cscrut{id}_{index}"))
                .collect::<Vec<_>>();
            if let Some(plans) =
                self.plan_direct_constructor_match(constructor, &the.match_clauses, &locals)
            {
                write!(code, "({{ ")?;
                for (local, argument) in locals.iter().zip(&arguments) {
                    write!(code, "Value {local} = ")?;
                    self.compile_expr(argument, code)?;
                    write!(code, "; ")?;
                }
                for (clause, plan) in the.match_clauses.iter().zip(&plans) {
                    let Some((tests, binds)) = plan else {
                        continue;
                    };
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
        let scrutinee_owned = self.expression_is_owned_spine(&the.scrutinee);
        // A recursive eliminator can return a product containing a fresh spine
        // even when its input was shared. Preserve that field-level provenance
        // through the product match so a following structural consumer can use
        // the fresh spine as a destination. This is derived from the producer's
        // typed recursion and callback result, not from a library identity.
        let owned_product_fields = OWNED_SPINE_LOCALS.with(|owned| {
            self.owned_product_fields_from_recursive_eliminator(&the.scrutinee, &owned.borrow())
        });
        let scrutinee_dynamic = self
            .dynamic_owned_condition(&the.scrutinee)
            .filter(|condition| condition != "true");

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
            let mut owned_binders = HashSet::default();
            if scrutinee_owned {
                self.collect_owned_spine_pattern_binders(
                    &clause.pattern,
                    &the.scrutinee.annotation().type_info.inferred_type,
                    &mut owned_binders,
                );
                owned_binders.retain(|level| {
                    // Destructive consumption is valid only for a linear use of
                    // this particular subspine along each selected path.
                    Self::owned_local_is_linear(&clause.consequent, *level)
                });
            }
            if let Pattern::Tuple(_, tuple) = &clause.pattern {
                for field in &owned_product_fields {
                    if let Some(field_pattern) = tuple.elements.get(*field) {
                        self.collect_owned_spine_pattern_binders(
                            field_pattern,
                            &field_pattern.annotation().type_info.inferred_type,
                            &mut owned_binders,
                        );
                    }
                }
            }
            owned_binders.retain(|level| {
                // Uses in mutually exclusive branches do not alias at runtime.
                // Accept one use on each path, rather than requiring one use in
                // the whole syntax tree, so the destination survives an `if`.
                Self::owned_local_is_linear(&clause.consequent, *level)
            });
            let previous = Self::install_owned_spine_locals(owned_binders);
            let mut dynamic_binders = HashSet::default();
            if scrutinee_dynamic.is_some() {
                self.collect_owned_spine_pattern_binders(
                    &clause.pattern,
                    &the.scrutinee.annotation().type_info.inferred_type,
                    &mut dynamic_binders,
                );
                dynamic_binders
                    .retain(|level| Self::max_local_uses_per_path(&clause.consequent, *level) <= 1);
            }
            let previous_dynamic = Self::install_dynamic_owned_spine_locals(
                dynamic_binders.into_iter().map(|level| {
                    (
                        level,
                        scrutinee_dynamic.clone().expect("dynamic binder condition"),
                    )
                }),
            );
            let result = self.compile_expr(&clause.consequent, code);
            Self::restore_dynamic_owned_spine_locals(previous_dynamic);
            Self::restore_owned_spine_locals(previous);
            result?;
            write!(code, "; }}) : ")?;
        }

        write!(code, "match_fail(); }})")
    }

    /// Plan a match whose scrutinee is a tuple literal represented by one C local
    /// per element. Tuple patterns inspect those locals directly. A whole-tuple bind
    /// reconstructs the canonical tuple only within the matching clause.
    fn plan_direct_tuple_match(
        &self,
        clauses: &[phase::MatchClause<Closed>],
        locals: &[String],
    ) -> Option<Vec<(Vec<String>, Vec<(usize, String)>)>> {
        clauses
            .iter()
            .map(|clause| {
                let mut tests = Vec::new();
                let mut binds = Vec::new();
                match &clause.pattern {
                    Pattern::Tuple(_, tuple) if tuple.elements.len() == locals.len() => {
                        for (pattern, local) in tuple.elements.iter().zip(locals) {
                            if self.flat_records_enabled() {
                                self.collect_pattern_flat(
                                    pattern, local, 0, 1, true, &mut tests, &mut binds,
                                );
                            } else {
                                self.collect_pattern(pattern, local, &mut tests, &mut binds);
                            }
                        }
                    }
                    Pattern::Bind(_, Identifier::Local(LexicalLevel(level))) => binds.push((
                        *level,
                        if locals.len() <= 4 {
                            format!("mk_tuple{}({})", locals.len(), locals.join(", "))
                        } else {
                            format!("mk_tuple({}, {})", locals.len(), locals.join(", "))
                        },
                    )),
                    _ => return None,
                }
                // A whole-value fallback is represented as an ordinary binder,
                // including `_`.  When that binder is dead, rebuilding the
                // scalar-replaced tuple would be pure allocation with no
                // observable value.  Nested tuple binders benefit from the same
                // liveness check.  The element expressions have already been
                // evaluated into `locals`, so dropping the bind preserves source
                // evaluation order and effects.
                if std::env::var_os("MARM_NO_DEAD_PATTERN_BINDS").is_none() {
                    binds.retain(|(level, _)| {
                        Self::local_use_count(&clause.consequent, *level) != 0
                    });
                }
                Some((tests, binds))
            })
            .collect()
    }

    /// Plan a match against a constructor whose fields are held in separate C
    /// locals. Clauses for other constructors and literal clauses are statically
    /// unreachable. A binder for the whole scrutinee reconstructs the canonical
    /// Data value only in that matching branch.
    fn plan_direct_constructor_match(
        &self,
        injected_constructor: &QualifiedName,
        clauses: &[phase::MatchClause<Closed>],
        locals: &[String],
    ) -> Option<Vec<Option<(Vec<String>, Vec<(usize, String)>)>>> {
        let mut plans = Vec::with_capacity(clauses.len());
        let mut exhaustive = false;
        for clause in clauses {
            if exhaustive {
                plans.push(None);
                continue;
            }
            let mut tests = Vec::new();
            let mut binds = Vec::new();
            match &clause.pattern {
                Pattern::Coproduct(_, constructor) => {
                    let Identifier::Global(name) = &constructor.constructor else {
                        return None;
                    };
                    if name.as_ref() != injected_constructor {
                        plans.push(None);
                        continue;
                    }
                    if constructor.arguments.len() != locals.len() {
                        return None;
                    }
                    for (pattern, local) in constructor.arguments.iter().zip(locals) {
                        if self.flat_records_enabled() {
                            self.collect_pattern_flat(
                                pattern, local, 0, 1, true, &mut tests, &mut binds,
                            );
                        } else {
                            self.collect_pattern(pattern, local, &mut tests, &mut binds);
                        }
                    }
                }
                Pattern::Bind(_, Identifier::Local(LexicalLevel(level))) => {
                    binds.push((
                        *level,
                        self.materialize_constructor(injected_constructor, locals),
                    ));
                }
                Pattern::Bind(_, other) => {
                    panic!("pattern binder must be a local: {other:?}")
                }
                Pattern::Literally(..) => {
                    plans.push(None);
                    continue;
                }
                Pattern::Tuple(..) | Pattern::Struct(..) => return None,
            }
            // As in direct tuple matching, materialize a scalar-replaced
            // constructor only when its pattern binding reaches the clause body.
            // This also removes dead field binds without changing any pattern
            // tests, which refer directly to the scalar locals.
            if std::env::var_os("MARM_NO_DEAD_PATTERN_BINDS").is_none() {
                binds.retain(|(level, _)| Self::local_use_count(&clause.consequent, *level) != 0);
            }
            exhaustive = tests.is_empty();
            plans.push(Some((tests, binds)));
        }
        Some(plans)
    }

    fn materialize_constructor(&self, constructor: &QualifiedName, locals: &[String]) -> String {
        let tag = self.constructor_tag(constructor);
        match locals.len() {
            0 => format!("STATIC_DATA0({tag})"),
            n @ 1..=4 => format!("mk_data{n}({tag}, {})", locals.join(", ")),
            n => format!("mk_data({tag}, {n}, {})", locals.join(", ")),
        }
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
                for (index, (_, _label, field)) in the.fields.iter().enumerate() {
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
        // Keep the annotations of the application nodes as well. Optimisation may
        // wrap an original surface call in synthetic applications (for example
        // when forcing an inlined IO action), whose annotations deliberately have
        // no source file. For diagnostics we want the innermost real application:
        // that is the call written by the programmer.
        let mut application_infos = vec![&annotation.type_info];
        let mut head: &Expr = &the.function;
        while let Expr::Apply(inner_annotation, inner) = head {
            application_infos.push(&inner_annotation.type_info);
            args.push(&inner.argument);
            head = &inner.function;
        }
        args.reverse();

        let borrowed_slot = BORROWED_SLICE_PLACES
            .with(|places| places.borrow().get(&(the as *const _ as usize)).cloned());
        if let Some(slot) = borrowed_slot
            && let Some(semantics) = self.intrinsic_for_expr(head)
            && semantics.arity == args.len()
            && let ResultRepresentation::BorrowableSlice {
                owner_argument,
                offset_argument,
                length_argument,
            } = semantics.result
        {
            write!(code, "slice_sub_borrowed(")?;
            self.compile_expr(args[owner_argument], code)?;
            write!(code, ", (size_t)as_int(")?;
            self.compile_expr(args[offset_argument], code)?;
            write!(code, "), (size_t)as_int(")?;
            self.compile_expr(args[length_argument], code)?;
            return write!(code, "), &{slot})");
        }

        if let Some(rebuild) = self.owned_spine_rebuild(head, &args)
            && self.expression_is_owned_spine(rebuild.input)
        {
            let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
            write!(code, "({{ Value _ors{id}_seed = ")?;
            self.compile_expr(rebuild.seed, code)?;
            write!(code, "; Value _ors{id}_input = ")?;
            self.compile_expr(rebuild.input, code)?;
            return write!(
                code,
                "; reverse_constructor_spine_owned(_ors{id}_input, _ors{id}_seed, {}, {}, {}); }})",
                self.constructor_tag(rebuild.step_constructor),
                self.constructor_tag(rebuild.end_constructor),
                rebuild.next_field
            );
        }

        // `omg_wtf_bbq` deliberately keeps the ordinary surface type `Text -> a`.
        // Its private foreign worker has extra diagnostic parameters; inject them
        // here, after all transformations. Since the result is bottom, a source
        // call may legally be over-applied (`omg_wtf_bbq "bad" x`): the first
        // application never returns, so later arguments are unreachable and must
        // not prevent recognition of the panic boundary.
        if !args.is_empty()
            && self
                .intrinsic_for_expr(head)
                .is_some_and(|semantics| semantics.operation == IntrinsicOperation::Panic)
        {
            let has_source =
                |info: &&TypeInfo| crate::source_map::path_of(info.parse_info.file).is_some();
            let head_info = &head.annotation().type_info;
            let message_info = &args[0].annotation().type_info;
            let info = application_infos
                .into_iter()
                // The vector is outermost-to-innermost. Prefer the innermost
                // surviving surface call, then the panic identifier/message,
                // which retain their source annotations when a surrounding node
                // was synthesised by simplification or IO deforestation.
                .rev()
                .find(has_source)
                .or_else(|| {
                    crate::source_map::path_of(head_info.parse_info.file).map(|_| head_info)
                })
                .or_else(|| {
                    crate::source_map::path_of(message_info.parse_info.file).map(|_| message_info)
                })
                .unwrap_or(&annotation.type_info);
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
                c_name(&raw_panic_name()),
                self.compile_constant(&Literal::Text(function)),
                self.compile_constant(&Literal::Text(file)),
                info.parse_info.location.row,
                info.parse_info.location.column,
            )?;
            self.compile_expr(args[0], code)?;
            return write!(code, ")");
        }

        // Materialised surface panics use the private five-argument worker. If
        // bottom polymorphism leaves further applications on the spine, call the
        // nonreturning worker at its saturation point; evaluating later arguments
        // would be both unnecessary and contrary to curried evaluation order.
        if args.len() >= 5
            && self
                .intrinsic_for_expr(head)
                .is_some_and(|semantics| semantics.operation == IntrinsicOperation::RawPanic)
        {
            write!(code, "{}_worker(", c_name(&raw_panic_name()))?;
            for (index, argument) in args.iter().take(5).enumerate() {
                if index > 0 {
                    write!(code, ", ")?;
                }
                self.compile_expr(argument, code)?;
            }
            return write!(code, ")");
        }

        // A saturated write-only packed-array primitive whose replacement is a
        // structural literal can write its already-evaluated leaves straight into
        // the slot. This avoids constructing a canonical record/sum only for the
        // runtime shape interpreter to immediately dismantle it again.
        if direct_write_enabled()
            && args.len() == 3
            && self.intrinsic_for_expr(head).is_some_and(|semantics| {
                semantics.operation == IntrinsicOperation::PackedArraySetUnchecked
            })
        {
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
            // A nominal record can have a fixed canonical ABI that differs from
            // its fully-ground packed-array shape.  In that case the runtime
            // array shape carries an ABI adapter; let `flat_array_set` apply it.
            // Projecting the packed width directly from the canonical value
            // would read beyond (or otherwise misinterpret) the record body.
            if ground
                && self
                    .flat_array_record_adapter_shape(&args[2].annotation().type_info.inferred_type)
                    .is_none()
            {
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

        // `gc_poll` is an opaque call to C's optimiser, so it cannot prove that
        // reloading an immutable Slice's `base` on every byte access gives the
        // same pointer. Loop emission snapshots bases which are invariant on every
        // self back-edge; lower reads from those exact variables to the snapshot.
        // The owner Value remains live in the loop frame, and the collector is
        // non-moving, so this changes neither rooting nor lifetime.
        if args.len() == 2
            && let Some(semantics) = self.intrinsic_for_expr(head)
            && matches!(
                semantics.operation,
                IntrinsicOperation::BytesGetU8 | IntrinsicOperation::BytesGetU64Le
            )
        {
            let source = match strip_ascription(args[0]) {
                Expr::Variable(_, Identifier::Local(LexicalLevel(level))) => {
                    Some(ImmutableSliceSource::Local(*level))
                }
                Expr::Variable(_, Identifier::Captured(capture)) => {
                    Some(ImmutableSliceSource::Captured(capture.index()))
                }
                _ => None,
            };
            let base = source.and_then(|source| {
                IMMUTABLE_SLICE_BASES.with(|bases| bases.borrow().get(&source).cloned())
            });
            if let Some(base) = base {
                match semantics.operation {
                    IntrinsicOperation::BytesGetU8 => write!(
                        code,
                        "VInt((int64_t)slice_base_get_u8({base}, (size_t)as_int("
                    )?,
                    IntrinsicOperation::BytesGetU64Le => write!(
                        code,
                        "VInt((int64_t)slice_base_get_u64_le({base}, (size_t)as_int("
                    )?,
                    _ => unreachable!(),
                }
                self.compile_expr(args[1], code)?;
                return write!(code, ")))");
            }
        }

        // A *saturated* application of a known-arity function (currently the
        // foreign functions) lowers to a direct call to its uncurried worker --
        // no intermediate closures, no allocation. Under- or over-saturated calls
        // fall through to the curried `apply` path below.
        if let Expr::Variable(_, Identifier::Global(qualified_name)) = head {
            if self.arities.get(qualified_name.as_ref()) == Some(&args.len()) {
                let recursive_eliminator = OWNED_RECURSIVE_ELIMINATORS
                    .with(|variants| variants.borrow().get(qualified_name.as_ref()).cloned());
                if let Some(variant) = recursive_eliminator
                    && args
                        .get(variant.product_parameter)
                        .is_some_and(|argument| self.expression_is_owned_tuple(argument))
                    && args.get(variant.input_parameter).is_some_and(|argument| {
                        self.expression_is_owned_spine(argument)
                            && !Self::constructor_application(argument)
                                .is_some_and(|(_, fields)| fields.is_empty())
                    })
                    && self.owned_spine_argument_is_exclusive(&args, variant.input_parameter)
                {
                    write!(
                        code,
                        "{}_owned_tuple_{}_data_{}_worker(",
                        c_name(qualified_name.as_ref()),
                        variant.product_parameter,
                        variant.input_parameter
                    )?;
                    for (index, argument) in args.iter().enumerate() {
                        if index != 0 {
                            write!(code, ", ")?;
                        }
                        self.compile_expr(argument, code)?;
                    }
                    return write!(code, ")");
                }
                let owned_data_parameter = OWNED_DATA_WORKER_VARIANTS.with(|variants| {
                    variants
                        .borrow()
                        .get(qualified_name.as_ref())
                        .and_then(|parameters| {
                            parameters.iter().copied().find(|parameter| {
                                args.get(*parameter).is_some_and(|argument| {
                                    self.expression_is_owned_spine(argument)
                                        && !Self::constructor_application(argument)
                                            .is_some_and(|(_, fields)| fields.is_empty())
                                }) && self.owned_data_argument_is_exclusive(
                                    qualified_name.as_ref(),
                                    &args,
                                    *parameter,
                                )
                            })
                        })
                });
                if let Some(parameter) = owned_data_parameter {
                    write!(
                        code,
                        "{}_owned_data_{}_worker(",
                        c_name(qualified_name.as_ref()),
                        parameter
                    )?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            write!(code, ", ")?;
                        }
                        self.compile_expr(arg, code)?;
                    }
                    return write!(code, ")");
                }
                let dynamic_data_parameter = OWNED_DATA_WORKER_VARIANTS.with(|variants| {
                    variants
                        .borrow()
                        .get(qualified_name.as_ref())
                        .and_then(|parameters| {
                            parameters.iter().find_map(|parameter| {
                                let condition = args
                                    .get(*parameter)
                                    .and_then(|argument| self.dynamic_owned_condition(argument))?;
                                if condition == "true"
                                    || args.iter().enumerate().any(|(index, argument)| {
                                        index != *parameter
                                            && self.dynamic_owned_condition(argument).as_deref()
                                                == Some(condition.as_str())
                                    })
                                {
                                    return None;
                                }
                                Some((*parameter, condition))
                            })
                        })
                });
                if let Some((parameter, condition)) = dynamic_data_parameter {
                    write!(
                        code,
                        "({condition} ? {}_owned_data_{}_worker(",
                        c_name(qualified_name.as_ref()),
                        parameter
                    )?;
                    for (index, argument) in args.iter().enumerate() {
                        if index != 0 {
                            write!(code, ", ")?;
                        }
                        self.compile_expr(argument, code)?;
                    }
                    write!(code, ") : {}_worker(", c_name(qualified_name.as_ref()))?;
                    for (index, argument) in args.iter().enumerate() {
                        if index != 0 {
                            write!(code, ", ")?;
                        }
                        self.compile_expr(argument, code)?;
                    }
                    return write!(code, "))");
                }
                let owned_spine_parameter = OWNED_SPINE_WORKER_VARIANTS.with(|variants| {
                    variants
                        .borrow()
                        .get(qualified_name.as_ref())
                        .and_then(|parameters| {
                            parameters.iter().copied().find(|parameter| {
                                args.get(*parameter).is_some_and(|argument| {
                                    self.expression_is_owned_spine(argument)
                                }) && self.owned_spine_argument_is_exclusive(&args, *parameter)
                            })
                        })
                });
                if let Some(parameter) = owned_spine_parameter {
                    write!(
                        code,
                        "{}_owned_spine_{}_worker(",
                        c_name(qualified_name.as_ref()),
                        parameter
                    )?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            write!(code, ", ")?;
                        }
                        self.compile_expr(arg, code)?;
                    }
                    return write!(code, ")");
                }
                let dynamic_spine_parameter = OWNED_SPINE_WORKER_VARIANTS.with(|variants| {
                    variants
                        .borrow()
                        .get(qualified_name.as_ref())
                        .and_then(|parameters| {
                            parameters.iter().find_map(|parameter| {
                                args.get(*parameter)
                                    .and_then(|argument| self.dynamic_owned_condition(argument))
                                    .filter(|condition| condition != "true")
                                    .map(|condition| (*parameter, condition))
                            })
                        })
                });
                if let Some((parameter, condition)) = dynamic_spine_parameter {
                    write!(
                        code,
                        "({condition} ? {}_owned_spine_{}_worker(",
                        c_name(qualified_name.as_ref()),
                        parameter
                    )?;
                    for (index, argument) in args.iter().enumerate() {
                        if index != 0 {
                            write!(code, ", ")?;
                        }
                        self.compile_expr(argument, code)?;
                    }
                    write!(code, ") : {}_worker(", c_name(qualified_name.as_ref()))?;
                    for (index, argument) in args.iter().enumerate() {
                        if index != 0 {
                            write!(code, ", ")?;
                        }
                        self.compile_expr(argument, code)?;
                    }
                    return write!(code, "))");
                }
                let owned_tuple_parameter = OWNED_TUPLE_WORKER_VARIANTS.with(|variants| {
                    variants
                        .borrow()
                        .get(qualified_name.as_ref())
                        .and_then(|parameters| {
                            parameters.iter().copied().find(|parameter| {
                                args.get(*parameter).is_some_and(|argument| {
                                    annotation.type_info.inferred_type
                                        == argument.annotation().type_info.inferred_type
                                        && self.expression_is_owned_tuple(argument)
                                })
                            })
                        })
                });
                if let Some(parameter) = owned_tuple_parameter {
                    write!(
                        code,
                        "{}_owned_tuple_{}_worker(",
                        c_name(qualified_name.as_ref()),
                        parameter
                    )?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            write!(code, ", ")?;
                        }
                        self.compile_expr(arg, code)?;
                    }
                    return write!(code, ")");
                }
                let owned_rebuild = args.len() == 1
                    && OWNED_REBUILD_WORKER_VARIANTS
                        .with(|variants| variants.borrow().contains(qualified_name.as_ref()))
                    && self.expression_is_owned_spine(args[0])
                    && self.owned_spine_argument_is_exclusive(&args, 0);
                if owned_rebuild {
                    write!(
                        code,
                        "{}_owned_rebuild_worker(",
                        c_name(qualified_name.as_ref())
                    )?;
                } else {
                    write!(code, "{}_worker(", c_name(qualified_name.as_ref()))?;
                }
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
            let owned_last = args.last().is_some_and(|last| {
                annotation.type_info.inferred_type == last.annotation().type_info.inferred_type
                    && self.expression_is_owned_tuple(last)
            });
            write!(
                code,
                "{}(",
                if owned_last {
                    "apply_n_owned_last"
                } else {
                    "apply_n"
                }
            )?;
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
                write!(code, "Value {name} = ")?;
                self.compile_expr(element, code)?;
                write!(code, "; ")?;
                values.push(name);
                continue;
            }

            let mut prelude = Vec::new();
            // Closure frames use the same capped flat-record layout as ordinary
            // record objects. The array runtime shape is deliberately deeper and
            // cannot describe these slots: a one-field nested record is one boxed
            // pointer here, while an array element recursively packs its field.
            let leaves = self.flat_leaves(element, place.width, &mut prelude);
            if leaves.len() != place.width {
                return Err(fmt::Error);
            }
            for binding in prelude {
                write!(code, "{binding} ")?;
            }
            for (word, leaf) in leaves.into_iter().enumerate() {
                let name = format!("{stem}_{capture}_{word}");
                write!(code, "Value {name} = {leaf}; ")?;
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

                // Capture temporaries stay C-live until this frame is initialised, and
                // the frame stays live until the direct call returns. Across a call,
                // the ABI therefore puts each live word either on the stack or in a
                // callee-saved register; `gc_park` explicitly spills those registers
                // before publishing the stack. The collector is non-moving, so no
                // address needs to be reloaded after a safepoint. Making both the
                // temporaries and aggregate `volatile` duplicated that rooting and
                // prevented SROA/LICM throughout an inlined hot loop.
                write!(
                    code,
                    "static const ClosureDesc _sd{id} = {{{name}, {descriptor_worker}, {descriptor_arity}}}; "
                )?;
                write!(
                    code,
                    "_Alignas(MARM_VALUE_ALIGNMENT) struct {{ const ClosureDesc *desc; Value caps[{captures}]; }} _sc{id} = {{&_sd{id}, {{"
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
                .all(|(_, _, field)| Self::self_references_are_calls(field, arity)),
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
        let owned_worker = OWNED_TUPLE_STEP_WORKERS.with(|workers| {
            workers
                .borrow()
                .contains_key(&the.lifted_name)
                .then(|| format!("{name}_owned_tuple_uworker"))
                .unwrap_or_else(|| "NULL".to_owned())
        });
        let owned_data_worker = OWNED_PRODUCT_DATA_STEP_WORKERS.with(|workers| {
            workers
                .borrow()
                .contains_key(&the.lifted_name)
                .then(|| format!("{name}_owned_tuple_data_uworker"))
                .unwrap_or_else(|| "NULL".to_owned())
        });
        // Capture-free: identical + immutable, so a single static instance, no heap
        // allocation at all (mirrors the borrowed-string descriptors).
        if env.elements.is_empty() {
            if owned_worker == "NULL" && owned_data_worker == "NULL" {
                return write!(code, "STATIC_CLOSURE0({name}, {worker}, {arity})");
            }
            if owned_data_worker != "NULL" {
                return write!(
                    code,
                    "STATIC_CLOSURE0_OWNED_DATA({name}, {worker}, {arity}, {owned_worker}, {owned_data_worker})"
                );
            }
            return write!(
                code,
                "STATIC_CLOSURE0_OWNED({name}, {worker}, {arity}, {owned_worker})"
            );
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
            "static const ClosureDesc __d = {{{name}, {worker}, {arity}, {owned_worker}, {owned_data_worker}}}; "
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
            // On wasm32 a `Slice` is only 4-byte aligned, and a body address with
            // bit 2 set reads as a borrowed tuple. Every emitted Value body uses
            // the runtime's shared tagged-pointer alignment contract.
            Literal::Text(x) => {
                // The `Text` may hold characters that are special in a C string literal
                // (quotes, backslashes, newlines from source escapes), so re-escape it.
                // `sizeof` then still counts the C-decoded byte length, sizing the body
                // and the slice correctly.
                let x = c_string_escape(x);
                format!(
                    "({{ _Alignas(MARM_VALUE_ALIGNMENT) static const struct {{ GcHeader gch; char b[sizeof(\"{x}\")]; }} \
                     __marm_b = {{{{sizeof(\"{x}\"), 0, OBJ_BYTES, MARM_ETERNAL}}, \"{x}\"}}; \
                     _Alignas(MARM_VALUE_ALIGNMENT) static const struct {{ GcHeader gch; Slice s; }} \
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
        let Expr::Record(_, record) = value else {
            return None;
        };
        let mut prelude = Vec::new();
        // The SAME words `compile_record` would build the object from -- see
        // `record_literal_leaves`. Splatting the literal independently is what let the
        // two representations drift apart.
        let leaves = self.record_literal_leaves(ty, record, &mut prelude)?;
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

        if Self::max_local_uses_per_path(body, *level) <= 1
            && let Expr::If(_, branch) = strip_ascription(bound)
        {
            let consequent_owned = self.dynamic_owned_condition(&branch.consequent);
            let alternate_owned = self.dynamic_owned_condition(&branch.alternate);
            if consequent_owned.is_some() || alternate_owned.is_some() {
                let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
                write!(code, "({{ Value l{level}; bool _own{id}; if (as_bool(")?;
                self.compile_expr(&branch.predicate, code)?;
                write!(code, ")) {{ l{level} = ")?;
                self.compile_expr(&branch.consequent, code)?;
                write!(
                    code,
                    "; _own{id} = {}; }} else {{ l{level} = ",
                    consequent_owned.as_deref().unwrap_or("false")
                )?;
                self.compile_expr(&branch.alternate, code)?;
                write!(
                    code,
                    "; _own{id} = {}; }} ",
                    alternate_owned.as_deref().unwrap_or("false")
                )?;
                let previous_dynamic =
                    Self::install_dynamic_owned_spine_locals([(*level, format!("_own{id}"))]);
                let result = self.compile_expr(body, code);
                Self::restore_dynamic_owned_spine_locals(previous_dynamic);
                result?;
                return write!(code, "; }})");
            }
        }

        let dynamic_bound = (Self::max_local_uses_per_path(body, *level) <= 1)
            .then(|| self.dynamic_owned_condition(bound))
            .flatten()
            .filter(|condition| condition != "true");
        let bound_owned = self.expression_is_owned_spine(bound);
        write!(code, "({{ Value l{level} = ")?;
        self.compile_expr(bound, code)?;
        write!(code, "; ")?;
        if let Some(condition) = dynamic_bound {
            let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
            write!(code, "bool _own{id} = {condition}; ")?;
            let previous_dynamic =
                Self::install_dynamic_owned_spine_locals([(*level, format!("_own{id}"))]);
            let result = self.compile_expr(body, code);
            Self::restore_dynamic_owned_spine_locals(previous_dynamic);
            result?;
            return write!(code, "; }})");
        }
        if bound_owned
            && let Expr::If(_, branch) = strip_ascription(body)
            && Self::local_use_count(&branch.consequent, *level) <= 1
            && Self::local_use_count(&branch.alternate, *level) <= 1
        {
            write!(code, "(as_bool(")?;
            self.compile_expr(&branch.predicate, code)?;
            write!(code, ") ? ")?;
            let previous = Self::install_owned_spine_locals([*level]);
            let consequent = self.compile_expr(&branch.consequent, code);
            Self::restore_owned_spine_locals(previous);
            consequent?;
            write!(code, " : ")?;
            let previous = Self::install_owned_spine_locals([*level]);
            let alternate = self.compile_expr(&branch.alternate, code);
            Self::restore_owned_spine_locals(previous);
            alternate?;
            return write!(code, "); }})");
        }
        let previous = if bound_owned && Self::local_use_count(body, *level) == 1 {
            Some(Self::install_owned_spine_locals([*level]))
        } else {
            None
        };
        let result = self.compile_expr(body, code);
        if let Some(previous) = previous {
            Self::restore_owned_spine_locals(previous);
        }
        result?;
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

    fn fresh_backedge_parameters(
        &self,
        target: SelfCall,
        arity: usize,
        expression: &Expr,
    ) -> Vec<usize> {
        fn visit(
            program: &lambda_lift::Program,
            target: SelfCall<'_>,
            arity: usize,
            expression: &Expr,
            fresh: &mut [bool],
            seen: &mut bool,
        ) {
            let expression = strip_ascription(expression);
            if program.is_self_call(target, arity, expression) {
                *seen = true;
                let mut head = expression;
                let mut arguments = Vec::new();
                while let Expr::Apply(_, application) = head {
                    arguments.push(application.argument.as_ref());
                    head = strip_ascription(&application.function);
                }
                arguments.reverse();
                for (index, argument) in arguments.into_iter().enumerate() {
                    fresh[index] &= program.expression_is_owned_spine(argument);
                }
                return;
            }
            match expression {
                Expr::If(_, branch) => {
                    visit(program, target, arity, &branch.consequent, fresh, seen);
                    visit(program, target, arity, &branch.alternate, fresh, seen);
                }
                Expr::Let(_, binding) => visit(program, target, arity, &binding.body, fresh, seen),
                Expr::Sequence(_, sequence) => {
                    visit(program, target, arity, &sequence.and_then, fresh, seen)
                }
                Expr::Deconstruct(_, deconstruct) => {
                    for clause in &deconstruct.match_clauses {
                        visit(program, target, arity, &clause.consequent, fresh, seen);
                    }
                }
                _ => {}
            }
        }

        let mut fresh = vec![true; arity];
        let mut seen = false;
        visit(self, target, arity, expression, &mut fresh, &mut seen);
        if !seen {
            return Vec::new();
        }
        fresh
            .into_iter()
            .enumerate()
            .filter_map(|(index, fresh)| fresh.then_some(index))
            .collect()
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
                if Self::max_local_uses_per_path(&the.body, *level) <= 1
                    && let Expr::If(_, branch) = strip_ascription(&the.bound)
                {
                    let consequent_owned = self.dynamic_owned_condition(&branch.consequent);
                    let alternate_owned = self.dynamic_owned_condition(&branch.alternate);
                    if consequent_owned.is_some() || alternate_owned.is_some() {
                        let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
                        write!(code, "Value l{level}; bool _own{id}; if (as_bool(")?;
                        self.compile_expr(&branch.predicate, code)?;
                        write!(code, ")) {{ l{level} = ")?;
                        self.compile_expr(&branch.consequent, code)?;
                        write!(
                            code,
                            "; _own{id} = {}; }} else {{ l{level} = ",
                            consequent_owned.as_deref().unwrap_or("false")
                        )?;
                        self.compile_expr(&branch.alternate, code)?;
                        write!(
                            code,
                            "; _own{id} = {}; }} ",
                            alternate_owned.as_deref().unwrap_or("false")
                        )?;
                        let previous_dynamic = Self::install_dynamic_owned_spine_locals([(
                            *level,
                            format!("_own{id}"),
                        )]);
                        let result = self.compile_tail(target, arity, &the.body, code);
                        Self::restore_dynamic_owned_spine_locals(previous_dynamic);
                        return result;
                    }
                }
                write!(code, "Value l{level} = ")?;
                self.compile_expr(&the.bound, code)?;
                write!(code, "; ")?;
                let dynamic_bound = (Self::max_local_uses_per_path(&the.body, *level) <= 1)
                    .then(|| self.dynamic_owned_condition(&the.bound))
                    .flatten()
                    .filter(|condition| condition != "true");
                if let Some(condition) = dynamic_bound {
                    let id = MATCH_ID.fetch_add(1, Ordering::Relaxed);
                    write!(code, "bool _own{id} = {condition}; ")?;
                    let previous_dynamic =
                        Self::install_dynamic_owned_spine_locals([(*level, format!("_own{id}"))]);
                    let result = self.compile_tail(target, arity, &the.body, code);
                    Self::restore_dynamic_owned_spine_locals(previous_dynamic);
                    result
                } else {
                    self.compile_tail(target, arity, &the.body, code)
                }
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

                // Tail-position counterpart of the tuple producer/consumer fusion
                // in `compile_deconstruct`.
                if let Expr::Tuple(_, tuple) = strip_ascription(&the.scrutinee)
                    && !tuple.elements.is_empty()
                {
                    let locals = (0..tuple.elements.len())
                        .map(|index| format!("_tscrut{id}_{index}"))
                        .collect::<Vec<_>>();
                    if let Some(plans) = self.plan_direct_tuple_match(&the.match_clauses, &locals) {
                        write!(code, "{{ ")?;
                        for (local, element) in locals.iter().zip(&tuple.elements) {
                            write!(code, "Value {local} = ")?;
                            self.compile_expr(element, code)?;
                            write!(code, "; ")?;
                        }
                        let mut first = true;
                        let mut exhaustive = false;
                        for (clause, (tests, binds)) in the.match_clauses.iter().zip(&plans) {
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
                            for (level, path) in binds {
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
                }

                // Tail-position counterpart of generic constructor scalar
                // replacement in `compile_deconstruct`.
                if let Some((constructor, arguments)) =
                    Self::constructor_application(&the.scrutinee)
                    && !arguments.is_empty()
                    && self.constructor_tags.contains_key(constructor)
                    && !self.newtype_constructors.contains(constructor)
                {
                    let locals = (0..arguments.len())
                        .map(|index| format!("_tcscrut{id}_{index}"))
                        .collect::<Vec<_>>();
                    if let Some(plans) =
                        self.plan_direct_constructor_match(constructor, &the.match_clauses, &locals)
                    {
                        write!(code, "{{ ")?;
                        for (local, argument) in locals.iter().zip(&arguments) {
                            write!(code, "Value {local} = ")?;
                            self.compile_expr(argument, code)?;
                            write!(code, "; ")?;
                        }
                        let mut first = true;
                        let mut exhaustive = false;
                        for (clause, plan) in the.match_clauses.iter().zip(&plans) {
                            let Some((tests, binds)) = plan else {
                                continue;
                            };
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
                            for (level, path) in binds {
                                write!(code, "Value l{level} = {path}; ")?;
                            }
                            self.compile_tail(target, arity, &clause.consequent, code)?;
                            write!(code, " }}")?;
                            if exhaustive {
                                break;
                            }
                        }
                        if first {
                            write!(code, "match_fail();")?;
                        } else if !exhaustive {
                            write!(code, " else {{ match_fail(); }}")?;
                        }
                        return write!(code, " }}");
                    }
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
                let escape = BORROWED_SLICE_PLACES.with(|places| !places.borrow().is_empty());
                write!(code, "{{ ")?;
                for (i, arg) in args.iter().enumerate() {
                    let dynamic_target = DYNAMIC_OWNED_SPINE_LOCALS
                        .with(|current| current.borrow().get(&i).cloned());
                    let dynamic_result = dynamic_target.as_ref().map(|_| {
                        self.dynamic_owned_condition(arg)
                            .unwrap_or_else(|| "false".into())
                    });
                    write!(code, "Value _a{id}_{i} = ")?;
                    if escape {
                        write!(code, "gc_escape_borrowed(")?;
                    }
                    let last_use = TAIL_BACKEDGE_OWNED_LOCALS.with(|owned| {
                        owned
                            .borrow()
                            .iter()
                            .copied()
                            .filter(|level| {
                                Self::local_use_count(arg, *level) != 0
                                    && args[i + 1..]
                                        .iter()
                                        .all(|later| Self::local_use_count(later, *level) == 0)
                            })
                            .collect::<Vec<_>>()
                    });
                    let previous_owned = Self::install_owned_spine_locals(last_use);
                    let result = self.compile_expr(arg, code);
                    Self::restore_owned_spine_locals(previous_owned);
                    result?;
                    if escape {
                        write!(code, ")")?;
                    }
                    write!(code, "; ")?;
                    if let Some(condition) = dynamic_result {
                        write!(code, "bool _ao{id}_{i} = {condition}; ")?;
                    }
                }
                for i in 0..arity {
                    write!(code, "l{i} = _a{id}_{i}; ")?;
                    if let Some(flag) =
                        DYNAMIC_OWNED_SPINE_LOCALS.with(|current| current.borrow().get(&i).cloned())
                    {
                        write!(code, "{flag} = _ao{id}_{i}; ")?;
                    }
                }
                if let Some(label) = TAIL_BACKEDGE_LABEL.with(|current| current.borrow().clone()) {
                    write!(code, "goto {label}; }}")
                } else {
                    write!(code, "continue; }}")
                }
            }

            _ => {
                let escape = BORROWED_SLICE_PLACES.with(|places| !places.borrow().is_empty());
                write!(code, "return ")?;
                if escape {
                    write!(code, "gc_escape_borrowed(")?;
                }
                self.compile_expr(expr, code)?;
                if escape {
                    write!(code, ")")?;
                }
                write!(code, ";")
            }
        }
    }
}
