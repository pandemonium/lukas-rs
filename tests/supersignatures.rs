//! Phase 1 of supersignatures (see notes/supersignatures.md): a `signature` may
//! carry a `|-` supersignature context, which is parsed, stored, and checked for
//! cycles. No entailment semantics yet — a supersignature is inert here, so a
//! super-annotated signature behaves exactly like a plain one.

use std::{fs, path::PathBuf};

use lukas::{
    ast::{self, ROOT_MODULE_NAME, namer::QualifiedName},
    compiler::Compiler,
    parser::IdentifierPath,
};

fn eval_start(test_name: &str, source: &str) -> Result<String, String> {
    let dir = std::env::temp_dir().join(format!("lukas_super_{test_name}"));
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("Root.lady"), source).unwrap();

    let compiler = Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: dir,
        scheme_file: None,
    };

    let env = compiler
        .compile_and_initialize()
        .map_err(|e| format!("compilation failed: {e}"))?;

    env.call(
        &QualifiedName::new(IdentifierPath::new(ROOT_MODULE_NAME), "start"),
        ast::Literal::Int(0),
    )
    .map(|value| format!("{value}"))
    .map_err(|e| format!("evaluation failed: {e:?}"))
}

/// A signature with a supersignature context (`Eq α |- Ord`) parses, stores the
/// super, and — since Phase 1 attaches no semantics — compiles and dispatches
/// exactly like an unannotated signature.
#[test]
fn supersignature_context_is_inert() {
    let source = r#"
signature Eq ::= ∀α.
  { eqv :: α -> α -> Bool }

signature Ord ::= ∀α. Eq α |-
  { lte :: α -> α -> Bool }

witness Eq Int :=
  { eqv := λp q. p = q }

witness Ord Int :=
  { lte := λp q. p = q }

start :: Int -> Int := λ_.
  if eqv 2 2 then (if lte 4 4 then 7 else 1) else 0
"#;

    assert_eq!(eval_start("inert", source), Ok("7".to_string()));
}

// NOTE (parametric witnesses): Phase 3 also *populates* the `$super$` field for
// parametric/derived witnesses — the value comes from `resolve_witness` against the
// builder's dictionary parameters, verified via tracing. It is not covered by an
// end-to-end test here for two reasons: (1) observing a populated super-field
// requires the entailment phase (Phase 4), which projects it; and (2) the natural
// minimal repros use a *constructor-headed* premise (e.g. `Super (Box α) |- Sub (Box α)`),
// which hits a PRE-EXISTING limitation unrelated to supersignatures — such a premise
// is baked in as evidence (it is not `is_parametric`) yet the witness is still
// registered as taking it as an argument, so the built record gets applied as a
// function at the use site. That reproduces with no supersignature at all.

/// Phase 4 (entailment): a function constrained only by the *sub*signature may
/// call a *super*signature's method. The super dictionary is projected out of the
/// sub dictionary's `$super$` field — no separate constraint needed.
#[test]
fn superclass_method_reachable_via_subclass_constraint() {
    let source = r#"
signature Eq ::= ∀α.
  { eqv :: α -> α -> Bool }

signature Ord ::= ∀α. Eq α |-
  { lte :: α -> α -> Bool }

witness Eq Int :=
  { eqv := λp q. p = q }

witness Ord Int :=
  { lte := λp q. p = q }

useOrd :: ∀α. Ord α |- α -> Bool := λx. eqv x x

start :: Int -> Int := λ_. if useOrd 5 then 1 else 0
"#;

    assert_eq!(eval_start("entail", source), Ok("1".to_string()));
}

/// Entailment is transitive: a `Num α |- …` function reaches `Eq`'s method through
/// two projection hops (`Num → Ord → Eq`).
#[test]
fn transitive_superclass_method() {
    let source = r#"
signature Eq ::= ∀α.
  { eqv :: α -> α -> Bool }

signature Ord ::= ∀α. Eq α |-
  { lte :: α -> α -> Bool }

signature Num ::= ∀α. Ord α |-
  { zero :: α }

witness Eq Int :=
  { eqv := λp q. p = q }

witness Ord Int :=
  { lte := λp q. p = q }

witness Num Int :=
  { zero := 0 }

useNum :: ∀α. Num α |- α -> Bool := λx. eqv x x

start :: Int -> Int := λ_. if useNum 7 then 1 else 0
"#;

    assert_eq!(eval_start("transitive", source), Ok("1".to_string()));
}

/// A subclass-constrained function may use *both* a super method and its own
/// method: `lte` comes from the `Ord` dictionary directly, `eqv` from its
/// `$super$Eq` projection.
#[test]
fn subclass_and_superclass_methods_together() {
    let source = r#"
signature Eq ::= ∀α.
  { eqv :: α -> α -> Bool }

signature Ord ::= ∀α. Eq α |-
  { lte :: α -> α -> Bool }

witness Eq Int :=
  { eqv := λp q. p = q }

witness Ord Int :=
  { lte := λp q. p = q }

both :: ∀α. Ord α |- α -> α -> Bool := λx y.
  if eqv x y then lte x y else lte y x

start :: Int -> Int := λ_. if both 3 3 then 5 else 0
"#;

    assert_eq!(eval_start("both", source), Ok("5".to_string()));
}

/// Mutually-requiring signatures are a cycle and must be rejected at
/// compile time, not hang or overflow.
#[test]
fn mutual_supersignature_cycle_rejected() {
    let source = r#"
signature Fee ::= ∀α. Fum α |-
  { fee :: α -> α }

signature Fum ::= ∀α. Fee α |-
  { fum :: α -> α }

start :: Int -> Int := λ_. 0
"#;

    let err = eval_start("mutual_cycle", source).expect_err("expected a cycle rejection");
    assert!(
        err.starts_with("compilation failed"),
        "expected a compilation failure, got: {err}"
    );
}

/// A signature requiring itself is a cycle too.
#[test]
fn self_supersignature_cycle_rejected() {
    let source = r#"
signature Loop ::= ∀α. Loop α |-
  { step :: α -> α }

start :: Int -> Int := λ_. 0
"#;

    let err = eval_start("self_cycle", source).expect_err("expected a self-cycle rejection");
    assert!(
        err.starts_with("compilation failed"),
        "expected a compilation failure, got: {err}"
    );
}

/// A method that carries its own `|-` constraint must NOT be mistaken for a
/// supersignature context (the method's `|-` is inside the `{ … }` block). This
/// guards the `has_type_constraints` lookahead in the signature parser.
#[test]
fn method_constraint_is_not_a_supersignature() {
    let source = r#"
use Stdlib.

Box ::= ∀α. MkBox α

signature Squash ::= ∀m : * -> *.
  { squash :: ∀α. Monoid α |- m α -> α
  }

witness Squash Box :=
  { squash := λb. deconstruct b into MkBox a -> mappend a mempty
  }

start :: Int -> Int := λ_. squash (MkBox 5)
"#;

    assert_eq!(eval_start("method_constraint", source), Ok("5".to_string()));
}
