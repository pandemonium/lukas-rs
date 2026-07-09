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
