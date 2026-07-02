//! Regression tests for the type-class (signature / witness) machinery.
//!
//! Each test writes a minimal hermetic program to a temp dir, compiles and
//! statically initializes it, then calls `start` and asserts on the returned
//! value. `start` *returns* its result (rather than printing) so we can assert
//! on it directly instead of scraping stdout.

use std::{fs, path::PathBuf};

use lukas::{
    ast::{self, ROOT_MODULE_NAME, namer::QualifiedName},
    compiler::Compiler,
    parser::IdentifierPath,
};

/// Compile `source` as the Root module and evaluate `start 0`, returning the
/// `Display` of the resulting value.
fn eval_start(test_name: &str, source: &str) -> Result<String, String> {
    let dir = std::env::temp_dir().join(format!("lukas_tc_{test_name}"));
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

/// A conditional / derived instance: `Eq (Box α)` given `Eq α`. Resolving `eq`
/// on two boxes must select the derived witness and discharge its `Eq α`
/// premise with `Eq Int`.
///
/// Currently fails: the witness's evidence dictionary is bound to the
/// self-reference slot (#0) instead of the dictionary parameter slot (#1), so
/// the element selector receives the builder closure and projects a field off
/// it -> BadProjection.
#[test]
fn derived_instance_discharges_premise() {
    let source = r#"
Box ::= ∀α. MkBox α

signature Eq ::= ∀α.
  { eq :: α -> α -> Bool
  }

witness Eq Int :=
  { eq := λp q. p = q
  }

witness ∀α. Eq α |- Eq (Box α) :=
  { eq := λx y.
      deconstruct x into
        MkBox a ->
          deconstruct y into
            MkBox b -> eq a b
  }

start :: Int -> Int := λ_.
  if eq (MkBox 3) (MkBox 3) then 1 else 0
"#;

    assert_eq!(eval_start("derived_instance", source), Ok("1".to_string()));
}

/// A *recursive* derived instance: `Eq (List α)` given `Eq α`, whose body calls
/// `eq` on sub-lists (the self instance) as well as on elements (the premise).
///
/// The inferred self-recursive constraint `Eq (List α)` — which matches the
/// witness's own head — is resolved via the instance (not a fresh parameter) and
/// tied back to the self-reference slot, reconstructing the recursive dictionary
/// from the `Eq α` premise.
#[test]
fn recursive_derived_instance() {
    let source = r#"
List ::= ∀α. Nil | Cons α (List α)

signature Eq ::= ∀α.
  { eq :: α -> α -> Bool
  }

witness Eq Int :=
  { eq := λp q. p = q
  }

witness ∀α. Eq α |- Eq (List α) :=
  { eq := λxs ys.
      deconstruct xs, ys into
        Cons x xs, Cons y ys -> eq x y and eq xs ys
      | Nil, Nil             -> true
      | otherwise            -> false
  }

start :: Int -> Int := λ_.
  if eq (Cons 1 (Cons 2 Nil)) (Cons 1 (Cons 2 Nil)) then 1 else 0
"#;

    assert_eq!(eval_start("recursive_derived", source), Ok("1".to_string()));
}

/// A signature method that itself carries an extra constraint:
/// `mconcat :: ∀α. Monoid α |- m α -> α`. The witness method body is lifted to a
/// top-level symbol (`<witness>$mconcat`) so its `Monoid α` constraint is
/// discharged into a leading dictionary parameter of the *field* (rank-2), and
/// the witness record stays unconstrained.
#[test]
fn method_level_constraint_discharges() {
    let source = r#"
Box ::= ∀α. MkBox α

signature Monoid ::= ∀α.
  { mempty  :: α
    mappend :: α -> α -> α
  }

witness Monoid Int :=
  { mempty  := 0
    mappend := λp q. p + q
  }

signature Mconcat ::= ∀m : * -> *.
  { mconcat :: ∀α. Monoid α |- m α -> α
  }

witness Mconcat Box :=
  { mconcat := λb. deconstruct b into MkBox a -> mappend a mempty
  }

start :: Int -> Int := λ_.
  mconcat (MkBox 5)
"#;

    assert_eq!(eval_start("method_constraint", source), Ok("5".to_string()));
}

/// Traversable: a method (`traverse`) constrained by a *distinct* higher-kinded
/// class (`Applicative f`), i.e. two dictionaries whose classes sort in the
/// opposite order to the way the selector projects them. Exercises the
/// multi-dictionary ordering: the accessor selector must inject `Traversable`
/// and `Applicative` in the order its body expects, not `BTreeSet` order.
#[test]
fn traversable_multi_dictionary_order() {
    let source = r#"
List ::= ∀α. Nil | Cons α (List α)
Perhaps ::= ∀α. Nope | This α

signature Applicative ::= ∀f : * -> *.
  { pure  :: ∀α. α -> f α
    apply :: ∀α β. f (α -> β) -> f α -> f β
  }

witness Applicative Perhaps :=
  { pure  := λx. This x
    apply := λff fa.
      deconstruct ff into
        Nope   -> Nope
      | This f ->
          deconstruct fa into
            Nope   -> Nope
          | This a -> This (f a)
  }

liftA2 :: ∀f : *->* α β γ. Applicative f |- (α -> β -> γ) -> f α -> f β -> f γ :=
  λh fa fb. apply (apply (pure h) fa) fb

fold_right :: ∀z α. (α -> z -> z) -> z -> List α -> z :=
  λf z xs.
    deconstruct xs into
      Cons a tail -> f a (fold_right f z tail)
    | Nil         -> z

signature Traversable ::= ∀t : * -> *.
  { traverse :: ∀f : * -> * α β. Applicative f |- (α -> f β) -> t α -> f (t β)
  }

witness Traversable List :=
  { traverse := λf xs.
      deconstruct xs into
        Nil          -> pure Nil
      | Cons a tail  -> liftA2 Cons (f a) (traverse f tail)
  }

start :: Int -> Int := λ_.
  deconstruct traverse (λx. This x) (Cons 1 (Cons 2 (Cons 3 Nil))) into
    This ys -> fold_right (λa z. a + z) 0 ys
  | Nope    -> 0
"#;

    assert_eq!(eval_start("traversable", source), Ok("6".to_string()));
}
