//! Regression tests for opaque types (`opaque T ::= ...`) and foreign types
//! (`foreign T`).
//!
//! Each test writes a minimal hermetic program to a temp dir, compiles and
//! statically initializes it, then (for the positive cases) calls `start 0` and
//! asserts on the returned value. Negative cases assert that *compilation*
//! fails — distinguishing a type/name error from a mere runtime failure.

use std::{fs, path::PathBuf};

use lukas::{
    ast::{self, ROOT_MODULE_NAME, namer::QualifiedName},
    compiler::Compiler,
    parser::IdentifierPath,
};

/// Compile `source` as the Root module and evaluate `start 0`, returning the
/// `Display` of the resulting value. Compilation and evaluation failures are
/// reported with distinct prefixes so tests can tell them apart.
fn eval_start(test_name: &str, source: &str) -> Result<String, String> {
    let dir = std::env::temp_dir().join(format!("lukas_of_{test_name}"));
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

/// A `foreign` type has no surface body. It can still appear in signatures; a
/// function taking it need never inspect it.
#[test]
fn foreign_type_is_usable_in_signatures() {
    let source = r#"
foreign File

consume :: File -> Int := λ_. 42

start :: Int -> Int := λ_. 42
"#;

    assert_eq!(
        eval_start("foreign_usable", source),
        Ok("42".to_string())
    );
}

/// Two distinct foreign types must NOT unify. Both are (internally) empty
/// zero-constructor coproducts, so if references were expanded structurally
/// they would collapse into one and this program would type-check. They must be
/// referenced *nominally* instead, so passing a `Socket` where a `File` is
/// expected is a compile-time type error (not a mere runtime failure).
#[test]
fn foreign_types_do_not_unify() {
    let source = r#"
foreign File
foreign Socket

foreign make_socket :: Int -> Socket

sink :: File -> Int := λ_. 0

start :: Int -> Int := λ_. sink (make_socket 0)
"#;

    let result = eval_start("foreign_distinct", source);
    let err = result.expect_err("expected a compile-time type error");
    assert!(
        err.starts_with("compilation failed"),
        "expected a compilation (type) failure, got: {err}"
    );
}

/// An opaque type's *name* is exported and usable across modules — a sibling
/// module can hold values of it and call the owning module's functions — while
/// its constructors stay private. Construction/deconstruction happens inside
/// the declaring module; the outside only moves the value through.
#[test]
fn opaque_type_name_crosses_module_boundary() {
    let source = r#"
module Stack:
  opaque T ::= MkT Int

  make :: Int -> T := λn. MkT n

  unwrap :: T -> Int := λt.
    deconstruct t into
      MkT n -> n

start :: Int -> Int := λ_. Stack.unwrap (Stack.make 7)
"#;

    assert_eq!(
        eval_start("opaque_crosses", source),
        Ok("7".to_string())
    );
}

/// An opaque type's constructor may NOT be named from outside the declaring
/// module. Constructing `Stack.MkT 3` from Root resolves to a constructor whose
/// owning type is opaque outside `Stack`, so name resolution rejects it and
/// compilation fails.
#[test]
fn opaque_constructor_hidden_outside_module() {
    let source = r#"
module Stack:
  opaque T ::= MkT Int

start :: Int -> Int := λ_.
  let hidden = Stack.MkT 3 in 0
"#;

    let result = eval_start("opaque_hidden", source);
    let err = result.expect_err("expected the opaque constructor to be inaccessible");
    assert!(
        err.starts_with("compilation failed"),
        "expected a compilation (name) failure, got: {err}"
    );
}

/// Control for `opaque_constructor_hidden_outside_module`: with a *transparent*
/// type, the very same qualified-constructor access from Root succeeds. This
/// proves the hidden case fails because of opacity, not because qualified
/// constructor access is impossible in general.
#[test]
fn transparent_constructor_accessible_across_module() {
    let source = r#"
module Stack:
  T ::= MkT Int

  unwrap :: T -> Int := λt.
    deconstruct t into
      MkT n -> n

start :: Int -> Int := λ_. Stack.unwrap (Stack.MkT 5)
"#;

    assert_eq!(
        eval_start("transparent_access", source),
        Ok("5".to_string())
    );
}

/// A submodule of the declaring module counts as "inside" and may use the
/// constructors (module + submodules scope).
#[test]
fn opaque_constructor_visible_in_submodule() {
    let source = r#"
module Stack:
  opaque T ::= MkT Int

  module Inner:
    make :: Int -> T := λn. MkT n

  unwrap :: T -> Int := λt.
    deconstruct t into
      MkT n -> n

start :: Int -> Int := λ_. Stack.unwrap (Stack.Inner.make 9)
"#;

    assert_eq!(
        eval_start("opaque_submodule", source),
        Ok("9".to_string())
    );
}
