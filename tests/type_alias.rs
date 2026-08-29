use std::{fs, path::PathBuf};

use lukas::{
    ast::{self, ROOT_MODULE_NAME, namer::QualifiedName},
    compiler::{self, Compiler},
    parser::IdentifierPath,
};

fn compiler_for(test_name: &str, source: &str) -> Compiler {
    let dir = std::env::temp_dir().join(format!("lukas_alias_{test_name}"));
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("Root.lady"), source).unwrap();
    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: dir,
        backend: compiler::Backend::Native,
        output_file: None,
    }
}

fn eval_start(test_name: &str, source: &str) -> Result<String, String> {
    let env = compiler_for(test_name, source)
        .compile_and_initialize()
        .map_err(|error| format!("{error}"))?;
    env.call(
        &QualifiedName::new(IdentifierPath::new(ROOT_MODULE_NAME), "start"),
        ast::Literal::Int(0),
    )
    .map(|value| format!("{value}"))
    .map_err(|error| format!("{error:?}"))
}

#[test]
fn ground_alias_is_transparent() {
    let source = r#"
alias Number ::= Int

identity :: Number -> Int := lambda x. x
start :: Int -> Int := lambda _. identity 42
"#;
    assert_eq!(eval_start("ground", source), Ok("42".to_owned()));
}

#[test]
fn parameterized_alias_reduces_in_record_and_tuple_types() {
    let source = r#"
Box ::= forall a. { value :: a }
alias Boxed_Pair ::= forall a. Box (a, a)

sum :: Boxed_Pair Int -> Int := lambda box. box.value.0 + box.value.1
start :: Int -> Int := lambda _. sum { value := 20, 22 }
"#;
    assert_eq!(eval_start("parameterized", source), Ok("42".to_owned()));
}

#[test]
fn higher_kinded_alias_accepts_a_partially_applied_constructor() {
    let source = r#"
Box ::= forall a. MkBox a
alias Applied ::= forall f : * -> * a. f a

unwrap :: forall a. Applied Box a -> a := lambda boxed. deconstruct boxed into MkBox value -> value

start :: Int -> Int := lambda _. unwrap (MkBox 42)
"#;
    assert_eq!(eval_start("higher_kinded", source), Ok("42".to_owned()));
}

#[test]
fn alias_body_may_itself_have_higher_kind() {
    let source = r#"
Box ::= forall a. MkBox a
alias Collection ::= Box
alias Constructor_Id ::= forall f : * -> *. f

unwrap :: Constructor_Id Collection Int -> Int := lambda boxed. deconstruct boxed into MkBox value -> value
start :: Int -> Int := lambda _. unwrap (MkBox 42)
"#;
    assert_eq!(
        eval_start("higher_kinded_result", source),
        Ok("42".to_owned())
    );
}

#[test]
fn alias_chains_reduce_transparently() {
    let source = r#"
alias First ::= forall a. Second a
alias Second ::= forall a. (a, a)

sum :: First Int -> Int := lambda pair. pair.0 + pair.1
start :: Int -> Int := lambda _. sum (19, 23)
"#;
    assert_eq!(eval_start("chain", source), Ok("42".to_owned()));
}

#[test]
fn cyclic_aliases_are_rejected() {
    let source = r#"
alias First ::= Second
alias Second ::= First
start :: Int -> Int := lambda x. x
"#;
    let error = compiler_for("cycle", source)
        .compile_and_initialize()
        .expect_err("cyclic aliases must not compile")
        .to_string();
    assert!(error.contains("cyclic type alias"), "{error}");
}

#[test]
fn native_backend_accepts_alias_declarations() {
    let source = r#"
Pair ::= forall a. { left :: a; right :: a }
alias Int_Pair ::= Pair Int

sum :: Int_Pair -> Int := lambda pair. pair.left + pair.right
start :: Int -> Int := lambda _. sum { left := 20; right := 22 }
"#;
    let mut compiler = compiler_for("native_backend", source);
    let output = compiler.source_path.join("alias.c");
    compiler.output_file = Some(output.clone());
    compiler
        .compiler_main()
        .expect("native code generation should accept aliases");
    let generated = fs::read_to_string(output).expect("generated C output");
    assert!(generated.contains("#include"));
}
