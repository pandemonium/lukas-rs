use std::{fs, path::PathBuf};

use lukas::{
    ast::{self, ROOT_MODULE_NAME, namer::QualifiedName},
    compiler::{self, Compiler},
    parser::IdentifierPath,
};

fn compiler_for(test_name: &str, source: &str, backend: compiler::Backend) -> Compiler {
    let dir = std::env::temp_dir().join(format!("lukas_conversion_{test_name}"));
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("Root.lady"), source).unwrap();
    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: dir,
        backend,
        output_file: None,
    }
}

const SOURCE: &str = r#"
same_int :: Int -> Bool := lambda n. n = 42
same_char :: Char -> Bool := lambda c. c = 'x'
same_bool :: Bool -> Bool := lambda b. b = false
same_text :: Text -> Bool := lambda t. t = "x"

start :: Int -> Int := lambda n. Int.of_float (Float.of_int n + 0.9)
"#;

fn generated_function<'a>(generated: &'a str, name: &str) -> &'a str {
    let marker = format!("Value {name}(");
    let start = generated
        .match_indices(&marker)
        .find_map(|(start, _)| {
            let line_end = generated[start..].find('\n')? + start;
            generated[start..line_end].ends_with(" {").then_some(start)
        })
        .unwrap_or_else(|| panic!("generated function `{name}` not found"));
    let end = generated[start..]
        .find("\n}\n")
        .map(|end| start + end + "\n}\n".len())
        .expect("generated function has no closing brace");
    &generated[start..end]
}

#[test]
fn int_of_float_truncates_toward_zero() {
    let env = compiler_for("interpreter", SOURCE, compiler::Backend::Native)
        .compile_and_initialize()
        .expect("conversion program should compile");
    let value = env
        .call(
            &QualifiedName::new(IdentifierPath::new(ROOT_MODULE_NAME), "start"),
            ast::Literal::Int(42),
        )
        .expect("conversion program should evaluate");
    assert_eq!(format!("{value}"), "42");
}

#[test]
fn native_backend_lowers_monomorphic_primitives() {
    let mut compiler = compiler_for("native", SOURCE, compiler::Backend::Native);
    let output = compiler.source_path.join("conversion.c");
    compiler.output_file = Some(output.clone());
    compiler.compiler_main().expect("native code generation");
    let generated = fs::read_to_string(output).expect("generated C source");
    assert!(generated.contains("prim_int_of_float"));

    for name in [
        "Root_same_int_worker",
        "Root_same_char_worker",
        "Root_same_bool_worker",
    ] {
        let function = generated_function(&generated, name);
        assert!(
            function.contains("prim_word_eq"),
            "immediate equality retained generic runtime dispatch: {function}"
        );
        assert!(!function.contains("prim_eq("), "{function}");
    }
    let text = generated_function(&generated, "Root_same_text_worker");
    assert!(text.contains("prim_text_eq"), "{text}");
}
