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
start :: Int -> Int := lambda n. Int.of_float (Float.of_int n + 0.9)
"#;

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
fn native_backend_lowers_int_of_float_primitive() {
    let mut compiler = compiler_for("native", SOURCE, compiler::Backend::Native);
    let output = compiler.source_path.join("conversion.c");
    compiler.output_file = Some(output.clone());
    compiler.compiler_main().expect("native code generation");
    let generated = fs::read_to_string(output).expect("generated C source");
    assert!(generated.contains("prim_int_of_float"));
}
