use std::{fs, path::PathBuf};

use lukas::compiler::{Backend, Compiler};

fn compiler_for(test_name: &str, source: &str) -> Compiler {
    let dir = std::env::temp_dir().join(format!("lukas_type_error_{test_name}"));
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("Root.lady"), source).unwrap();
    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: dir,
        backend: Backend::Native,
        output_file: None,
    }
}

#[test]
fn coproduct_pattern_against_function_is_a_located_type_error() {
    let source = r#"
Box ::= Box Int

bad :: (Int -> Int) -> Int := λvalue.
  deconstruct value into
    Box n -> n

start := λ_. 0
"#;

    let error = compiler_for("pattern_type_mismatch", source)
        .compiler_main()
        .expect_err("the ill-typed pattern must be rejected");
    let diagnostic = error.to_string();

    assert!(diagnostic.contains("Root.lady:6:"), "{diagnostic}");
    assert!(
        diagnostic.contains("cannot match a value of type"),
        "{diagnostic}"
    );
    assert!(diagnostic.contains("Int -> Int"), "{diagnostic}");
}
