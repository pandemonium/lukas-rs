use std::{fs, path::PathBuf};

use lukas::compiler::{Backend, Compiler};

#[test]
fn native_crash_carries_surface_function_and_exact_call_site() {
    let dir = std::env::temp_dir().join("lukas_crash_site");
    fs::create_dir_all(&dir).unwrap();
    fs::write(
        dir.join("Root.lady"),
        r#"inner :: Int -> Int := λx.
  if x = 7
  then omg_wtf_bbq "the impossible seven"
  else x

start :: Int -> Unit := λ_.
  let result = inner 7
  in ()
"#,
    )
    .unwrap();

    let output = dir.join("crash.c");
    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: dir.clone(),
        backend: Backend::Native,
        output_file: Some(output.clone()),
    }
    .compiler_main()
    .expect("native code generation");

    let generated = fs::read_to_string(output).unwrap();
    assert!(generated.contains("Root_Prelude_raw_omg_wtf_bbq_worker"));
    assert!(generated.contains("Root.inner"), "{generated}");
    assert!(
        generated.contains(&dir.join("Root.lady").display().to_string()),
        "{generated}"
    );
    assert!(generated.contains("VInt(3), VInt(8)"), "{generated}");
}
