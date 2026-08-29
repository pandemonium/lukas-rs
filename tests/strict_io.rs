use std::{fs, path::PathBuf};

use lukas::compiler::{Backend, Compiler};

#[test]
fn strict_io_opens_user_defined_composition_by_structure() {
    let dir = std::env::temp_dir().join("lukas_strict_io_structural");
    fs::create_dir_all(&dir).unwrap();
    fs::write(
        dir.join("Root.lady"),
        r#"delay :: ∀α. α -> IO α := λvalue.
  Suspend (λ_. value)

chain :: ∀α β. (α -> IO β) -> IO α -> IO β := λnext (Suspend thunk).
  Suspend (λ_.
    let Suspend tail = next (thunk ())
    in tail ()
  )

force :: ∀α. IO α -> α := λ(Suspend thunk).
  thunk ()

drive :: Int -> IO Int := λlimit.
  let loop = λi.
    if i < limit
    then chain loop (delay (i + 1))
    else delay i
  in loop 0

start :: Int -> Int := λlimit.
  force (drive limit)
"#,
    )
    .unwrap();

    let output = dir.join("strict_io.c");
    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: dir,
        backend: Backend::Native,
        output_file: Some(output.clone()),
    }
    .compiler_main()
    .expect("native code generation");

    let generated = fs::read_to_string(output).expect("generated C source");
    let strict_loop = generated
        .split("\n\n")
        .find(|function| {
            function.starts_with("Value Root_lambda_") && function.contains("for (;;)")
        })
        .expect("the local IO recursion was not lowered to a native loop");

    assert!(strict_loop.contains("prim_add"), "{strict_loop}");
    assert!(!strict_loop.contains("Root_chain"), "{strict_loop}");
    assert!(!strict_loop.contains("Root_delay"), "{strict_loop}");
    assert!(
        !strict_loop.contains("Root_Prelude_Suspend"),
        "{strict_loop}"
    );
}
