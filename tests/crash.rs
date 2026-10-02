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

#[test]
fn native_crash_keeps_site_when_bottom_is_overapplied_or_io_deforested() {
    let dir = std::env::temp_dir().join("lukas_crash_transformed_sites");
    fs::create_dir_all(&dir).unwrap();
    fs::write(
        dir.join("Root.lady"),
        r#"crash_io :: Int -> IO Unit := λvalue.
  omg_wtf_bbq "inlined io marker"

run :: ∀α. IO α -> α := λ(Suspend thunk).
  thunk ()

oversaturated :: Int -> Int -> Int := λx.
  omg_wtf_bbq "oversaturated marker"

start :: Int -> Unit := λ_.
  let _ = run (crash_io 1) in
  let _ = oversaturated 1 2 in
  ()
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
    let assertions = [
        ("inlined io marker", "Root.crash_io", "VInt(2), VInt(3)"),
        (
            "oversaturated marker",
            "Root.oversaturated",
            "VInt(8), VInt(3)",
        ),
    ];
    for (marker, function, location) in assertions {
        let lines = generated
            .lines()
            .filter(|line| line.contains(marker))
            .collect::<Vec<_>>();
        assert!(!lines.is_empty(), "missing {marker}: {generated}");
        for line in lines {
            assert!(line.contains(function), "{line}");
            assert!(line.contains(location), "{line}");
            assert!(!line.contains("sizeof(\"<unknown>\")"), "{line}");
        }
    }
}

#[test]
fn scheme_crash_carries_surface_function_and_exact_call_site() {
    let dir = std::env::temp_dir().join("lukas_scheme_crash_site");
    fs::create_dir_all(&dir).unwrap();
    fs::write(
        dir.join("Root.lady"),
        r#"start :: Int -> Unit := λ_.
  omg_wtf_bbq "scheme marker"
"#,
    )
    .unwrap();

    let output = dir.join("crash.ss");
    let compiler = Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: dir.clone(),
        backend: Backend::Scheme,
        output_file: Some(output.clone()),
    };

    // Scheme foreign implementations are spliced per declaring module. This test
    // only inspects the emitted call, so empty source-local companions are enough
    // and keep it independent of which Prelude modules currently contain foreigns.
    let checked = compiler.check().expect("type checking");
    for foreign in checked.foreign_terms {
        fs::write(dir.join(format!("{}.ss", foreign.name.module)), "").unwrap();
    }

    compiler.compiler_main().expect("Scheme code generation");

    let generated = fs::read_to_string(output).unwrap();
    assert!(
        generated.contains("Root-Prelude-raw_omg_wtf_bbq"),
        "{generated}"
    );
    assert!(generated.contains("\"Root.start\""), "{generated}");
    assert!(
        generated.contains(&format!("\"{}\"", dir.join("Root.lady").display())),
        "{generated}"
    );
    assert!(
        generated.contains(") 2) 3) \"scheme marker\""),
        "{generated}"
    );
}
