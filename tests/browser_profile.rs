use std::{fs, path::PathBuf};

use lukas::compiler::{Backend, Compiler, ExecutionProfile};

fn browser_compiler(source_path: PathBuf, output: PathBuf) -> Compiler {
    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path,
        backend: Backend::Native,
        profile: ExecutionProfile::WasmBrowser,
        capability_config: None,
        provider_plan: None,
        requirements_report: None,
        output_file: Some(output),
    }
}

#[test]
fn browser_profile_emits_an_idempotent_export_without_process_main() {
    let dir = std::env::temp_dir().join("lukas_browser_profile");
    fs::create_dir_all(&dir).unwrap();
    fs::write(
        dir.join("Root.lady"),
        r#"start :: Int -> Unit := λ_.
  print_endline "hello from wasm"
"#,
    )
    .unwrap();

    let output = dir.join("browser.c");
    browser_compiler(dir, output.clone())
        .compiler_main()
        .expect("browser C generation");

    let generated = fs::read_to_string(output).expect("generated browser C");
    assert!(generated.contains("void marmelade_start(void) {"));
    assert!(generated.contains("if (marmelade_started) return;"));
    assert!(generated.contains("gc_init(&gc_anchor);"));
    assert!(generated.contains("runtime_init();"));
    assert!(generated.contains("startup();"));
    assert!(generated.contains("gc_collect();"));
    assert!(!generated.contains("int main(void) {"));
}

#[test]
fn browser_profile_rejects_reachable_threads() {
    let output = std::env::temp_dir().join("lukas_browser_threads.c");
    let _ = fs::remove_file(&output);
    let error = browser_compiler(PathBuf::from("ladies/examples/37_threads"), output.clone())
        .compiler_main()
        .expect_err("browser builds cannot provide native threads");
    let diagnostic = error.to_string();

    assert!(diagnostic.contains("requirements cannot be satisfied for Wasm_Browser"));
    assert!(diagnostic.contains("`Threads` has no provider"));
    assert!(diagnostic.contains("Root.start -> Root.main"));
    assert!(!output.exists(), "a rejected build emitted C");
}

#[test]
fn browser_profile_rejects_reachable_mmap_and_file_system() {
    let output = std::env::temp_dir().join("lukas_browser_mmap.c");
    let _ = fs::remove_file(&output);
    let error = browser_compiler(PathBuf::from("ladies/c_examples/05_mmap"), output.clone())
        .compiler_main()
        .expect_err("browser builds cannot provide native mmap or file access");
    let diagnostic = error.to_string();

    assert!(diagnostic.contains("`MMap` has no provider"));
    assert!(diagnostic.contains("`File_System` has no provider"));
    assert!(diagnostic.contains("Root.start -> Root.program"));
    assert!(!output.exists(), "a rejected build emitted C");
}

#[test]
fn an_unreachable_foreign_requirement_does_not_reject_the_entry_point() {
    let dir = std::env::temp_dir().join("lukas_browser_unreachable_requirement");
    fs::create_dir_all(&dir).unwrap();
    fs::write(
        dir.join("Root.lady"),
        r#"foreign [ Threads ] unused :: Unit -> Unit

start :: Int -> Unit := λ_. ()
"#,
    )
    .unwrap();

    let output = dir.join("browser.c");
    browser_compiler(dir, output.clone())
        .compiler_main()
        .expect("only requirements reachable from start constrain an application build");
    assert!(output.exists());
}
