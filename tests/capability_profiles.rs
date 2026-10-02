use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicUsize, Ordering},
};

use lukas::compiler::{Backend, Compiler, ExecutionProfile};

static NEXT_DIRECTORY: AtomicUsize = AtomicUsize::new(0);

fn source_directory(name: &str, source: &str) -> PathBuf {
    let serial = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
    let directory = std::env::temp_dir().join(format!(
        "lukas_capability_{name}_{}_{serial}",
        std::process::id()
    ));
    fs::create_dir_all(&directory).unwrap();
    fs::write(directory.join("Root.lady"), source).unwrap();
    directory
}

fn compile(
    directory: &Path,
    profile: ExecutionProfile,
) -> Result<(String, String), lukas::compiler::CompilationError> {
    let profile_name = format!("{profile:?}");
    let output = directory.join(format!("{profile_name}.c"));
    let plan = directory.join(format!("{profile_name}.providers"));
    let report = directory.join(format!("{profile_name}.requirements"));
    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: directory.to_owned(),
        backend: Backend::Native,
        profile,
        capability_config: None,
        provider_plan: Some(plan.clone()),
        requirements_report: Some(report.clone()),
        output_file: Some(output),
    }
    .compiler_main()?;

    Ok((
        fs::read_to_string(plan).unwrap(),
        fs::read_to_string(report).unwrap(),
    ))
}

#[test]
fn web_socket_resolves_through_the_provider_graph_for_every_platform() {
    let directory = source_directory(
        "web_socket",
        r#"foreign [ Web_Socket ] raw_open :: Unit -> Unit

open :: Unit -> Unit := λunit. raw_open unit
start :: Int -> Unit := λ_. open ()
"#,
    );

    let cases: [(ExecutionProfile, &[&str]); 5] = [
        (
            ExecutionProfile::NativeMacOS,
            &["Socket_Web_Socket", "MacOS_Socket", "MacOS_Timer"],
        ),
        (
            ExecutionProfile::NativeLinux,
            &["Socket_Web_Socket", "Linux_Socket", "Linux_Timer"],
        ),
        (
            ExecutionProfile::NativeWindows,
            &["Socket_Web_Socket", "Windows_Socket", "Windows_Timer"],
        ),
        (
            ExecutionProfile::WasmNode,
            &["Socket_Web_Socket", "Node_Socket", "Node_Timer"],
        ),
        (
            ExecutionProfile::WasmBrowser,
            &["Browser_Web_Socket", "Browser_Runtime"],
        ),
    ];

    for (profile, providers) in cases {
        let (plan, report) = compile(&directory, profile).unwrap();
        for provider in providers {
            assert!(
                plan.contains(&format!("provider {provider}")),
                "{profile:?} plan did not select {provider}:\n{plan}"
            );
        }
        assert!(plan.contains("define MARM_PROVIDER_WEB_SOCKET_"));
        assert!(report.contains("Root.raw_open: Web_Socket"));
        assert!(report.contains("Root.open: Web_Socket"));
        assert!(report.contains("Root.start: Web_Socket"));
    }
}

#[test]
fn browser_only_requirement_fails_during_other_target_builds() {
    let directory = source_directory(
        "dom",
        r#"foreign [ Dom ] raw_title :: Unit -> Text

start :: Int -> Unit := λ_. print_endline (raw_title ())
"#,
    );

    let (browser_plan, _) = compile(&directory, ExecutionProfile::WasmBrowser).unwrap();
    assert!(browser_plan.contains("provider Browser_DOM"));
    assert!(browser_plan.contains("define MARM_PROVIDER_DOM_BROWSER"));

    for profile in [
        ExecutionProfile::NativeMacOS,
        ExecutionProfile::NativeLinux,
        ExecutionProfile::NativeWindows,
        ExecutionProfile::WasmNode,
    ] {
        let error = compile(&directory, profile).unwrap_err().to_string();
        assert!(
            error.contains("`Dom` has no provider"),
            "{profile:?}: {error}"
        );
        assert!(error.contains("Root.start -> Root.raw_title"));
    }
}

#[test]
fn windows_rejects_threads_but_accepts_file_system() {
    let threaded = source_directory(
        "windows_threads",
        r#"foreign [ Threads ] raw_spawn :: Unit -> Unit
start :: Int -> Unit := λ_. raw_spawn ()
"#,
    );
    let error = compile(&threaded, ExecutionProfile::NativeWindows)
        .unwrap_err()
        .to_string();
    assert!(error.contains("`Threads` has no provider reaching `Native_Windows`"));

    let files = source_directory(
        "windows_files",
        r#"foreign [ File_System ] raw_sync :: Unit -> Unit
start :: Int -> Unit := λ_. raw_sync ()
"#,
    );
    let (plan, _) = compile(&files, ExecutionProfile::NativeWindows).unwrap();
    assert!(plan.contains("provider Windows_File_System"));
    assert!(plan.contains("define MARM_PROVIDER_FILE_SYSTEM_WINDOWS"));
}

#[test]
fn scheme_codegen_does_not_load_the_capability_model() {
    let directory = source_directory(
        "scheme_ignores_capabilities",
        "start :: Int -> Unit := λ_. ()\n",
    );
    let library = directory.join("library");
    fs::create_dir_all(&library).unwrap();
    fs::write(library.join("Prelude.lady"), "").unwrap();
    let output = directory.join("root.ss");
    Compiler {
        library_path: library,
        source_path: directory.clone(),
        backend: Backend::Scheme,
        profile: ExecutionProfile::Host,
        capability_config: Some(directory.join("does-not-exist.conf")),
        provider_plan: Some(directory.join("must-not-exist.providers")),
        requirements_report: Some(directory.join("must-not-exist.requirements")),
        output_file: Some(output.clone()),
    }
    .compiler_main()
    .expect("Scheme code generation is outside the capability model");

    assert!(output.exists());
    assert!(!directory.join("must-not-exist.providers").exists());
    assert!(!directory.join("must-not-exist.requirements").exists());
}
