use std::{fs, path::PathBuf};

use lukas::compiler::{Backend, Compiler};

#[test]
fn semantic_spine_rebuild_reuses_fresh_custom_constructor_nodes() {
    let source = r#"
use Stdlib.

Spine ::= Stop | Link Int Spine Int

turn :: (Spine -> Int -> Int -> Spine) -> Spine -> Spine -> Spine := λrebuild seed input.
  deconstruct input into
    Link left rest right -> turn rebuild (rebuild seed left right) rest
  | Stop -> seed

grow :: Int -> Spine := λn.
  if n = 0 then Stop else Link n (grow (n - 1)) (n + 10)

normalize :: Spine -> Spine := λinput.
  turn (λtail left right. Link left tail right) Stop input

first :: Spine -> Int := λspine.
  deconstruct spine into Link value _ _ -> value | Stop -> 0

shared :: Int -> Int := λn.
  let spine = grow n in first (normalize spine) + first spine

Fork ::= Done | Ahead Fork | Behind Fork

turn_both :: (Fork -> Fork) -> Fork -> Fork -> Fork := λrebuild seed input.
  deconstruct input into
    Ahead rest -> turn_both rebuild (rebuild seed) rest
  | Behind rest -> turn_both rebuild (rebuild seed) rest
  | Done -> seed

grow_ahead :: Int -> Fork := λn.
  if n = 0 then Done else Ahead (grow_ahead (n - 1))

ambiguous :: Fork -> Fork := λinput.
  turn_both (λtail. Behind tail) Done input

ambiguous_probe :: Int -> Fork := λn. ambiguous (grow_ahead n)

start := λ_. first (normalize (grow 4))
"#;
    let dir =
        std::env::temp_dir().join(format!("lukas_owned_spine_codegen_{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("Root.lady"), source).unwrap();
    let output = dir.join("program.c");
    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: dir.clone(),
        backend: Backend::Native,
        profile: lukas::compiler::ExecutionProfile::Host,
        capability_config: None,
        provider_plan: None,
        requirements_report: None,
        output_file: Some(output.clone()),
    }
    .compiler_main()
    .expect("native code generation");

    let generated = fs::read_to_string(&output).expect("generated C source");
    let normalize = generated_function(&generated, "Root_normalize_worker");
    assert!(
        !normalize.contains("reverse_constructor_spine_owned"),
        "an ordinary call with a potentially shared argument consumed its spine: {normalize}"
    );

    let start = generated_function(&generated, "Root_start_worker");
    assert!(
        start.contains("reverse_constructor_spine_owned") && start.contains(", 1);"),
        "a fresh custom spine was not rebuilt through its middle recursive field: {start}"
    );

    let shared = generated_function(&generated, "Root_shared_worker");
    assert!(
        !shared.contains("reverse_constructor_spine_owned"),
        "a spine with a live alias was consumed: {shared}"
    );

    let ambiguous = generated_function(&generated, "Root_ambiguous_probe_worker");
    assert!(
        !ambiguous.contains("reverse_constructor_spine_owned"),
        "a recursion with two possible step constructors was treated as a single spine rebuild: {ambiguous}"
    );

    fs::remove_dir_all(dir).unwrap();
}

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
