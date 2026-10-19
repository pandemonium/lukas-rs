use std::{fs, path::PathBuf};

use lukas::compiler::{Backend, Compiler};

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
fn known_constructor_fields_are_scalar_replaced_for_arbitrary_arity() {
    let source = r#"
use Stdlib.

Inner ::= Empty | Leaf Int
Outer ::= Other | Wrap5 Inner Int Int Int Int

match_nested :: Int -> Int := λn.
  deconstruct Wrap5 (Leaf n) 2 3 4 5 into
    Wrap5 (Leaf value) _ _ _ _ -> value
  | Wrap5 (Empty) _ _ _ _ -> 0
  | Other -> 0

fallback :: Int -> Outer := λn.
  deconstruct Wrap5 (if n = 0 then Empty else Leaf n) 2 3 4 5 into
    Wrap5 (Empty) _ _ _ _ -> Other
  | whole -> whole

dead_fallback :: Int -> Int := λn.
  deconstruct Wrap5 (if n = 0 then Empty else Leaf n) 2 3 4 5 into
    Wrap5 (Leaf value) _ _ _ _ -> value
  | _ -> 0

make_outer :: Int -> Outer := λn. Wrap5 (Leaf n) 2 3 4 5

start := λ_. match_nested 7
"#;
    let dir = std::env::temp_dir().join(format!(
        "lukas_constructor_match_codegen_{}",
        std::process::id()
    ));
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

    let matched = generated_function(&generated, "Root_match_nested_worker");
    assert!(
        matched.contains("_tcscrut") || matched.contains("_cscrut"),
        "{matched}"
    );
    assert!(
        !matched.contains("mk_data("),
        "the immediately matched arity-five constructor was allocated: {matched}"
    );

    let fallback = generated_function(&generated, "Root_fallback_worker");
    assert!(
        fallback.contains("_tcscrut") || fallback.contains("_cscrut"),
        "{fallback}"
    );
    assert!(
        fallback.contains("mk_data("),
        "a whole-value fallback did not reconstruct its constructor: {fallback}"
    );

    let dead_fallback = generated_function(&generated, "Root_dead_fallback_worker");
    assert!(
        !dead_fallback.contains("mk_data("),
        "an unused whole-constructor fallback was still materialized: {dead_fallback}"
    );

    let escaping = generated_function(&generated, "Root_make_outer_worker");
    assert!(
        escaping.contains("Root_Wrap5_worker("),
        "an escaping constructor was incorrectly scalar replaced: {escaping}"
    );

    fs::remove_dir_all(dir).unwrap();
}
