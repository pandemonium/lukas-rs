use std::{fs, path::PathBuf};

use lukas::compiler::{Backend, Compiler};

#[test]
fn perhaps_uses_zero_niche_and_nested_perhaps_falls_back_to_a_tag() {
    let output = std::env::temp_dir().join("lukas_niche_layout.c");
    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: PathBuf::from("ladies/lang/13_flat_sum_arrays"),
        backend: Backend::Native,
        profile: lukas::compiler::ExecutionProfile::Host,
        capability_config: None,
        provider_plan: None,
        requirements_report: None,
        output_file: Some(output.clone()),
    }
    .compiler_main()
    .expect("native code generation");

    let generated = fs::read_to_string(output).expect("generated C source");

    // Perhaps Int: [-2, Nope-tag, This-tag, niche-offset, payload-leaf].
    assert!(
        generated.contains("(int64_t[]){-2, 0, 1, 0, 1, 0}, 6"),
        "Perhaps Int did not use its one-word zero niche"
    );
    // Perhaps Pair has the same niche encoding but retains Pair's two flat words.
    assert!(
        generated.contains("(int64_t[]){-2, 0, 1, 0, 1, 2, 0, 0}, 8"),
        "Perhaps Pair did not remain payload-width"
    );
    // The inner Perhaps has consumed zero, so the outer Perhaps must retain a tag.
    assert!(
        generated.contains("(int64_t[]){-1, 1, 2, 0, 1, -2, 0, 1, 0, 1, 0}, 11"),
        "nested Perhaps did not preserve Nope versus This Nope"
    );
    // Complex has a fixed five-word canonical record ABI but a four-word ground
    // packed layout. Nested inside Perhaps it cannot use the top-level record ABI
    // adapter, so it remains one boxed leaf. The outer Perhaps can use the nonzero
    // record pointer as its niche without confusing `This { Maybe := Nope, .. }`
    // with its own `Nope`.
    let complex_initializer = generated
        .lines()
        .find(|line| line.contains("Root_complex_values ="))
        .expect("the Complex array initializer");
    assert!(
        complex_initializer.contains("(int64_t[]){-2, 0, 1, 0, 1, 0}, 6"),
        "the nested ABI-mismatched record was not kept boxed: {complex_initializer}"
    );
    // Occupied has three constructor arguments. Its first is itself niche-encoded,
    // so zero is valid there; selection must continue and use the Text at offset 1.
    assert!(
        generated.contains("(int64_t[]){-2, 0, 1, 1, 3, -2, 0, 1, 0, 1, 0, 0, 2, 0, 0}, 15"),
        "niche search stopped before the later eligible payload field"
    );
}

#[test]
fn record_mediated_recursive_sum_does_not_overflow_layout_analysis() {
    let dir =
        std::env::temp_dir().join(format!("lukas_recursive_sum_layout_{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    fs::write(
        dir.join("Root.lady"),
        r#"State ::= Idle | In_Transit Transition

Transition ::=
  { From  :: State
    To    :: State
    Turns :: Int
  }

Player ::= { State :: State; Score :: Int }

step :: Player -> Int := λplayer.
  deconstruct player.State into
    Idle                    -> player.Score
  | In_Transit transition   -> transition.Turns

start := λ_. step { State := Idle; Score := 1 }
"#,
    )
    .unwrap();

    let output = dir.join("program.c");
    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: dir,
        backend: Backend::Native,
        profile: lukas::compiler::ExecutionProfile::Host,
        capability_config: None,
        provider_plan: None,
        requirements_report: None,
        output_file: Some(output.clone()),
    }
    .compiler_main()
    .expect("recursive native layout code generation");

    let generated = fs::read_to_string(output).expect("generated C source");
    assert!(
        generated.contains("Root_step_worker"),
        "the projected recursive match was not emitted"
    );
}
