use std::{fs, path::PathBuf};

use lukas::compiler::{Backend, Compiler};

#[test]
fn captured_ground_records_stay_split_until_used_as_whole_values() {
    let dir = std::env::temp_dir().join("lukas_flat_record_values");
    fs::create_dir_all(&dir).unwrap();
    fs::write(
        dir.join("Root.lady"),
        r#"Pair ::= { X :: Int; Y :: Int }

project :: Pair -> Int -> Int := λpair offset.
  pair.Y + offset

retain :: Pair -> Int -> Pair := λpair _.
  pair

start :: Int -> Int := λn.
  let pair = { X := n; Y := n + 1 } in
  (project pair 10) + (retain pair 0).X
"#,
    )
    .unwrap();

    let output = dir.join("flat_record_values.c");
    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: dir,
        backend: Backend::Native,
        output_file: Some(output.clone()),
    }
    .compiler_main()
    .expect("native code generation");

    let generated = fs::read_to_string(output).expect("generated C source");
    let projector = generated
        .split("\n\n")
        .find(|function| {
            function.starts_with("Value Root_lambda_")
                && function.contains("prim_add(env_get(self, 1), l0)")
        })
        .expect("the captured Pair projection was not found");
    assert!(!projector.contains("mk_tuple"), "{projector}");
    assert!(!projector.contains("proj("), "{projector}");

    let retainer = generated
        .split("\n\n")
        .find(|function| {
            function.starts_with("Value Root_lambda_")
                && function.contains("mk_tuple2(env_get(self, 0), env_get(self, 1))")
        })
        .expect("the whole captured Pair was not reconstructed");
    assert_eq!(retainer.matches("mk_tuple2").count(), 1, "{retainer}");

    assert!(
        generated.contains("mk_closure_d2(&__d"),
        "the two Pair words were not stored directly in a heap closure"
    );
}
