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

#[test]
fn nested_projection_stops_at_a_boxed_oversized_record() {
    let dir = std::env::temp_dir().join("lukas_flat_record_projection_boundary");
    fs::create_dir_all(&dir).unwrap();
    fs::write(
        dir.join("Root.lady"),
        r#"Large ::=
  { A :: Int; B :: Int; C :: Int; D :: Int; E :: Int
    F :: Int; G :: Int; H :: Int; I :: Int
  }

Middle ::= { Marker :: Int; Payload :: Large }
Outer ::= { Marker :: Int; Middle :: Middle }

get :: Outer -> Int := λouter. outer.Middle.Payload.I

start := λ_.
  let large =
    { A := 1; B := 2; C := 3; D := 4; E := 5
      F := 6; G := 7; H := 8; I := 9
    }
  in
  let middle = { Marker := 1; Payload := large } in
  get { Marker := 0; Middle := middle }
"#,
    )
    .unwrap();

    let output = dir.join("program.c");
    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: dir,
        backend: Backend::Native,
        output_file: Some(output.clone()),
    }
    .compiler_main()
    .expect("native code generation");

    let generated = fs::read_to_string(output).expect("generated C source");
    assert!(
        generated.contains("proj(proj(l0, 2), 8)"),
        "projection did not dereference the boxed Large field: {generated}"
    );
}
