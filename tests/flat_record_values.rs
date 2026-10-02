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
        profile: lukas::compiler::ExecutionProfile::Host,
        capability_config: None,
        provider_plan: None,
        requirements_report: None,
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
        profile: lukas::compiler::ExecutionProfile::Host,
        capability_config: None,
        provider_plan: None,
        requirements_report: None,
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

#[test]
fn captured_projection_stops_at_a_boxed_one_field_record() {
    let dir = std::env::temp_dir().join("lukas_flat_one_field_record_boundary");
    fs::create_dir_all(&dir).unwrap();
    fs::write(
        dir.join("Root.lady"),
        r#"Inner ::= { Value :: Int }
Outer ::= { Extra :: Int; Inner :: Inner }

read_later :: Outer -> (Unit -> Int) := λouter.
  λ_. outer.Inner.Value

start := λn.
  let outer = { Extra := n; Inner := { Value := n + 1 } } in
  read_later outer ()
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
    .expect("native code generation");

    let generated = fs::read_to_string(output).expect("generated C source");
    let reader = generated
        .split("\n\n")
        .find(|function| {
            function.starts_with("Value Root_lambda_")
                && function.contains("proj(env_get(self, 1), 0)")
        })
        .expect("the boxed Inner projection was not found");
    assert_eq!(reader.matches("proj(").count(), 1, "{reader}");

    let creator = generated
        .split("\n\n")
        .find(|function| {
            function.starts_with("Value Root_lambda_")
                && function.contains("mk_closure_d2")
                && function.contains("Value _fr")
        })
        .expect("the closure capturing Outer was not found");
    assert_eq!(creator.matches("proj(").count(), 2, "{creator}");
    assert!(!creator.contains("proj(proj("), "{creator}");
}

#[test]
fn polymorphic_record_field_keeps_one_word_at_ground_sum_instantiation() {
    let dir = std::env::temp_dir().join("lukas_polymorphic_record_sum_field");
    fs::create_dir_all(&dir).unwrap();
    fs::write(
        dir.join("Root.lady"),
        r#"Command ::= Travel Int | Stay

Item ::= ∀α.
  { Command :: α
    Label   :: Int
  }

build_item :: Int -> Item Command := λdestination.
  { Command := Travel destination; Label := 7 }

command :: ∀α. Item α -> α := λitem.
  item.Command

start :: Int -> Int := λdestination.
  deconstruct command (build_item destination) into
    Travel destination -> destination
  | Stay               -> 0
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
    .expect("native code generation");

    let generated = fs::read_to_string(output).expect("generated C source");
    let item_builder = generated
        .split("\n\n")
        .find(|function| function.starts_with("Value Root_build_item_worker"))
        .expect("the concrete Item builder was not emitted");
    assert!(item_builder.contains("mk_tuple2("), "{item_builder}");
    assert!(
        !item_builder.contains("data_tag") && !item_builder.contains("mk_tuple(3,"),
        "the concrete sum was inlined into Item's polymorphic field: {item_builder}"
    );

    let command_reader = generated
        .split("\n\n")
        .find(|function| {
            function.starts_with("Value Root_command_worker") && function.contains("proj(l0, 0)")
        })
        .expect("the generic Item.Command projection was not emitted");
    assert!(
        !command_reader.contains("mk_data_inline"),
        "{command_reader}"
    );
}

#[test]
fn an_abi_mismatched_record_nested_in_a_shaped_sum_stays_boxed() {
    let dir = std::env::temp_dir().join("lukas_nested_record_array_abi");
    fs::create_dir_all(&dir).unwrap();
    fs::write(
        dir.join("Root.lady"),
        r#"use Stdlib.
use Stdlib.Data.
use Stdlib.Data.Array.

Pair ::= { X :: Int; Y :: Int }
Complex ::= { Maybe :: Perhaps Int; Pair :: Pair; Title :: Text }

values :: Array (Perhaps Complex) :=
  [ Nope
    This { Maybe := Nope; Pair := { X := 4; Y := 5 }; Title := "deep" }
  ]

start :: Int -> Unit := λ_.
  deconstruct Array.get values 1 into
    This (This value) -> print_endline value.Title
  | otherwise -> print_endline "empty"
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
    .expect("native code generation");

    let generated = fs::read_to_string(output).expect("generated C source");
    assert!(
        generated.contains("(int64_t[]){-2, 0, 1, 0, 1, 0}, 6)"),
        "the nested Complex record was not retained as the boxed payload of Perhaps"
    );
}
