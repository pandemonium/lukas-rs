use std::{fs, path::PathBuf};

use lukas::{
    ast::{self, ROOT_MODULE_NAME, namer::QualifiedName},
    compiler::{Backend, Compiler},
    parser::IdentifierPath,
};

fn compiler_for(test_name: &str, source: &str) -> Compiler {
    let dir = std::env::temp_dir().join(format!("lukas_record_update_{test_name}"));
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("Root.lady"), source).unwrap();
    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: dir,
        backend: Backend::Native,
        output_file: None,
    }
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

fn first_closure_target(function: &str) -> &str {
    function
        .split("ClosureDesc __d = {")
        .nth(1)
        .and_then(|rest| rest.split(',').next())
        .expect("generated wrapper did not contain a closure target")
}

const SOURCE: &str = r#"
Pair ::= { x :: Int; y :: Int }

start :: Int -> Int := λn.
  let original = { x := n; y := n + 1 } in
  let changed =
    { original:
        y := original.x + 10
    }
  in original.y + changed.y
"#;

const DOTTED_SOURCE: &str = r#"
Point ::= { x :: Int; y :: Int }
Bounds ::= { lo :: Point; hi :: Point }

start :: Int -> Int := λn.
  let original =
    { lo := { x := n; y := n + 1 }
      hi := { x := n + 2; y := n + 3 }
    }
  in
  let changed =
    { original:
        lo.x := original.hi.y
        lo.y := original.lo.x
        hi.x := 90
    }
  in original.lo.x + changed.lo.x + changed.lo.y + changed.hi.x + changed.hi.y
"#;

#[test]
fn pure_record_update_copies_and_leaves_the_base_unchanged() {
    let env = compiler_for("interpreter", SOURCE)
        .compile_and_initialize()
        .expect("record update should compile");
    let value = env
        .call(
            &QualifiedName::new(IdentifierPath::new(ROOT_MODULE_NAME), "start"),
            ast::Literal::Int(5),
        )
        .expect("record update should evaluate");
    assert_eq!(format!("{value}"), "21");
}

#[test]
fn native_codegen_evaluates_the_base_once_and_emits_a_copy() {
    let mut compiler = compiler_for("native", SOURCE);
    let output = compiler.source_path.join("record_update.c");
    compiler.output_file = Some(output.clone());
    compiler.compiler_main().expect("native code generation");
    let generated = fs::read_to_string(output).expect("generated C source");
    assert!(generated.contains("_rub"), "{generated}");
}

#[test]
fn dotted_update_rebuilds_nested_records_and_preserves_the_base() {
    let env = compiler_for("dotted_interpreter", DOTTED_SOURCE)
        .compile_and_initialize()
        .expect("dotted record update should compile");
    let value = env
        .call(
            &QualifiedName::new(IdentifierPath::new(ROOT_MODULE_NAME), "start"),
            ast::Literal::Int(5),
        )
        .expect("dotted record update should evaluate");
    assert_eq!(format!("{value}"), "116");
}

#[test]
fn dotted_update_rejects_overlapping_paths() {
    let source = r#"
Point ::= { x :: Int; y :: Int }
Bounds ::= { lo :: Point; hi :: Point }

start :: Int -> Bounds := λn.
  let original =
    { lo := { x := n; y := n }
      hi := { x := n; y := n }
    }
  in
  { original:
      lo := { x := 1; y := 2 }
      lo.x := 3
  }
"#;
    assert!(
        compiler_for("dotted_overlap", source)
            .compile_and_initialize()
            .is_err()
    );
}

#[test]
fn mutable_array_deep_update_is_one_load_and_one_store_at_the_leaf_offset() {
    let output = std::env::temp_dir().join("lukas_mutable_deep_record_update.c");
    let compiler = Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: PathBuf::from("ladies/lang/15_mutable_record_updates"),
        backend: Backend::Native,
        output_file: Some(output.clone()),
    };
    compiler.compiler_main().expect("native code generation");
    let generated = fs::read_to_string(output).expect("generated C source");
    let fused = generated
        .match_indices("Value _pa")
        .filter_map(|(start, _)| {
            let rest = &generated[start..];
            let end = rest.find("VUnit();")? + "VUnit();".len();
            let expression = &rest[..end];
            expression
                .contains("prim_add(flat_array_get_word")
                .then_some(expression)
        })
        .collect::<Vec<_>>();

    assert!(!fused.is_empty(), "no fused same-place update found");
    for line in fused {
        assert_eq!(line.matches("flat_array_get_word").count(), 3, "{line}");
        assert_eq!(line.matches("flat_array_set_word").count(), 3, "{line}");
        assert!(
            line.rfind("flat_array_get_word").unwrap() < line.find("flat_array_set_word").unwrap(),
            "a store happened before all update values were evaluated: {line}"
        );
        for offset in [0, 1, 2] {
            assert!(
                line.contains(&format!(", {offset}, _pv")),
                "missing selective store at offset {offset}: {line}"
            );
        }
        assert!(
            !line.contains("mk_tuple"),
            "replacement record allocated: {line}"
        );
    }
}

#[test]
fn mutable_array_update_fusion_refuses_different_places_and_aggregate_leaves() {
    let source = r#"
use Stdlib.
use Stdlib.Data.Array.

Inner ::= { x :: Int; y :: Int }
Outer ::= { inner :: Inner; tail :: Int }

write_somewhere_else :: Mutable_Array Outer -> IO Unit := λa.
  let old = Mutable_Array.unsafe_get_unchecked a 0 in
  Mutable_Array.set_unchecked a 1 { old: tail := 9 }

replace_inner :: Outer -> Outer := λold.
  { old: inner := { x := old.inner.x + 1; y := 7 } }

replace_aggregate :: Mutable_Array Outer -> IO Unit := λa.
  Mutable_Array.modify_at a 0 replace_inner

start :: Int -> Unit := λ_.
  let values = unsafe_run_IO (Mutable_Array.generate 2 (λ_. { inner := { x := 1; y := 2 }; tail := 3 })) in
  let _ = unsafe_run_IO (write_somewhere_else values) in
  unsafe_run_IO (replace_aggregate values)
"#;
    let mut compiler = compiler_for("fusion_boundaries", source);
    let output = compiler.source_path.join("fusion_boundaries.c");
    compiler.output_file = Some(output.clone());
    compiler.compiler_main().expect("native code generation");
    let generated = fs::read_to_string(output).expect("generated C source");

    // Inspect only the two operations under test. The imported stdlib now contains
    // legitimate selective Vector length updates, so scanning the entire generated
    // translation unit for `_pa` mistakes unrelated successful fusions for this
    // fixture crossing one of its safety boundaries.
    let replace_wrapper = generated_function(&generated, "Root_replace_aggregate_worker");
    let write_wrapper = generated_function(&generated, "Root_write_somewhere_else_worker");
    let replace_effect = generated_function(&generated, first_closure_target(replace_wrapper));
    let write_effect = generated_function(&generated, first_closure_target(write_wrapper));

    for effect in [replace_effect, write_effect] {
        assert!(
            !effect.contains("Value _pa"),
            "an update outside the supported same-place scalar case was fused: {effect}"
        );
        assert_eq!(
            effect.matches("flat_array_set_word").count(),
            3,
            "the whole three-word Outer value must be stored: {effect}"
        );
    }
    assert!(
        replace_effect.contains("mk_tuple(3"),
        "an aggregate replacement must be rebuilt before its whole-value store: {replace_effect}"
    );
}

#[test]
fn generic_record_update_fuses_when_the_selected_offset_is_fixed() {
    let output = std::env::temp_dir().join("lukas_generic_fixed_offset_update.c");
    let compiler = Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: PathBuf::from("ladies/lang/13_flat_sum_arrays"),
        backend: Backend::Native,
        output_file: Some(output.clone()),
    };
    compiler.compiler_main().expect("native code generation");
    let generated = fs::read_to_string(output).expect("generated C source");

    // Vector_State a is still abstract here, but its alphabetically first Length
    // field has offset zero regardless of a. Both push branches must therefore
    // update the cell's packed state without rebuilding the two-field record.
    let updates = generated
        .match_indices("Value _pv")
        .filter_map(|(start, _)| {
            let rest = &generated[start..];
            let end = rest.find("VUnit();")? + "VUnit();".len();
            let expression = &rest[..end];
            expression
                .contains("prim_add(VInt(1), flat_array_get_word")
                .then_some(expression)
        })
        .collect::<Vec<_>>();
    assert!(
        updates.len() >= 2,
        "generic Vector length updates were not fused"
    );
    for update in updates {
        assert!(
            update.contains("flat_array_set_word") && update.contains(", 0,"),
            "Length was not written at its fixed leaf offset: {update}"
        );
        assert!(
            !update.contains("mk_tuple"),
            "Vector_State was rebuilt: {update}"
        );
    }

    let capacity_reads_from_place = generated.match_indices("raw_len_worker").any(|(at, _)| {
        let start = at.saturating_sub(300);
        generated[start..at].contains("flat_array_get_word")
    });
    assert!(
        capacity_reads_from_place,
        "Vector capacity did not load Storage directly from the cell place"
    );
}
