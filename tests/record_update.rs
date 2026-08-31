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
fn mutable_array_update_fusion_refuses_different_places_and_scalarizes_aggregate_leaves() {
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

    assert!(
        !write_effect.contains("Value _pa"),
        "a write to a different index was fused: {write_effect}"
    );
    assert_eq!(
        write_effect.matches("flat_array_set_word").count(),
        3,
        "the whole three-word Outer value must be stored at the other index: {write_effect}"
    );

    assert!(
        replace_effect.contains("Value _pa"),
        "the same-place aggregate replacement was not fused: {replace_effect}"
    );
    assert_eq!(
        replace_effect.matches("flat_array_get_word").count(),
        1,
        "only old.inner.x should be read: {replace_effect}"
    );
    assert_eq!(
        replace_effect.matches("flat_array_set_word").count(),
        2,
        "only the two leaves of inner should be written: {replace_effect}"
    );
    for offset in [0, 1] {
        assert!(
            replace_effect.contains(&format!(", {offset}, _pv")),
            "missing aggregate leaf store at offset {offset}: {replace_effect}"
        );
    }
    assert!(
        !replace_effect.contains("mk_tuple"),
        "the aggregate replacement allocated a temporary tuple: {replace_effect}"
    );
}

#[test]
fn branch_local_update_keeps_a_niche_key_and_nested_record_in_the_array_place() {
    let source = r#"
use Stdlib.
use Stdlib.Data.Array.

Stats ::= { Count :: Int; Max :: Int; Min :: Int; Sum :: Int }
Entry ::= ∀α. { Entry_Key :: Perhaps α; Entry_Value :: Stats }
Store ::= ∀α. { Buckets :: Mutable_Array (Entry α) }

combine :: Stats -> Stats -> Stats := λold added.
  { Count := old.Count + added.Count
    Max := old.Max + added.Max
    Min := old.Min + added.Min
    Sum := old.Sum + added.Sum
  }

update :: ∀α. Eq α |- α -> Stats -> Store α -> Int -> IO Unit :=
  λkey added store initial_index.
    let length = Mutable_Array.length store.Buckets in
    let loop = λindex.
      let* old = Mutable_Array.get_unchecked store.Buckets index in
      deconstruct old.Entry_Key into
        This existing ->
          if existing = key then
            let changed = { old: Entry_Value := combine old.Entry_Value added } in
            Mutable_Array.set_unchecked store.Buckets index changed
          else
            loop ((index + 1) % length)
      | Nope ->
          Mutable_Array.set_unchecked store.Buckets index
            { Entry_Key := This key; Entry_Value := added }
    in loop initial_index

rename_entry :: Entry Text -> Entry Text := λold.
  { old: Entry_Key := This "beta" }

rename :: Mutable_Array (Entry Text) -> IO Unit := λbuckets.
  Mutable_Array.modify_at buckets 0 rename_entry

start :: Int -> Unit := λ_.
  let zero = { Count := 0; Max := 0; Min := 0; Sum := 0 } in
  let one = { Count := 1; Max := 2; Min := 3; Sum := 4 } in
  let buckets = unsafe_run_IO (Mutable_Array.generate 4 (λ_. { Entry_Key := Nope; Entry_Value := zero })) in
  let store = { Buckets := buckets } in
  let _ = unsafe_run_IO (update "alpha" one store 0) in
  unsafe_run_IO (update "alpha" one store 0)
"#;
    let mut compiler = compiler_for("branch_local_niche_update", source);
    let output = compiler.source_path.join("branch_local_niche_update.c");
    compiler.output_file = Some(output.clone());
    compiler.compiler_main().expect("native code generation");
    let generated = fs::read_to_string(output).expect("generated C source");

    assert!(
        generated.contains("{6, 5, 0, 0, 0, 0, 0}"),
        "Entry Text was not represented as one niche key plus four inline Stats words"
    );

    let hot_function = generated
        .split("\nValue ")
        .find(|function| {
            function.contains("Value _pv")
                && function.contains(", 1, _pv")
                && function.contains(", 2, _pv")
                && function.contains(", 3, _pv")
                && function.contains(", 4, _pv")
        })
        .expect("no four-leaf same-place update was generated");
    let update_start = hot_function.find("Value _pa").unwrap();
    let update_end = hot_function[update_start..]
        .find("VUnit();")
        .map(|end| update_start + end + "VUnit();".len())
        .unwrap();
    let occupied_update = &hot_function[update_start..update_end];

    assert!(
        hot_function.contains(".w != 0"),
        "the Perhaps key was not tested through its zero niche: {hot_function}"
    );
    assert!(
        !hot_function.contains("raw_get_unchecked_worker"),
        "the complete Entry was reconstructed by an array read: {hot_function}"
    );
    assert_eq!(
        occupied_update.matches("flat_array_get_word").count(),
        4,
        "the occupied update should read exactly the four Stats leaves: {occupied_update}"
    );
    assert_eq!(
        occupied_update.matches("flat_array_set_word").count(),
        4,
        "the occupied update should write exactly the four Stats leaves: {occupied_update}"
    );
    assert_eq!(
        occupied_update
            .matches("flat_array_set_word_immediate")
            .count(),
        4,
        "immediate Stats leaves should not enter the GC remembered set: {occupied_update}"
    );
    assert!(
        !occupied_update.contains(", 0, _pv") && !occupied_update.contains("mk_tuple"),
        "the occupied update rewrote the key or rebuilt an aggregate: {occupied_update}"
    );

    let rename_wrapper = generated_function(&generated, "Root_rename_worker");
    let rename_effect = generated_function(&generated, first_closure_target(rename_wrapper));
    assert!(
        rename_effect.contains("flat_array_set_word(") && rename_effect.contains(", 0, _pv"),
        "the pointer-bearing Perhaps Text field must retain its write barrier: {rename_effect}"
    );
    assert!(
        !rename_effect.contains("flat_array_set_word_immediate"),
        "the pointer-bearing Perhaps Text field used the immediate-only setter: {rename_effect}"
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
