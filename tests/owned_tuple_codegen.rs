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
fn owned_tuple_flows_through_generic_recursive_and_higher_order_calls() {
    let source = r#"
use Stdlib.

Chain ::= End | Node Int Chain

walk :: (Int -> (Int, List Int) -> (Int, List Int)) -> (Int, List Int) -> Chain -> (Int, List Int) := λstep seed input.
  deconstruct input into
    Node value rest -> step value (walk step seed rest)
  | End -> seed

grow :: Int -> Chain := λn.
  if n = 0 then End else Node n (grow (n - 1))

sum :: Chain -> Int := λinput.
  let total, _ =
    walk
      (λvalue (running, output). running + value, Cons value output)
      (0, Nil)
      input
  in total

shared :: (Int, List Int) -> Chain -> Int := λseed input.
  let total, _ = walk (λvalue (running, output). running + value, Cons value output) seed input
  in total

start := λ_. sum (grow 4)
"#;
    let dir =
        std::env::temp_dir().join(format!("lukas_owned_tuple_codegen_{}", std::process::id()));
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
    let owned_walk = generated_function(&generated, "Root_walk_owned_tuple_1_worker");
    assert!(
        owned_walk.contains("Root_walk_owned_tuple_1_worker(l0, l1"),
        "the recursive call did not preserve tuple ownership: {owned_walk}"
    );
    assert!(
        owned_walk.contains("apply_n_owned_last(l0, 2"),
        "the higher-order call did not consume its owned last argument: {owned_walk}"
    );

    let owned_steps = generated
        .match_indices("_owned_tuple_uworker(Value self, Value *args) {")
        .filter_map(|(marker, _)| {
            let start = generated[..marker].rfind("Value ")?;
            let end = generated[start..].find("\n}\n")? + start + "\n}\n".len();
            Some(&generated[start..end])
        })
        .find(|function| function.contains("reuse_owned_tuple2_fast(l1"))
        .expect("tuple-producing step has no owned worker");
    assert!(owned_steps.contains("reuse_owned_tuple2_fast(l1"));

    let sum = generated_function(&generated, "Root_sum_worker");
    assert!(sum.contains("Root_walk_owned_tuple_1_worker("));
    assert!(
        sum.contains("OBJ_TUPLE, MARM_ETERNAL") && sum.contains("VBorrowedTuple("),
        "the fresh tuple seed was not represented in the consuming match's stack frame: {sum}"
    );
    assert!(
        !sum.contains("mk_tuple2(VInt(0)"),
        "the virtual tuple seed was still allocated: {sum}"
    );
    let shared = generated_function(&generated, "Root_shared_worker");
    assert!(
        shared.contains("Root_walk_worker("),
        "a caller-owned seed was consumed without uniqueness: {shared}"
    );
    assert!(!shared.contains("Root_walk_owned_tuple_1_worker("));

    fs::remove_dir_all(dir).unwrap();
}
