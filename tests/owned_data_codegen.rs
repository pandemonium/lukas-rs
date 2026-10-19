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
fn structural_eliminator_reuses_exclusive_custom_product_and_data_nodes() {
    let source = r#"
use Stdlib.

Spine ::= Stop | Link Int Spine Int

grow :: Int -> Spine := λn.
  if n = 0 then Stop else Link n (grow (n - 1)) (n + 10)

bump :: Spine -> Spine := λinput.
  deconstruct input into
    Stop -> Stop
  | Link left rest right -> Link (left + 1) (bump rest) (right + 1)

branch_bump :: Spine -> Bool -> Spine := λinput high.
  deconstruct input into
    Stop -> Stop
  | Link left rest right ->
      if high
      then Link (left + 1) (branch_bump rest high) right
      else Link left (branch_bump rest high) (right + 1)

first :: Spine -> Int := λinput.
  deconstruct input into Stop -> 0 | Link value _ _ -> value

shared :: Int -> Int := λn.
  let input = grow n in first (bump input) + first input

Chain ::= End | Node Int Chain

walk :: (Int -> (Int, Chain) -> (Int, Chain)) -> (Int, Chain) -> Chain -> (Int, Chain) := λstep seed input.
  deconstruct input into
    Node value rest -> step value (walk step seed rest)
  | End -> seed

chain :: Int -> Chain := λn.
  if n = 0 then End else Node n (chain (n - 1))

turn :: (Chain -> Int -> Chain) -> Chain -> Chain -> Chain := λrebuild seed input.
  deconstruct input into
    Node value rest -> turn rebuild (rebuild seed value) rest
  | End -> seed

convert :: Chain -> Chain := λinput.
  let _, output =
    walk
      (λvalue (total, tail). total + value, Node (value + 1) tail)
      (0, End)
      input
  in output

convert_and_turn :: Chain -> Chain := λinput.
  let _, output =
    walk
      (λvalue (total, tail). total + value, Node (value + 1) tail)
      (0, End)
      input
  in turn (λtail value. Node value tail) End output

combine :: Chain -> Chain -> Chain := λleft right.
  deconstruct left, right into
    End, End -> End
  | Node x xs, End -> Node x (combine xs End)
  | End, Node y ys -> Node y (combine End ys)
  | Node x xs, Node y ys -> Node (x + y) (combine xs ys)

iterate :: Chain -> Int -> Chain := λbase count.
  let loop = λfactor remaining answer.
    if remaining = 0 then answer else
      let answer' = if remaining % 2 = 0 then answer else combine answer factor in
      loop (combine factor factor) (remaining - 1) answer'
  in loop base count End

start := λ_. first (branch_bump (bump (grow 4)) true) + deconstruct convert_and_turn (convert (iterate (chain 4) 5)) into Node value _ -> value | End -> 0
"#;
    let dir = std::env::temp_dir().join(format!("lukas_owned_data_codegen_{}", std::process::id()));
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
    let bump_owned = generated_function(&generated, "Root_bump_owned_data_0_worker");
    assert!(
        bump_owned.contains("reuse_owned_data3_fast(l0"),
        "the renamed arity-three spine was not rebuilt in place: {bump_owned}"
    );

    let shared = generated_function(&generated, "Root_shared_worker");
    assert!(
        shared.contains("Root_bump_worker(") && !shared.contains("Root_bump_owned_data_0_worker("),
        "a spine with a live alias was consumed: {shared}"
    );

    let branch_owned = generated_function(&generated, "Root_branch_bump_owned_data_0_worker");
    assert!(
        branch_owned
            .matches("Root_branch_bump_owned_data_0_worker(")
            .count()
            >= 2
            && !branch_owned.contains("Root_branch_bump_worker("),
        "mutually exclusive recursive uses did not retain the owned destination: {branch_owned}"
    );

    let walk_owned = generated_function(&generated, "Root_walk_owned_tuple_1_data_2_worker");
    assert!(
        walk_owned.contains("apply_n_owned_last_data"),
        "the custom recursive eliminator did not pass exclusive product and data values to its combiner: {walk_owned}"
    );

    assert!(
        generated.contains("reuse_owned_data2_fast(_owned_data")
            && generated.contains("reuse_owned_tuple2_fast(l1"),
        "the custom combiner did not reuse its exclusive input node and accumulator product"
    );

    let convert = generated_function(&generated, "Root_convert_owned_spine_0_worker");
    assert!(
        convert.contains("Root_walk_owned_tuple_1_data_2_worker"),
        "the custom eliminator's ownership entry was not selected: {convert}"
    );

    let convert_and_turn = generated_function(&generated, "Root_convert_and_turn_worker");
    assert!(
        convert_and_turn.contains("reverse_constructor_spine_owned"),
        "a fresh recursive field returned inside a virtual product lost its destination ownership: {convert_and_turn}"
    );
    assert!(
        generated.contains("bool _own2 = false;")
            && generated.contains("_own2 = _ao")
            && generated.contains("? Root_combine_owned_data_0_worker("),
        "path-linear loop ownership was not carried across the conditional backedge"
    );

    let combine_owned = generated_function(&generated, "Root_combine_owned_data_0_worker");
    assert!(
        combine_owned.contains("for (;;)")
            && combine_owned
                .matches("Root_combine_owned_data_0_worker(")
                .count()
                == 1
            && combine_owned.contains("set_owned_data_field_fast("),
        "the renamed recursive constructor rebuild was not lowered to a forward owned-data loop: {combine_owned}"
    );

    fs::remove_dir_all(dir).unwrap();
}
