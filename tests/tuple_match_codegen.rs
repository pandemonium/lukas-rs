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
fn tuple_literal_is_matched_through_separate_locals() {
    let source = r#"
use Stdlib.

sum_pairs :: List Int -> List Int -> Int := λleft right.
  deconstruct left, right into
    Nil, Nil -> 0
  | Cons x xs, Cons y ys -> x + y + sum_pairs xs ys
  | Nil, Cons _ _ -> 1
  | Cons _ _, Nil -> 2

tail_equal :: List Int -> List Int -> Bool := λleft right.
  deconstruct left, right into
    Nil, Nil -> true
  | Cons x xs, Cons y ys -> if x = y then tail_equal xs ys else false
  | _ -> false

keep_fallback :: List Int -> List Int -> (List Int, List Int) := λleft right.
  deconstruct left, right into
    Nil, Nil -> Nil, Nil
  | whole -> whole

make_pair :: Int -> Int -> (Int, Int) := λleft right. left, right

start := λ_.
  let xs = from [1; 2] in
  sum_pairs xs xs + if tail_equal xs xs then 1 else 0
"#;
    let dir =
        std::env::temp_dir().join(format!("lukas_tuple_match_codegen_{}", std::process::id()));
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
    for name in ["Root_sum_pairs_worker", "Root_tail_equal_worker"] {
        let function = generated_function(&generated, name);
        assert!(
            function.contains("_scrut") || function.contains("_tscrut"),
            "{function}"
        );
        assert!(
            !function.contains("mk_tuple2(l0, l1)"),
            "an immediately matched tuple was still allocated: {function}"
        );
    }

    let dead_fallback = generated_function(&generated, "Root_tail_equal_worker");
    assert!(
        !dead_fallback.contains("mk_tuple2("),
        "an unused whole-tuple fallback was still materialized: {dead_fallback}"
    );

    let live_fallback = generated_function(&generated, "Root_keep_fallback_worker");
    assert!(
        live_fallback.contains("mk_tuple2("),
        "a used whole-tuple fallback lost its required materialization: {live_fallback}"
    );

    let fallback = generated_function(&generated, "Root_make_pair_worker");
    assert!(
        fallback.contains("mk_tuple2(l0, l1)"),
        "an escaping tuple lost its required value: {fallback}"
    );

    fs::remove_dir_all(dir).unwrap();
}
