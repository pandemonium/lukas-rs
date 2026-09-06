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
fn loop_hot_workers_inline_and_slices_borrow_until_they_escape() {
    let source = r#"
use Stdlib.

hash_prime :: Int := 1099511628211

small_hash :: Int -> Int := λn.
  let loop = λi h.
    if i <= 0 then h else loop (i - 1) ((h xor i) * hash_prime)
  in loop n 7

hot :: Int -> Int -> Int := λn acc.
  if n <= 0 then acc else hot (n - 1) (acc + small_hash n)

cold_leaf :: Int -> Int := λn. n + 1

cold_exit :: Int -> Int := λn.
  if n <= 0 then cold_leaf n else cold_exit (n - 1)

allocating :: Bytes -> Int -> Int := λbytes n.
  if n <= 0 then Bytes.length bytes
  else allocating (Bytes.slice bytes 0 (Bytes.length bytes)) (n - 1)

borrow_hot :: Bytes -> Int -> Int -> Int := λbytes n acc.
  if n <= 0 then acc
  else
    let view = Bytes.slice bytes 0 (Bytes.length bytes) in
    borrow_hot bytes (n - 1) (acc + Bytes.length view)

scan_bytes :: Bytes -> Int -> Int := λbytes n.
  if n <= 0 then Bytes.get_u8 bytes 0
  else scan_bytes bytes (n - 1)

outer :: Bytes -> Int -> Int := λbytes n.
  if n <= 0 then 0
  else
    let used = borrow_hot bytes 1 0 in
    outer bytes (n - 1)

mixed :: Bytes -> Int -> Int := λbytes n.
  if n <= 0 then Bytes.length bytes
  else if n = 1
    then mixed (Bytes.slice bytes 0 (Bytes.length bytes)) (n - 1)
    else mixed bytes (n - 1)

module Fake:
  module Prelude:
    module Bytes:
      raw_sub :: Bytes -> Int -> Int -> Bytes := λbytes _ _. bytes

fake_hot :: Bytes -> Int -> Int := λbytes n.
  if n <= 0 then Bytes.length bytes
  else
    let view = Fake.Prelude.Bytes.raw_sub bytes 0 (Bytes.length bytes) in
    fake_hot view (n - 1)

start := λ_. hot 2 0
"#;
    let dir = std::env::temp_dir().join(format!("lukas_c_hot_loop_codegen_{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("Root.lady"), source).unwrap();
    let output = dir.join("program.c");
    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: dir,
        backend: Backend::Native,
        output_file: Some(output.clone()),
    }
    .compiler_main()
    .expect("native code generation");
    let generated = fs::read_to_string(&output).unwrap();

    let helper = generated_function(&generated, "Root_small_hash_worker");
    assert!(
        generated[..generated.find(helper).unwrap()]
            .contains("MARM_ALWAYS_INLINE Value Root_small_hash_worker(Value);"),
        "small direct worker called from a loop was not marked always-inline"
    );
    assert!(
        !generated.contains("MARM_ALWAYS_INLINE Value Root_cold_leaf_worker"),
        "a helper used only on a loop's cold exit was marked always-inline"
    );

    let allocating = generated_function(&generated, "Root_allocating_worker");
    assert!(allocating.contains("for (;;)"), "{allocating}");
    assert!(allocating.contains("raw_sub_worker"), "{allocating}");
    assert!(!allocating.contains("_poll"), "{allocating}");

    let borrowed = generated_function(&generated, "Root_borrow_hot_worker");
    assert!(borrowed.contains("Slice _bs"), "{borrowed}");
    assert!(borrowed.contains("slice_sub_borrowed"), "{borrowed}");
    assert!(borrowed.contains("gc_escape_borrowed"), "{borrowed}");
    assert!(
        borrowed.contains("_poll"),
        "a loop whose allocation was scalar-replaced still needs a poll: {borrowed}"
    );

    let scan = generated_function(&generated, "Root_scan_bytes_worker");
    assert!(scan.contains("const uint8_t *_ib"), "{scan}");
    assert!(scan.contains("slice_base_get_u8(_ib"), "{scan}");
    assert!(
        !scan.contains("raw_get_u8_worker"),
        "an invariant immutable byte view still reloads its Slice descriptor: {scan}"
    );

    let mixed = generated_function(&generated, "Root_mixed_worker");
    assert!(mixed.contains("for (;;)"), "{mixed}");
    assert!(mixed.contains("raw_sub_worker"), "{mixed}");
    assert!(
        mixed.contains("_poll"),
        "an allocation on only one back-edge suppressed the required poll: {mixed}"
    );

    let outer = generated_function(&generated, "Root_outer_worker");
    assert!(
        outer.contains("_poll"),
        "a scalar-replacing callee cannot safepoint a repeatedly calling loop: {outer}"
    );

    let fake = generated_function(&generated, "Root_fake_hot_worker");
    assert!(
        !fake.contains("slice_sub_borrowed"),
        "a user symbol resembling the old mangled suffix acquired intrinsic semantics: {fake}"
    );

    assert!(
        generated
            .contains("MARM_PURE extern Value Root_Prelude_Bytes_raw_slice_len_worker(Value);"),
        "read-only byte intrinsic did not carry its C purity attribute"
    );
    assert!(
        generated.contains(
            "MARM_NORETURN MARM_COLD extern Value Root_Prelude_raw_omg_wtf_bbq_worker(Value, Value, Value, Value, Value);"
        ),
        "non-returning intrinsic did not carry its C control-flow attribute"
    );
    assert!(
        !generated.contains("volatile struct { const ClosureDesc *desc;"),
        "an immediate stack closure retained the redundant volatile aggregate barrier"
    );
    assert!(
        generated.contains("static const Value Root_hash_prime ="),
        "a literal Int global remained opaque to clang"
    );
    assert!(
        !generated.contains("&Root_hash_prime,"),
        "an immediate constant was unnecessarily registered as a GC root"
    );

    fs::remove_dir_all(output.parent().unwrap()).unwrap();
}
