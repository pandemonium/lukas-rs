use std::{fs, path::PathBuf};

use lukas::compiler::{Backend, Compiler};

#[test]
fn perhaps_uses_zero_niche_and_nested_perhaps_falls_back_to_a_tag() {
    let output = std::env::temp_dir().join("lukas_niche_layout.c");
    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: PathBuf::from("ladies/lang/13_flat_sum_arrays"),
        backend: Backend::Native,
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
    // Once the record is ground, its Perhaps Int field also uses a one-word niche.
    // Together with Pair's two words and Text's one, the record is four words wide
    // under the outer Perhaps. The record is splatted, so all four are leaves --
    // but the first is the field's own niche word, where zero spells `Nope`, so the
    // outer niche must skip it and take Pair's `X` at offset 1. This is the same
    // rule the `Occupied` case below asserts for a constructor payload; taking
    // offset 0 here made `This { Maybe := Nope, .. }` read back as `Nope`.
    assert!(
        generated.contains("(int64_t[]){-2, 0, 1, 1, 1, 4, 0, 0, 0, 0}, 10"),
        "the outer niche took a word its record payload can legitimately zero"
    );
    // Occupied has three constructor arguments. Its first is itself niche-encoded,
    // so zero is valid there; selection must continue and use the Text at offset 1.
    assert!(
        generated.contains("(int64_t[]){-2, 0, 1, 1, 3, -2, 0, 1, 0, 1, 0, 0, 2, 0, 0}, 15"),
        "niche search stopped before the later eligible payload field"
    );
}
