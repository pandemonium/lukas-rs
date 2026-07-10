//! Rust-style modules: `module X.` mounts a file-backed module under its
//! *declaring parent* (the filesystem mirrors the tree, so a child `X` of a
//! module whose children live in `<dir>/` sits at `<dir>/X.lady` and its own
//! children in `<dir>/X/`). `use A.B.` opens an already-mounted nested module by
//! path; `use X.` opens a top-level module.
//!
//! Each test writes a small module tree to a temp dir, compiles it, and
//! evaluates `start 0`.

use std::{fs, path::PathBuf};

use lukas::{
    ast::{self, ROOT_MODULE_NAME, namer::QualifiedName},
    compiler::Compiler,
    parser::IdentifierPath,
};

/// Write `files` (relative path -> contents) into a fresh temp dir, compile the
/// Root module, and evaluate `start 0`.
fn eval_tree(test_name: &str, files: &[(&str, &str)]) -> Result<String, String> {
    let dir = std::env::temp_dir().join(format!("lukas_mod_{test_name}"));
    let _ = fs::remove_dir_all(&dir);
    for (rel, contents) in files {
        let path = dir.join(rel);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    let compiler = Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: dir,
        scheme_file: None,
    };

    let env = compiler
        .compile_and_initialize()
        .map_err(|e| format!("compilation failed: {e}"))?;

    env.call(
        &QualifiedName::new(IdentifierPath::new(ROOT_MODULE_NAME), "start"),
        ast::Literal::Int(0),
    )
    .map(|value| format!("{value}"))
    .map_err(|e| format!("evaluation failed: {e:?}"))
}

/// `module Data.` mounts `Data.lady`; inside it `module List.` mounts
/// `Data/List.lady`. The leaf is reachable by its full path `Data.List.thing`.
#[test]
fn module_mounts_under_declaring_parent() {
    let files = [
        (
            "Root.lady",
            "module Data.\nstart :: Int -> Int := λ_. Data.List.thing\n",
        ),
        ("Data.lady", "module List.\n"),
        ("Data/List.lady", "thing :: Int := 7\n"),
    ];
    assert_eq!(eval_tree("mount_parent", &files), Ok("7".to_string()));
}

/// A multi-segment `use Data.List.` opens the nested module, bringing its
/// members into unqualified scope.
#[test]
fn path_form_use_opens_nested_module() {
    let files = [
        (
            "Root.lady",
            "module Data.\nuse Data.List.\nstart :: Int -> Int := λ_. thing\n",
        ),
        ("Data.lady", "module List.\n"),
        ("Data/List.lady", "thing :: Int := 9\n"),
    ];
    assert_eq!(eval_tree("path_use", &files), Ok("9".to_string()));
}

/// `use Outer.` mounts the whole subtree (a top-level module found by the
/// source/library search); `use Outer.Data.List.` then opens a leaf three levels
/// deep. Both a fully-qualified reference and the opened bare name resolve.
#[test]
fn use_top_level_then_open_nested_path() {
    let files = [
        (
            "Root.lady",
            "use Outer.\nuse Outer.Data.List.\n\
             start :: Int -> Int := λ_. thing + Outer.Data.List.thing\n",
        ),
        ("Outer.lady", "module Data.\n"),
        ("Outer/Data.lady", "module List.\n"),
        ("Outer/Data/List.lady", "thing :: Int := 21\n"),
    ];
    assert_eq!(eval_tree("open_nested_path", &files), Ok("42".to_string()));
}

/// A `module X.` whose file is missing is a clear load error, not a panic or an
/// obscure I/O failure buried elsewhere.
#[test]
fn missing_module_file_is_a_load_error() {
    let files = [(
        "Root.lady",
        "module Gone.\nstart :: Int -> Int := λ_. 0\n",
    )];
    let result = eval_tree("missing_module", &files);
    assert!(
        result
            .as_ref()
            .is_err_and(|e| e.contains("Gone") && e.to_lowercase().contains("module")),
        "expected a clear missing-module error naming `Gone`, got: {result:?}"
    );
}
