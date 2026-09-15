//! Holes compile as ordinary polymorphic panic applications.
use lukas::{
    compiler::{Backend, Compiler},
    source_map,
};
use std::{collections::HashMap, path::PathBuf};

#[test]
fn holes_fit_values_functions_and_arguments() {
    let directory = std::env::temp_dir().join(format!("lady-holes-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let root = directory.join("Root.lady");
    let text = "use Stdlib.\nvalue :: Int := ???\nfunction :: Int -> Text := ???\nhole_apply :: (Int -> Int) -> Int := λf. f 1\nargument :: Int := hole_apply ???\nstart :: Int -> Unit := λ_. print_endline \"ok\"\n";
    std::fs::write(&root, text).unwrap();
    let compiler = Compiler {
        library_path: PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("ladies/stdlib"),
        source_path: directory.clone(),
        backend: Backend::Scheme,
        output_file: None,
    };
    source_map::reset();
    source_map::with_overlay(HashMap::new(), || {
        let symbols = compiler.check().expect("holes must typecheck");
        let rendered = format!("{symbols:?}");
        assert!(rendered.contains("Unimplemented hole ???"));
        assert!(rendered.contains("Root.lady:2:17"));
    });
    std::fs::remove_dir_all(directory).unwrap();
}
