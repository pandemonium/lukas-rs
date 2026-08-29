use std::{fs, path::PathBuf};

use lukas::compiler::{Backend, Compiler};

#[test]
fn monadic_binder_type_disambiguates_its_record_projection() {
    let dir = std::env::temp_dir().join("lukas_projection_inference");
    fs::create_dir_all(&dir).unwrap();
    fs::write(
        dir.join("Root.lady"),
        r#"use Stdlib.

First ::= { Length :: Int; Name :: Text }
Second ::= { Length :: Int; Enabled :: Bool }

read_first :: IO First := pure { Length := 11; Name := "eleven" }

start :: Int -> IO Int := λ_.
  let* state = read_first in
  pure state.Length
"#,
    )
    .unwrap();

    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: dir.clone(),
        backend: Backend::Native,
        output_file: Some(dir.join("projection.c")),
    }
    .compiler_main()
    .expect("the action fixes `state` to First before typing state.Length");
}
