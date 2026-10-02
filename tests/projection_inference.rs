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
        profile: lukas::compiler::ExecutionProfile::Host,
        capability_config: None,
        provider_plan: None,
        requirements_report: None,
        output_file: Some(dir.join("projection.c")),
    }
    .compiler_main()
    .expect("the action fixes `state` to First before typing state.Length");
}

#[test]
fn later_expression_disambiguates_projection_in_a_monomorphic_let() {
    let dir = std::env::temp_dir().join("lukas_projection_inference_monomorphic_let");
    fs::create_dir_all(&dir).unwrap();
    fs::write(
        dir.join("Root.lady"),
        r#"use Stdlib.

Monster ::= { Defense :: Int; Hit_Points :: Int }
Armor ::= { Defense :: Int; Block_Chance :: Int }

score :: Perhaps Monster -> Int := λmaybe.
  let score_monster = λmonster.
    let defense = 0 + monster.Defense in
    monster.Hit_Points - defense
  in perhaps 0 score_monster maybe

start :: Int -> Unit := λ_. ()
"#,
    )
    .unwrap();

    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: dir.clone(),
        backend: Backend::Native,
        profile: lukas::compiler::ExecutionProfile::Host,
        capability_config: None,
        provider_plan: None,
        requirements_report: None,
        output_file: None,
    }
    .check()
    .expect("the later `Hit_Points` projection fixes the earlier `Defense` base to Monster");
}
