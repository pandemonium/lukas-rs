//! Reusing a previous elaboration of the library must change *what it costs* to
//! check a program, and nothing else about the answer.
//!
//! The second check here is what a language server does on every save: same
//! program, same library, library already elaborated. See `notes/language-server.md`
//! rung 5.

use std::{collections::BTreeMap, path::PathBuf, time::Instant};

use lukas::{
    compiler::{Backend, Compiler},
    source_map,
    typer::Elaborated,
};

fn compiler(source: &str) -> Compiler {
    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: PathBuf::from(source),
        backend: Backend::Scheme,
        profile: lukas::compiler::ExecutionProfile::Host,
        capability_config: None,
        provider_plan: None,
        requirements_report: None,
        output_file: None,
    }
}

/// Every symbol, rendered -- the whole elaborated table, in a form two runs can be
/// compared by. `Debug` on the typed tree covers the inferred types, so a warm run
/// that got a type wrong shows up here.
fn rendered(symbols: &lukas::phase::SymbolTable<lukas::typer::Types>) -> BTreeMap<String, String> {
    symbols
        .symbols
        .iter()
        .map(|(name, symbol)| (format!("{name:?}"), canonical(&format!("{symbol:?}"))))
        .collect()
}

/// Fresh type-variable and confinement ids come from counters that keep climbing
/// for the life of the process, so a warm run numbers them differently than the cold
/// run it reused. Two elaborations agree if they differ only by a *consistent*
/// renaming: number the ids by first appearance, per counter, and any real
/// disagreement still shows.
fn canonical(rendered: &str) -> String {
    const VARIABLE: &str = "Variable(";
    const CONFINEMENTS: &str = "confinement_quantifiers: {";

    let mut canonical = String::with_capacity(rendered.len());
    let mut seen: std::collections::HashMap<(char, &str), usize> = std::collections::HashMap::new();
    let mut rest = rendered;

    loop {
        let next_marker = [
            rest.find(VARIABLE).map(|at| (at, 'v', VARIABLE.len())),
            rest.find(CONFINEMENTS)
                .map(|at| (at, 'c', CONFINEMENTS.len())),
        ]
        .into_iter()
        .flatten()
        .min_by_key(|(at, _, _)| *at);

        let Some((at, counter, marker)) = next_marker else {
            break;
        };
        canonical.push_str(&rest[..at + marker]);
        rest = &rest[at + marker..];

        // One id, or -- for the quantifier set -- a comma-separated list of them.
        loop {
            let digits = rest.len() - rest.trim_start_matches(|c: char| c.is_ascii_digit()).len();
            if digits > 0 {
                let fresh = seen.len();
                let id = *seen.entry((counter, &rest[..digits])).or_insert(fresh);
                canonical.push_str(&format!("#{id}"));
                rest = &rest[digits..];
            }
            match rest.strip_prefix(", ") {
                Some(remaining) if counter == 'c' => {
                    canonical.push_str(", ");
                    rest = remaining;
                }
                _ => break,
            }
        }
    }

    canonical.push_str(rest);
    canonical
}

/// Check `source` twice, the second time reusing the first's library elaboration.
/// Returns both renderings, both timings, and how many terms were carried.
fn check_twice(
    source: &str,
) -> (
    BTreeMap<String, String>,
    BTreeMap<String, String>,
    f64,
    f64,
    usize,
) {
    let compiler = compiler(source);

    source_map::reset();
    let program = compiler.parse_compilation_unit().expect("parses");
    let started = Instant::now();
    let (cold, warm_state) = compiler
        .check_reusing(program, &Elaborated::default())
        .expect("checks");
    let cold_ms = started.elapsed().as_secs_f64() * 1000.0;

    source_map::reset();
    let program = compiler.parse_compilation_unit().expect("parses");
    let started = Instant::now();
    let (warm, _) = compiler
        .check_reusing(program, &warm_state)
        .expect("checks");
    let warm_ms = started.elapsed().as_secs_f64() * 1000.0;

    (
        rendered(&cold),
        rendered(&warm),
        cold_ms,
        warm_ms,
        warm_state.len(),
    )
}

#[test]
fn a_warm_check_agrees_with_a_cold_one_and_is_far_cheaper() {
    let (cold, warm, cold_ms, warm_ms, carried) = check_twice("ladies/lang/10_syntax");

    assert!(
        carried > 100,
        "expected the library to be carried, got {carried} terms"
    );
    assert_eq!(
        cold.keys().collect::<Vec<_>>(),
        warm.keys().collect::<Vec<_>>(),
        "the warm check produced a different set of symbols"
    );
    for (name, cold_symbol) in &cold {
        assert_eq!(
            cold_symbol, &warm[name],
            "the warm check elaborated `{name}` differently"
        );
    }

    eprintln!("cold {cold_ms:.0} ms -> warm {warm_ms:.0} ms ({carried} terms carried)");
    assert!(
        warm_ms * 4.0 < cold_ms,
        "a warm check should be much cheaper: cold {cold_ms:.0} ms, warm {warm_ms:.0} ms"
    );
}

#[test]
fn a_warm_check_of_a_program_with_witnesses_and_constraints_agrees() {
    // Type classes are where elaboration carries the most state between terms:
    // dictionaries, constraint discharge, signature method placeholders.
    let (cold, warm, cold_ms, warm_ms, carried) =
        check_twice("ladies/examples/09_pattern_matching");

    for (name, cold_symbol) in &cold {
        assert_eq!(
            cold_symbol, &warm[name],
            "the warm check elaborated `{name}` differently"
        );
    }
    eprintln!("cold {cold_ms:.0} ms -> warm {warm_ms:.0} ms ({carried} terms carried)");
}

/// Check `source` cold, then check `edited` warm on top of that result, then check
/// `edited` cold, and hand back both renderings of the *edited* program along with
/// what the warm check cost.
fn check_edit(
    source: &str,
    edit: impl Fn(&str) -> String,
) -> (
    BTreeMap<String, String>,
    BTreeMap<String, String>,
    f64,
    f64,
    usize,
) {
    let compiler = compiler(source);
    let root = PathBuf::from(source).join("Root.lady");
    let original = std::fs::read_to_string(&root).expect("the program");
    let edited = edit(&original);
    assert_ne!(original, edited, "the edit changed nothing");

    let check = |text: &str, warm: &Elaborated| {
        source_map::reset();
        source_map::with_overlay(
            [(root.clone(), text.to_owned())].into_iter().collect(),
            || {
                let program = compiler.parse_compilation_unit().expect("parses");
                let started = Instant::now();
                let (symbols, next) = compiler.check_reusing(program, warm).expect("checks");
                let ms = started.elapsed().as_secs_f64() * 1000.0;
                (rendered(&symbols), next, ms)
            },
        )
    };

    let (_, before, _) = check(&original, &Elaborated::default());
    let (warm, _, warm_ms) = check(&edited, &before);
    let (cold, _, cold_ms) = check(&edited, &Elaborated::default());

    (cold, warm, cold_ms, warm_ms, before.len())
}

fn agree(cold: &BTreeMap<String, String>, warm: &BTreeMap<String, String>) {
    assert_eq!(
        cold.keys().collect::<Vec<_>>(),
        warm.keys().collect::<Vec<_>>(),
        "the warm check produced a different set of symbols"
    );
    for (name, cold_symbol) in cold {
        assert_eq!(
            cold_symbol, &warm[name],
            "the warm check elaborated `{name}` differently"
        );
    }
}

/// The whole safety argument for carrying work across an edit, in one test: a
/// check that reuses what the programmer did not touch has to agree with a check
/// that reuses nothing. A stale type that survives an edit shows up here as a
/// symbol the two checks disagree about.
#[test]
fn an_edited_declaration_is_rechecked_and_the_rest_is_carried() {
    // A body, changed, with the declaration's type left alone: the case the
    // editor sees on nearly every keystroke.
    let (cold, warm, cold_ms, warm_ms, carried) = check_edit("ladies/lang/10_syntax", |text| {
        text.replace("same_line :: Int := 40 + 2", "same_line :: Int := 40 + 3")
    });

    agree(&cold, &warm);
    eprintln!("edit one body: cold {cold_ms:.0} ms -> warm {warm_ms:.0} ms ({carried} carried)");
}

/// An edit that changes a declaration's *type* must reach everything that reads
/// it, however far away. `digest` is used by `start`, which is used by nothing --
/// so the dependents are what the check has to find on its own.
#[test]
fn an_edit_that_changes_a_type_invalidates_what_reads_it() {
    let (cold, warm, cold_ms, warm_ms, _) = check_edit("ladies/lang/10_syntax", |text| {
        text.replace(
            "interpolated :: Int -> Text := λn. \"the answer is `n`.\"",
            "interpolated :: Int -> Text := λn. \"the answer is `n`!\"",
        )
    });

    agree(&cold, &warm);
    eprintln!("edit a used term: cold {cold_ms:.0} ms -> warm {warm_ms:.0} ms");
}

/// Adding a declaration changes what names mean elsewhere, so nothing is carried.
/// It still has to be *right*, which is what this asserts.
#[test]
fn adding_a_declaration_still_checks_correctly() {
    let (cold, warm, ..) = check_edit("ladies/lang/10_syntax", |text| {
        format!("{text}\n\nafterthought :: Int := 3\n")
    });

    agree(&cold, &warm);
}

/// An edit inside the library is an edit like any other: the program that uses it
/// has to be re-checked against what the library now says.
#[test]
fn an_edit_to_a_library_module_reaches_its_users() {
    let compiler = compiler("ladies/lang/10_syntax");
    let library = PathBuf::from("ladies/stdlib/Stdlib/Data/List.lady");
    let original = std::fs::read_to_string(&library).expect("the module");
    let edited = original.replace(
        "length :: ∀α. List α -> Int",
        "length :: ∀α. List α -> Int (* counted *)",
    );
    assert_ne!(original, edited, "the edit changed nothing");

    let check = |text: &str, warm: &Elaborated| {
        source_map::reset();
        source_map::with_overlay(
            [(library.clone(), text.to_owned())].into_iter().collect(),
            || {
                let program = compiler.parse_compilation_unit().expect("parses");
                let (symbols, next) = compiler.check_reusing(program, warm).expect("checks");
                (rendered(&symbols), next)
            },
        )
    };

    let (_, before) = check(&original, &Elaborated::default());
    let (warm, _) = check(&edited, &before);
    let (cold, _) = check(&edited, &Elaborated::default());
    agree(&cold, &warm);
}
