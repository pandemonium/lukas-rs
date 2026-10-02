use std::{fs, path::PathBuf};

use lukas::compiler::{Backend, Compiler};

fn compiler_for(test_name: &str, source: &str) -> Compiler {
    let dir = std::env::temp_dir().join(format!("lukas_type_error_{test_name}"));
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("Root.lady"), source).unwrap();
    let output_file = dir.join("out.c");
    Compiler {
        library_path: PathBuf::from("ladies/stdlib"),
        source_path: dir,
        backend: Backend::Native,
        output_file: Some(output_file),
    }
}

/// Compile a program that must be accepted, returning nothing. Used for the
/// positive half of the confinement gate matrix: a boundary check is only as
/// good as the safe programs it still admits.
fn accepts(test_name: &str, source: &str) {
    if let Err(error) = compiler_for(test_name, source).compiler_main() {
        panic!("{test_name} must compile, but: {error}");
    }
}

/// Compile a program that must be rejected, returning the diagnostic.
fn rejects(test_name: &str, source: &str) -> String {
    compiler_for(test_name, source)
        .compiler_main()
        .expect_err("this program must be rejected")
        .to_string()
}

#[test]
fn coproduct_pattern_against_function_is_a_located_type_error() {
    let source = r#"
Box ::= Box Int

bad :: (Int -> Int) -> Int := λvalue.
  deconstruct value into
    Box n -> n

start := λ_. 0
"#;

    let error = compiler_for("pattern_type_mismatch", source)
        .compiler_main()
        .expect_err("the ill-typed pattern must be rejected");
    let diagnostic = error.to_string();

    assert!(diagnostic.contains("Root.lady:6:"), "{diagnostic}");
    assert!(
        diagnostic.contains("cannot match a value of type"),
        "{diagnostic}"
    );
    assert!(diagnostic.contains("Int -> Int"), "{diagnostic}");
}

#[test]
fn thread_spawn_rejects_io_returning_a_confined_value() {
    // Inline, like every other case here. This used to compile `ladies/examples/37_threads`
    // instead -- a program that must NOT compile, sitting in the suite `c/run-all.sh`
    // expects to pass end to end, where it read as a broken example rather than as this
    // test's fixture.
    let diagnostic = rejects(
        "thread_confined_result",
        r#"
use Stdlib.
use Stdlib.Threading.
use Stdlib.IO.

main :: IO Int :=
  let* buffer = Buffer.new_buffer 3 in
  let* t = Thread.spawn (pure buffer) in
  pure 2

start := λ_. ()
"#,
    );

    assert!(diagnostic.contains("Root.lady:8:"), "{diagnostic}");
    assert!(
        diagnostic.contains(
            "type `Root.Prelude.Buffer` is confined, but this context requires unconfined"
        ),
        "{diagnostic}"
    );
}

#[test]
fn thread_spawn_rejects_io_capturing_a_confined_value() {
    let diagnostic = rejects(
        "thread_confined_capture",
        r#"
use Stdlib.
use Stdlib.Threading.
use Stdlib.IO.

main :: IO Int :=
  let* buffer = Buffer.new_buffer 3 in
  let* t = Thread.spawn (Suspend (λ_.
    let ignored = Buffer.put_u8 buffer 1 in
    ())) in
  pure 2

start := λ_. ()
"#,
    );

    assert!(diagnostic.contains("Root.lady:8:"), "{diagnostic}");
    assert!(
        diagnostic.contains("this action captures `Root.Prelude.Buffer`, which is confined"),
        "{diagnostic}"
    );
}

// ----------------------------------------------------------------- the gate matrix
//
// `Thread.spawn` takes `(IO α) : unconfined`, which constrains both the values the
// action captured before it began and the value crossing back at `join`. These
// cover both halves, and both the accepting and rejecting side of each: a boundary
// that rejects everything is not a boundary, it is a wall.

#[test]
fn thread_spawn_accepts_an_action_capturing_only_unconfined_values() {
    accepts(
        "thread_unconfined_capture",
        r#"
use Stdlib.
use Stdlib.Threading.
use Stdlib.IO.

Config ::=
  { retries :: Int
    label   :: Text
  }

main :: IO Int :=
  let config = { retries := 3; label := "worker" } in
  let* t = Thread.spawn (Suspend (λ_. config.retries)) in
  pure 2

start := λ_. ()
"#,
    );
}

#[test]
fn thread_spawn_accepts_a_confined_intermediate_consumed_inside_the_action() {
    // The whole point of keeping the capture index separate from the result
    // capability: a Buffer created, used and discarded inside the action never
    // reaches a thread boundary, so the action stays spawnable.
    accepts(
        "thread_confined_intermediate",
        r#"
use Stdlib.
use Stdlib.Threading.
use Stdlib.IO.

fill :: IO Unit :=
  let* buffer = Buffer.new_buffer 3 in
  let ignored = Buffer.put_u8 buffer 1 in
  pure ()

main :: IO Int :=
  let* t = Thread.spawn fill in
  pure 2

start := λ_. ()
"#,
    );
}

#[test]
fn thread_spawn_accepts_an_unconfined_opaque_wrapper() {
    // A trusted assertion by the defining module: the confined representation is
    // reachable only through an API that mediates every access. The compiler takes
    // the author's word for it -- that is what `unconfined opaque` means.
    accepts(
        "thread_unconfined_opaque",
        r#"
use Stdlib.
use Stdlib.Threading.
use Stdlib.IO.

unconfined opaque Locked_Buffer ::= Make_Locked_Buffer Buffer

module Locked_Buffer:
  new :: Int -> IO Locked_Buffer := λn.
    let* raw = Buffer.new_buffer n in
    pure (Make_Locked_Buffer raw)

main :: IO Int :=
  let* locked = Locked_Buffer.new 3 in
  let* t = Thread.spawn (Suspend (λ_. deconstruct locked into Make_Locked_Buffer _ -> 1)) in
  pure 2

start := λ_. ()
"#,
    );
}

#[test]
fn thread_spawn_rejects_a_confined_value_nested_in_a_captured_record() {
    // Wrapping a Buffer in a record must not launder it, and the diagnostic must
    // name the field rather than only the enclosing type.
    let diagnostic = rejects(
        "thread_nested_confined_capture",
        r#"
use Stdlib.
use Stdlib.Threading.
use Stdlib.IO.

Workspace ::=
  { scratch :: Buffer
    retries :: Int
  }

main :: IO Int :=
  let* buffer = Buffer.new_buffer 3 in
  let workspace = { scratch := buffer; retries := 3 } in
  let* t = Thread.spawn (Suspend (λ_. workspace.retries)) in
  pure 2

start := λ_. ()
"#,
    );

    assert!(
        diagnostic.contains("this action captures `Root.Workspace`"),
        "{diagnostic}"
    );
    assert!(
        diagnostic.contains("confined because `scratch` is `Root.Prelude.Buffer`"),
        "{diagnostic}"
    );
}

#[test]
fn thread_spawn_rejects_a_transparent_wrapper_around_a_confined_value() {
    // Unlike `unconfined opaque`, a transparent coproduct cannot override
    // structural confinement: callers can unwrap it without going through any API.
    let diagnostic = rejects(
        "thread_transparent_wrapper",
        r#"
use Stdlib.
use Stdlib.Threading.
use Stdlib.IO.

Wrapped ::= Wrap Buffer

main :: IO Int :=
  let* buffer = Buffer.new_buffer 3 in
  let wrapped = Wrap buffer in
  let* t = Thread.spawn (Suspend (λ_. deconstruct wrapped into Wrap _ -> 1)) in
  pure 2

start := λ_. ()
"#,
    );

    assert!(
        diagnostic.contains("this action captures `Root.Wrapped`"),
        "{diagnostic}"
    );
    assert!(
        diagnostic.contains("confined because `Wrap` is `Root.Prelude.Buffer`"),
        "{diagnostic}"
    );
}

#[test]
fn thread_spawn_rejects_a_confined_value_nested_in_the_result() {
    // The result half of the judgment: nothing confined crosses back at `join`
    // either, however deeply it is buried.
    let diagnostic = rejects(
        "thread_nested_confined_result",
        r#"
use Stdlib.
use Stdlib.Threading.
use Stdlib.IO.

Workspace ::=
  { scratch :: Buffer
    retries :: Int
  }

build :: IO Workspace :=
  let* buffer = Buffer.new_buffer 3 in
  pure { scratch := buffer; retries := 3 }

main :: IO Int :=
  let* t = Thread.spawn build in
  pure 2

start := λ_. ()
"#,
    );

    assert!(
        diagnostic.contains("type `Root.Workspace` is confined"),
        "{diagnostic}"
    );
    assert!(
        diagnostic.contains("because `scratch` is `Root.Prelude.Buffer`"),
        "{diagnostic}"
    );
}

// ---------------------------------------------------------------- exhaustiveness
//
// The covered space of a match is a UNION OF BOXES, and widening it to the single box
// that contains them accepts matches that are not exhaustive. These pin the boundary
// from both sides: the widening cases must be rejected, and the ordinary case splits a
// person actually writes must still be accepted.

#[test]
fn a_missing_combination_of_two_scrutinees_is_not_exhaustive() {
    // Three of the four pairs. Joining them gives {This,Nope} x {This,Nope} -- the full
    // space -- which is exactly the false "exhaustive" this guards.
    let source = r#"
use Stdlib.

both :: Perhaps Int -> Perhaps Int -> Int := λa b.
  deconstruct (a, b) into
    (This x, This y) -> x + y
  | (This x, Nope)   -> x
  | (Nope,   This y) -> y

start := λ_. 0
"#;

    let diagnostic = rejects("nonexhaustive_pair", source);
    assert!(diagnostic.contains("not exhaustive"), "{diagnostic}");
    assert!(diagnostic.contains("(Nope, Nope)"), "{diagnostic}");
}

#[test]
fn a_gap_inside_a_matched_constructor_is_not_exhaustive() {
    let source = r#"
use Stdlib.

inner :: Perhaps (Perhaps Int) -> Int := λa.
  deconstruct a into
    This (This x) -> x
  | Nope -> 0

start := λ_. 0
"#;

    let diagnostic = rejects("nonexhaustive_nested", source);
    assert!(diagnostic.contains("not exhaustive"), "{diagnostic}");
    assert!(diagnostic.contains("This Nope"), "{diagnostic}");
}

#[test]
fn every_combination_of_two_scrutinees_is_exhaustive() {
    let source = r#"
use Stdlib.

both :: Perhaps Int -> Perhaps Int -> Int := λa b.
  deconstruct (a, b) into
    (This x, This y) -> x + y
  | (This x, Nope)   -> x
  | (Nope,   This y) -> y
  | (Nope,   Nope)   -> 0

start := λ_. 0
"#;

    accepts("exhaustive_pair", source);
}

#[test]
fn the_fourth_clause_of_a_two_scrutinee_split_is_still_useful() {
    // The reject-side twin of the case above: `Nope, Nope` is reachable, and reporting
    // it as dead code would refuse a perfectly ordinary program.
    let source = r#"
use Stdlib.

both :: Perhaps Int -> Perhaps Int -> Int := λa b.
  deconstruct (a, b) into
    (This x, This y) -> x + y
  | (This x, Nope)   -> x
  | (Nope,   This y) -> y
  | (Nope,   Nope)   -> 0

start := λ_. 0
"#;

    accepts("useful_fourth_clause", source);
}

#[test]
fn a_recursive_type_matched_only_by_a_binding_is_exhaustive() {
    // Splitting a column whose constructors nobody wrote would expand `List` for ever;
    // this is the termination case.
    let source = r#"
use Stdlib.

count :: List Int -> Int := λxs.
  deconstruct xs into
    everything -> 0

start := λ_. 0
"#;

    accepts("wildcard_over_recursive_type", source);
}

// ------------------------------------------------- constraints at repeated use sites
//
// Two self-recursive calls spliced into ONE interpolation used to leave the second
// `display` with a metavariable that no substitution could ground: unification reached
// the lambda's codomain twice and bound it to a fresh variable each time, and composing
// the two dropped the earlier image instead of recording that the two were equal. The
// stale constraint was then misread as parametric, giving a signature-free dictionary
// parameter to a term whose signature has no context -- and the generated code called a
// `Node` as though it were a dictionary.

#[test]
fn two_self_recursive_calls_in_one_interpolation_ground_the_same_constraint() {
    let source = r#"
use Stdlib.

Node ::= Leaf Text | Pair Node Node

render :: Node -> Text := λnode.
  let walk = λn.
    deconstruct n into
      Leaf t -> t
    | Pair x y -> "`walk x``walk y`"
  in walk node

start := λ_. 0
"#;

    accepts("repeated_self_recursive_splice", source);
}
