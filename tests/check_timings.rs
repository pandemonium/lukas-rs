//! The table `notes/incremental-checking.md` asks for, on demand.
//!
//! `cargo test --release --test check_timings -- --ignored --nocapture`
//!
//! Cold is the first check of a session; warm is what the editor pays after a
//! keystroke. Ignored because it is a measurement, not an assertion.

use std::{path::PathBuf, time::Instant};

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
        output_file: None,
    }
}

/// One cold check, then `repeats` warm ones, in milliseconds.
fn timings(source: &str, repeats: usize) -> (f64, Vec<f64>) {
    let compiler = compiler(source);

    source_map::reset();
    let program = compiler.parse_compilation_unit().expect("parses");
    let started = Instant::now();
    let (_, mut state) = compiler
        .check_reusing(program, &Elaborated::default())
        .expect("checks");
    let cold = started.elapsed().as_secs_f64() * 1000.0;

    let warm = (0..repeats)
        .map(|_| {
            source_map::reset();
            let program = compiler.parse_compilation_unit().expect("parses");
            let started = Instant::now();
            let (_, next) = compiler.check_reusing(program, &state).expect("checks");
            state = next;
            started.elapsed().as_secs_f64() * 1000.0
        })
        .collect();

    (cold, warm)
}

/// `MARM_BENCH_REPEATS` warm checks per program, for a profile with enough
/// samples in it to mean something.
fn repeats() -> usize {
    std::env::var("MARM_BENCH_REPEATS")
        .ok()
        .and_then(|repeats| repeats.parse().ok())
        .unwrap_or(5)
}

#[test]
#[ignore = "measurement"]
fn check_timings() {
    for source in [
        "ladies/usurper",
        "ladies/lang/10_syntax",
        "ladies/lang/09_pattern_matching",
    ] {
        let (cold, warm) = timings(source, repeats());
        let best = warm.iter().cloned().fold(f64::INFINITY, f64::min);
        let worst = warm.iter().cloned().fold(0.0, f64::max);
        println!("{source:36} cold {cold:7.0} ms   warm {best:6.0}-{worst:.0} ms");
    }
}
