//! Lightweight, opt-in wall-clock profiling for compiler passes.
//!
//! Set `MARM_PROFILE=1` to print timings to stderr. Keeping this separate from
//! diagnostic tracing makes profiling useful even when verbose trace events
//! would distort the workload being measured.

use std::{sync::OnceLock, time::Instant};

fn enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("MARM_PROFILE").is_some())
}

/// Run `work`, reporting its elapsed wall time when profiling is enabled.
pub fn time<T>(label: impl AsRef<str>, work: impl FnOnce() -> T) -> T {
    if !enabled() {
        return work();
    }

    let start = Instant::now();
    let result = work();
    eprintln!(
        "[profile] {:>10.3} ms  {}",
        start.elapsed().as_secs_f64() * 1_000.0,
        label.as_ref()
    );
    result
}

/// Run `work`, reporting it only when it takes at least `minimum_ms`.
pub fn time_if_slow<T>(label: impl AsRef<str>, minimum_ms: f64, work: impl FnOnce() -> T) -> T {
    if !enabled() {
        return work();
    }

    let start = Instant::now();
    let result = work();
    let elapsed_ms = start.elapsed().as_secs_f64() * 1_000.0;
    if elapsed_ms >= minimum_ms {
        eprintln!("[profile] {elapsed_ms:>10.3} ms  {}", label.as_ref());
    }
    result
}
