#!/usr/bin/env sh
# Compile and run every `ladies/` program through the C backend, checking each
# against its `expected` file, and print a per-suite + overall summary.
#
# Usage: c/run-all.sh [suite ...]
#   With no args, runs the suites meant to pass end-to-end:
#     examples c_examples stdlib_tests tc lang nested_deconstruct
#   Name suites explicitly to override, e.g.
#     c/run-all.sh examples stdlib_tests
#     c/run-all.sh known_bugs          # expected to fail; no `expected` files
#
# Env: TIMEOUT (per-program run cap, seconds; forwarded to c/run.sh).
#      JOBS    (concurrency, default 16). Every suite COMPILES JOBS-at-a-time;
#              the benchmarks suite then RUNS serially so its timings mean
#              something, while other suites also run JOBS-at-a-time.
#
# c_examples exercise the C backend's own foreign functions (a companion
# `<Module>.c` per program, linked in by c/run.sh). chez_examples are excluded:
# their foreign impls are Scheme (`.ss`), which the C backend cannot link.
set -u

: "${JOBS:=16}"

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
RUN="$ROOT_DIR/c/run.sh"

if [ "$#" -ge 1 ]; then
    suites="$*"
else
    suites="examples c_examples stdlib_tests tc lang nested_deconstruct"
fi

echo "building mc..."
cargo build -q --release --bin mc 2>/dev/null || { echo "cargo build failed"; exit 1; }

grand_ok=0
grand_total=0

for suite in $suites; do
    suite_dir="$ROOT_DIR/ladies/$suite"
    [ -d "$suite_dir" ] || { echo "== $suite (no such suite) =="; continue; }

    echo
    echo "== $suite =="
    ok=0
    total=0
    fails=""

    # Every directory that contains a Root.lady, in sorted order.
    dirs="$(find "$suite_dir" -name Root.lady 2>/dev/null | sed 's#/Root.lady$##' | sort)"

    # Two phases. Compiling is pure CPU with no shared state, so every suite
    # compiles JOBS-at-a-time. Running is different: a benchmark measures time,
    # and a neighbour competing for cores and memory bandwidth would make that
    # measurement meaningless -- so benchmarks run one at a time while ordinary
    # suites, which only check output, keep running concurrently.
    case "$suite" in
        benchmarks) run_jobs=1 ;;
        *)          run_jobs="$JOBS" ;;
    esac

    results="$(mktemp -d)"
    builds="$(mktemp -d)"

    # Phase 1: compile everything, JOBS at a time. A failure here writes its own
    # status line, which phase 2 leaves in place.
    index=0
    pids=""
    running=0
    for d in $dirs; do
        index=$((index + 1))
        slot="$(printf '%04d' "$index")"
        PHASE=build WORK="$builds/$slot" "$RUN" "$d" >"$results/$slot" 2>/dev/null &
        pids="$pids $!"
        running=$((running + 1))
        if [ "$running" -ge "$JOBS" ]; then
            # Wait on the OLDEST outstanding job: `wait -n` would be the precise
            # tool, and macOS's bash 3.2 does not have it.
            # shellcheck disable=SC2086
            set -- $pids
            wait "$1" 2>/dev/null
            shift
            pids="$*"
            running=$((running - 1))
        fi
    done
    wait

    # Phase 2: run whatever compiled, `run_jobs` at a time.
    index=0
    pids=""
    running=0
    for d in $dirs; do
        index=$((index + 1))
        slot="$(printf '%04d' "$index")"
        [ -s "$results/$slot" ] && continue   # already failed to build
        PHASE=run WORK="$builds/$slot" "$RUN" "$d" >"$results/$slot" 2>/dev/null &
        pids="$pids $!"
        running=$((running + 1))
        if [ "$running" -ge "$run_jobs" ]; then
            # shellcheck disable=SC2086
            set -- $pids
            wait "$1" 2>/dev/null
            shift
            pids="$*"
            running=$((running - 1))
        fi
    done
    wait

    # Report in the original order, so output is byte-identical to a sequential
    # run however the jobs happened to interleave.
    index=0
    for d in $dirs; do
        index=$((index + 1))
        total=$((total + 1))
        status_line="$(head -1 "$results/$(printf '%04d' "$index")" 2>/dev/null)"
        printf '  %s\n' "$status_line"
        if printf '%s' "$status_line" | grep -q ' ok$'; then
            ok=$((ok + 1))
        else
            fails="$fails $(basename "$d")"
        fi
    done
    rm -rf "$results" "$builds"

    printf '  -- %d/%d ok' "$ok" "$total"
    [ -n "$fails" ] && printf ' -- failed:%s' "$fails"
    printf '\n'

    grand_ok=$((grand_ok + ok))
    grand_total=$((grand_total + total))
done

echo
echo "==== TOTAL: $grand_ok/$grand_total ok ===="
[ "$grand_ok" -eq "$grand_total" ]
