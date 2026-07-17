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
#
# c_examples exercise the C backend's own foreign functions (a companion
# `<Module>.c` per program, linked in by c/run.sh). chez_examples are excluded:
# their foreign impls are Scheme (`.ss`), which the C backend cannot link.
set -u

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
RUN="$ROOT_DIR/c/run.sh"

if [ "$#" -ge 1 ]; then
    suites="$*"
else
    suites="examples stdlib_tests tc lang nested_deconstruct"
fi

echo "building mc..."
cargo build -q --bin mc 2>/dev/null || { echo "cargo build failed"; exit 1; }

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
    for d in $dirs; do
        total=$((total + 1))
        status_line="$("$RUN" "$d" 2>/dev/null | head -1)"
        printf '  %s\n' "$status_line"
        if printf '%s' "$status_line" | grep -q ' ok$'; then
            ok=$((ok + 1))
        else
            fails="$fails $(basename "$d")"
        fi
    done

    printf '  -- %d/%d ok' "$ok" "$total"
    [ -n "$fails" ] && printf ' -- failed:%s' "$fails"
    printf '\n'

    grand_ok=$((grand_ok + ok))
    grand_total=$((grand_total + total))
done

echo
echo "==== TOTAL: $grand_ok/$grand_total ok ===="
[ "$grand_ok" -eq "$grand_total" ]
