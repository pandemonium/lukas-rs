#!/usr/bin/env sh
# Build a benchmark under ladies/benchmarks/<name>/ (linking every stdlib `.c`
# companion, which bench-backends.sh does NOT do) and run it at clang -O2 -g with
# GC stats + timing. Set SAMPLE=1 to also capture a `sample` CPU profile (macOS)
# and print the self-time leaders.
#
# Usage: ladies/benchmarks/run.sh [name]   (default: binary_codec)
#        SAMPLE=1 ladies/benchmarks/run.sh binary_codec
set -u

ROOT="$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)"
LIB="${LADY_LIBRARY:-$ROOT/ladies/stdlib}"
NAME="${1:-binary_codec}"
SRC="$ROOT/ladies/benchmarks/$NAME"
W="$(mktemp -d)"

cargo run -q --manifest-path "$ROOT/Cargo.toml" --bin mc -- \
    --library "$LIB" --source "$SRC" --backend native -o "$W/prog.c" || exit 1

# link the program + runtime + every stdlib companion (foreign bindings)
companions="$(find "$LIB" -name '*.c' 2>/dev/null)"
# shellcheck disable=SC2086
clang -std=c11 -I"$ROOT/c" -O2 -g -o "$W/bench" \
    "$ROOT/c/runtime.c" "$ROOT/c/gc.c" $companions "$W/prog.c" || exit 1

if [ "${SAMPLE:-0}" = "1" ]; then
    MARM_GC_STATS=1 "$W/bench" > "$W/out" 2>&1 &
    PID=$!
    sleep 5
    sample "$PID" 25 -f "$W/profile.txt" >/dev/null 2>&1
    wait "$PID"
    cat "$W/out"
    echo "=== self-time leaders ($W/profile.txt) ==="
    awk '/Sort by top of stack/{p=1} p' "$W/profile.txt" | head -20
else
    MARM_GC_STATS=1 /usr/bin/time -p "$W/bench"
fi
