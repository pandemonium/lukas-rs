#!/usr/bin/env sh
# Compile a Marmelade example through the C backend and run it.
# Usage: c/run.sh <example-dir>
#   e.g. c/run.sh ladies/examples/03_functions
#
# Emits the program's C to a temp file, compiles it with the runtime, runs it,
# and (if an `expected` file is present) diffs the program output -- the lines
# printed after the `##TC` sentinel -- against it.
#
# One-line status: [name] ok | MISMATCH | GEN-PANIC | COMPILE-ERR | TIMEOUT |
#                          (no expected). Env: TIMEOUT (run cap, default 20s).
set -u

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
LIB="${LADY_LIBRARY:-$ROOT_DIR/ladies/stdlib}"
C_DIR="$ROOT_DIR/c"
: "${TIMEOUT:=20}"

dir="$1"
name="$(basename "$dir")"
work="$(mktemp -d)"

# Generate C straight to a file. mc prints "$$$$ …" (to stdout) on a front-end
# or type error and panics (a codegen `todo!()`) to stderr; in either case no
# output file is written, so an unwritten/empty file is our "generation failed".
cargo run -q --bin mc -- --library "$LIB" --source "$dir" \
    --backend native -o "$work/program.c" >"$work/out.txt" 2>"$work/err.txt"
if [ ! -s "$work/program.c" ]; then
    if grep -q 'panicked' "$work/err.txt"; then
        echo "[$name] GEN-PANIC"
        grep 'panicked at' "$work/err.txt" | head -1 | sed 's/^/  /'
    else
        echo "[$name] GEN-ERR"
        grep '^\$\$\$\$' "$work/out.txt" | head -1 | sed 's/^/  /'
    fi
    exit 1
fi

if ! clang -std=c11 -I"$C_DIR" -o "$work/prog" "$C_DIR/runtime.c" "$work/program.c" 2>"$work/cc.err"; then
    echo "[$name] COMPILE-ERR"
    cat "$work/cc.err"
    exit 1
fi

# Run under a timeout so a non-terminating program can't stall the harness.
"$work/prog" >"$work/out" 2>&1 &
prog_pid=$!
( sleep "$TIMEOUT"; kill -9 "$prog_pid" 2>/dev/null ) &
killer_pid=$!
wait "$prog_pid" 2>/dev/null
rc=$?
kill -9 "$killer_pid" 2>/dev/null
wait "$killer_pid" 2>/dev/null

if [ "$rc" -eq 137 ]; then
    echo "[$name] TIMEOUT (${TIMEOUT}s)"
    exit 1
fi

prog="$(sed -n '/^##TC$/,$p' "$work/out" | sed '1d')"

if [ -f "$dir/expected" ]; then
    exp="$(cat "$dir/expected")"
    if [ "$prog" = "$exp" ]; then
        echo "[$name] ok"
    else
        echo "[$name] MISMATCH"
        printf '%s\n' "$prog" | sed 's/^/  got:      /'
        printf '%s\n' "$exp"  | sed 's/^/  expected: /'
    fi
else
    echo "[$name] (no expected)"
    printf '%s\n' "$prog" | sed 's/^/  /'
fi
