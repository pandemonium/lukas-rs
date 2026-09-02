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

# PHASE selects which half to do: `build` stops after producing the executable,
# `run` assumes it is already there, `all` (the default) does both. `WORK` names
# where the artifacts live, so a `build` and a later `run` can find each other --
# c/run-all.sh uses this to compile every program concurrently and still run
# benchmarks one at a time, where a concurrent neighbour would distort timings.
: "${PHASE:=all}"

dir="$1"
name="$(basename "$dir")"
work="${WORK:-$(mktemp -d)}"
mkdir -p "$work"

if [ "$PHASE" != run ]; then

# Generate C straight to a file. mc prints "$$$$ …" (to stdout) on a front-end
# or type error and panics (a codegen `todo!()`) to stderr; in either case no
# output file is written, so an unwritten/empty file is our "generation failed".
# Prefer the built binary: `cargo run` takes the build lock, which serialises
# callers that run several examples at once (see c/run-all.sh). Fall back to
# cargo when the binary is absent, so running this script alone still works.
MC="$ROOT_DIR/target/release/mc"
if [ -x "$MC" ]; then
    "$MC" --library "$LIB" --source "$dir" \
        --backend native -o "$work/program.c" >"$work/out.txt" 2>"$work/err.txt"
else
    cargo run -q --release --bin mc -- --library "$LIB" --source "$dir" \
        --backend native -o "$work/program.c" >"$work/out.txt" 2>"$work/err.txt"
fi
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

# Companion C files implementing this module's `foreign` declarations, if any:
# one `<Module>.c` per module, living beside its `.lady` source.
foreign_cs=""
for f in "$dir"/*.c; do
    [ -e "$f" ] && foreign_cs="$foreign_cs $f"
done
# ...and the companions living beside stdlib modules in the library tree
# (e.g. Stdlib/Memory.c beside Memory.lady). Harmless to link even when unused.
for f in $(find "$LIB" -name '*.c' 2>/dev/null); do
    foreign_cs="$foreign_cs $f"
done

# The same flags compile-lady.sh builds with -- the panel must exercise the
# binary people actually run, not an unoptimised one.
. "$C_DIR/cflags.sh"

# shellcheck disable=SC2086 # $foreign_cs and $CFLAGS are intentional lists.
if ! clang $CSTD -I"$C_DIR" $CFLAGS -o "$work/prog" "$C_DIR/runtime.c" "$C_DIR/gc.c" $foreign_cs "$work/program.c" 2>"$work/cc.err"; then
    echo "[$name] COMPILE-ERR"
    cat "$work/cc.err"
    exit 1
fi

fi # end build phase

if [ "$PHASE" = build ]; then
    exit 0
fi

if [ ! -x "$work/prog" ]; then
    # The build phase already reported why; say nothing a second time.
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

# Any other non-zero status is a real failure and must be said out loud. Letting
# it fall through to the output diff reports a crashing program as a mismatch --
# or, with no `expected` file, as no failure at all.
if [ "$rc" -ne 0 ]; then
    if [ "$rc" -gt 128 ]; then
        echo "[$name] CRASH (signal $((rc - 128)))"
    else
        echo "[$name] EXIT $rc"
    fi
    sed -n '/^##TC$/,$p' "$work/out" | sed '1d;s/^/  /'
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
