#!/usr/bin/env sh
# Benchmark the C backend against the Chez backend on the SAME Marmelade program.
# Builds both, runs both, checks their outputs agree, and reports wall-clock time.
#
# Usage: ./bench-backends.sh [source-dir]
#   source-dir   a directory containing Root.lady
#                (default: a generated fib(32) microbenchmark)
#
# Env overrides: LADY_LIBRARY, CHEZ_BIN, PETITE_BIN, SCHEME_BOOTDIR.
#
# Reports CPU (user) time of the produced artifact -- stable, unlike wall-clock
# which is dominated by process/dyld startup for these short runs. The Chez
# number includes petite's boot-load CPU that the static C binary doesn't pay.
# The C backend is compiled at `-O2`, Chez at `optimize-level 3`.
set -u

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
LIB="${LADY_LIBRARY:-$ROOT_DIR/ladies/stdlib}"
C_DIR="$ROOT_DIR/c"
SCHEME_DIR="$ROOT_DIR/scheme"
work="$(mktemp -d)"

# --- locate Chez (optional; script still reports the C side without it) ---
CHEZ_BIN="${CHEZ_BIN:-$(command -v chez 2>/dev/null || true)}"
PETITE_BIN="${PETITE_BIN:-$(command -v petite 2>/dev/null || true)}"
BOOTDIR="${SCHEME_BOOTDIR:-}"
if [ -z "$BOOTDIR" ] && command -v brew >/dev/null 2>&1; then
    BOOTDIR="$(find -L "$(brew --prefix chezscheme 2>/dev/null)" -name petite.boot 2>/dev/null \
               | head -1 | sed 's#/petite.boot$##')"
fi

# --- the program under test ---
if [ "$#" -ge 1 ]; then
    SRC="$1"
else
    SRC="$work/fib"
    mkdir -p "$SRC"
    cat >"$SRC/Root.lady" <<'EOF'
fib :: Int -> Int := λn.
  if n < 2 then n
  else fib (n - 1) + fib (n - 2)

start :: Int -> Unit := λ_.
  print_endline "##TC"
  print_endline (prim_show (fib 45))
EOF
fi
name="$(basename "$SRC")"

# Run a command, capture its stdout to $work/out, echo CPU (user+sys) seconds.
timed() {
    /usr/bin/time -p "$@" >"$work/out" 2>"$work/time"
    awk '/^user/ { u = $2 } /^sys/ { s = $2 } END { printf "%.2fs", u + s }' "$work/time"
}
# The program's own output: everything after the ##TC sentinel.
carve() { sed -n '/^##TC$/,$p' "$work/out" | sed '1d'; }

echo "building mc..."
cargo build -q --bin mc 2>/dev/null || { echo "cargo build failed"; exit 1; }

# ---------------- C backend (clang -O2) ----------------
DUMP_C=1 cargo run -q --bin mc -- --library "$LIB" --source "$SRC" >/dev/null 2>"$work/dump.txt"
sed -n '/^======== GENERATED C ========$/,$p' "$work/dump.txt" | sed '1d' >"$work/prog.c"
if ! clang -std=c11 -I"$C_DIR" -O2 -o "$work/cprog" "$C_DIR/runtime.c" "$work/prog.c" 2>"$work/cc.err"; then
    echo "C backend: COMPILE-ERR"; cat "$work/cc.err"; exit 1
fi
c_time="$(timed "$work/cprog")"
c_out="$(carve)"

# ---------------- Chez backend (optimize-level 3) ----------------
chez_time="n/a"
chez_out=""
if [ -n "$CHEZ_BIN" ] && [ -n "$PETITE_BIN" ] && [ -n "$BOOTDIR" ]; then
    cargo run -q --bin mc -- --library "$LIB" --source "$SRC" --scheme "$work/root.ss" 2>/dev/null
    cp "$SCHEME_DIR/runtime.sls" "$SCHEME_DIR/startup.ss" "$work/"
    SCHEMEHEAPDIRS="$BOOTDIR:" "$CHEZ_BIN" -q >/dev/null 2>&1 <<EOF
(import (chezscheme))
(library-directories '(("$work" . "$work")))
(parameterize ([optimize-level 3])
  (compile-library "$work/runtime.sls")
  (compile-file "$work/root.ss")
  (compile-file "$work/startup.ss")
  (make-boot-file "$work/root.boot" '("petite" "scheme")
                  "$work/runtime.so" "$work/root.so" "$work/startup.so"))
EOF
    export SCHEMEHEAPDIRS="$BOOTDIR:"
    chez_time="$(timed "$PETITE_BIN" -b "$BOOTDIR/petite.boot" -b "$work/root.boot")"
    chez_out="$(carve)"
else
    echo "(Chez not found -- set CHEZ_BIN/PETITE_BIN/SCHEME_BOOTDIR or 'brew install chezscheme')"
fi

# ---------------- report ----------------
echo
echo "==== $name ===="
printf '  %-26s %s\n' "C backend (clang -O2)"    "$c_time"
printf '  %-26s %s\n' "Chez backend (opt 3)"     "$chez_time"
if [ -n "$chez_out" ] && [ "$c_out" != "$chez_out" ]; then
    echo "  !! OUTPUTS DIFFER"
    printf '     C:    %s\n' "$(printf '%s' "$c_out" | tr '\n' ' ')"
    printf '     Chez: %s\n' "$(printf '%s' "$chez_out" | tr '\n' ' ')"
else
    printf '  output: %s\n' "$(printf '%s' "$c_out" | tr '\n' ' ')"
fi
