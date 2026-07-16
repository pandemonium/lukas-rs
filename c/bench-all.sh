#!/usr/bin/env sh
# Compile every ladies program through BOTH backends, then time running all the
# compiled artifacts -- C natives vs Chez boot files -- to compare total runtime.
#
# Two phases, kept separate on purpose: (1) compile everything (not timed),
# (2) run each backend's whole set and time it. Only programs that BOTH backends
# compiled to a runnable artifact are included, so the comparison is apples to
# apples.
#
# Usage: c/bench-all.sh [suite ...]      (default: examples stdlib_tests tc lang)
# Env:   REPEAT (passes over the full set per backend, default 3).
#
# NB: these gallery programs do trivial work and exit, so total runtime is
# dominated by process/startup cost (a static C binary vs petite booting), not
# compute. For a compute comparison see bench-backends.sh (fib).
set -u

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
LIB="${LADY_LIBRARY:-$ROOT_DIR/ladies/stdlib}"
C_DIR="$ROOT_DIR/c"
SCHEME_DIR="$ROOT_DIR/scheme"
work="$(mktemp -d)"
: "${REPEAT:=3}"

CHEZ_BIN="${CHEZ_BIN:-$(command -v chez 2>/dev/null || true)}"
PETITE_BIN="${PETITE_BIN:-$(command -v petite 2>/dev/null || true)}"
BOOTDIR="${SCHEME_BOOTDIR:-}"
if [ -z "$BOOTDIR" ] && command -v brew >/dev/null 2>&1; then
    BOOTDIR="$(find -L "$(brew --prefix chezscheme 2>/dev/null)" -name petite.boot 2>/dev/null \
               | head -1 | sed 's#/petite.boot$##')"
fi
if [ -z "$CHEZ_BIN" ] || [ -z "$PETITE_BIN" ] || [ -z "$BOOTDIR" ]; then
    echo "Chez not found (need chez, petite, and petite.boot) -- 'brew install chezscheme'"; exit 1
fi

if [ "$#" -ge 1 ]; then suites="$*"; else suites="examples stdlib_tests tc lang"; fi

echo "building mc..."
cargo build -q --bin mc 2>/dev/null || { echo "cargo build failed"; exit 1; }

# Shared build inputs: the C runtime object and the Chez runtime/startup, all
# compiled once (per-program work reuses them).
clang -std=c11 -I"$C_DIR" -O2 -c "$C_DIR/runtime.c" -o "$work/runtime.o"
clang -std=c11 -I"$C_DIR" -O2 -c "$C_DIR/gc.c" -o "$work/gc.o"
cp "$SCHEME_DIR/runtime.sls" "$SCHEME_DIR/startup.ss" "$work/"

# ---------- phase 1: compile every program through both backends ----------
echo "compiling (both backends)..."
: >"$work/c_list"
chez_script="$work/compile.ss"
{
    echo '(import (chezscheme))'
    echo "(library-directories '((\"$work\" . \"$work\")))"
    echo '(parameterize ([optimize-level 3])'
    echo "  (compile-library \"$work/runtime.sls\")"
    echo "  (compile-file \"$work/startup.ss\")"
} >"$chez_script"

i=0
declare_ok=""
for suite in $suites; do
    for f in $(find "$ROOT_DIR/ladies/$suite" -name Root.lady 2>/dev/null | sort); do
        d="$(dirname "$f")"
        i=$((i + 1))

        # C backend: emit + compile.
        cargo run -q --bin mc -- --library "$LIB" --source "$d" \
            --backend native -o "$work/p_$i.c" 2>/dev/null || continue
        [ -s "$work/p_$i.c" ] || continue
        clang -std=c11 -I"$C_DIR" -O2 -o "$work/c_$i" "$work/p_$i.c" "$work/runtime.o" "$work/gc.o" 2>/dev/null || continue

        # Chez backend: emit .ss; queue its compile into the single chez session.
        cargo run -q --bin mc -- --library "$LIB" --source "$d" -o "$work/r_$i.ss" 2>/dev/null || continue
        [ -f "$work/r_$i.ss" ] || continue
        printf '  (compile-file "%s")(make-boot-file "%s" (quote ("petite" "scheme")) "%s" "%s" "%s")\n' \
            "$work/r_$i.ss" "$work/b_$i.boot" "$work/runtime.so" "$work/r_$i.so" "$work/startup.so" \
            >>"$chez_script"
        declare_ok="$declare_ok $i:$suite/$(basename "$d")"
    done
done
echo ')' >>"$chez_script"

SCHEMEHEAPDIRS="$BOOTDIR:" "$CHEZ_BIN" -q --script "$chez_script" >/dev/null 2>"$work/chez.err" \
    || { echo "chez compile failed:"; tail -3 "$work/chez.err"; }

# Keep only programs where BOTH artifacts exist; build the run lists.
: >"$work/c_list"; : >"$work/chez_list"; n=0
for entry in $declare_ok; do
    id="${entry%%:*}"
    if [ -x "$work/c_$id" ] && [ -f "$work/b_$id.boot" ]; then
        echo "$work/c_$id" >>"$work/c_list"
        echo "$work/b_$id.boot" >>"$work/chez_list"
        n=$((n + 1))
    fi
done
echo "compiled $n programs through both backends (of $i scanned)"
[ "$n" -gt 0 ] || { echo "nothing to run"; exit 1; }

# ---------- phase 2: run each backend's whole set, timed ----------
cat >"$work/run_c.sh" <<EOF
#!/bin/sh
r=0; while [ \$r -lt $REPEAT ]; do
  while read b; do "\$b" >/dev/null 2>&1; done < "$work/c_list"
  r=\$((r + 1))
done
EOF
cat >"$work/run_chez.sh" <<EOF
#!/bin/sh
export SCHEMEHEAPDIRS="$BOOTDIR:"
r=0; while [ \$r -lt $REPEAT ]; do
  while read b; do "$PETITE_BIN" -b "$BOOTDIR/petite.boot" -b "\$b" >/dev/null 2>&1; done < "$work/chez_list"
  r=\$((r + 1))
done
EOF

# Warm-up (untimed): pay macOS's one-time per-binary first-launch verification
# (Gatekeeper/syspolicyd) up front, so the timed passes measure steady-state
# execution rather than the OS scanning 64 freshly-built, unsigned binaries.
echo "warming up..."
while read b; do "$b" >/dev/null 2>&1; done < "$work/c_list"
SCHEMEHEAPDIRS="$BOOTDIR:" sh -c 'while read b; do "'"$PETITE_BIN"'" -b "'"$BOOTDIR"'/petite.boot" -b "$b" >/dev/null 2>&1; done' < "$work/chez_list"

echo "running C backend artifacts ($n progs x $REPEAT passes)..."
/usr/bin/time -p sh "$work/run_c.sh" 2>"$work/t_c.txt"
echo "running Chez backend artifacts ($n progs x $REPEAT passes)..."
/usr/bin/time -p sh "$work/run_chez.sh" 2>"$work/t_chez.txt"

cpu() { awk '/^user/{u=$2}/^sys/{s=$2}END{printf "%.2f", u+s}' "$1"; }
real() { awk '/^real/{printf "%.2f", $2}' "$1"; }

c_cpu="$(cpu "$work/t_c.txt")";      c_real="$(real "$work/t_c.txt")"
z_cpu="$(cpu "$work/t_chez.txt")";   z_real="$(real "$work/t_chez.txt")"

echo
echo "==== total runtime: $n programs x $REPEAT passes ===="
printf '  %-22s cpu %ss   real %ss\n' "C backend (clang -O2)" "$c_cpu" "$c_real"
printf '  %-22s cpu %ss   real %ss\n' "Chez backend (opt 3)"  "$z_cpu" "$z_real"
awk -v c="$c_real" -v z="$z_real" 'BEGIN{ if (c>0) printf "  Chez/C real ratio: %.1fx\n", z/c }'
