#!/usr/bin/env sh
# Run the C-backend example gallery and CHECK each program's output against its
# `expected` file. Unlike the `examples` panel (which runs the tree-walking
# interpreter), these programs use `foreign` functions with no interpreter body,
# so they must go through the C backend: `mc` emits C, which is compiled and
# linked against the runtime plus each module's companion `<dir>/*.c`.
#
# Each `start` prints a "##TC" sentinel before its results; we carve everything
# after it and diff against ladies/c_examples/<name>/expected. Status tokens
# match the `examples` panel so ladies/run.sh aggregates them the same way:
#   [ok]          carved output matches expected exactly
#   [MISMATCH]    ran, but produced the wrong value
#   [no-expected] ran and produced output, but no expected file
#   [COMPILE-ERR] $$$$ from the front end, or the C compiler rejected the output
#   [CRASH]       mc panicked, or the program crashed / timed out
#   [no-output]   no ##TC output and no error
set -u

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)"
LIB="$ROOT_DIR/ladies/stdlib"
C_DIR="$ROOT_DIR/c"
: "${TIMEOUT:=20}"

cargo build -q --bin mc 2>/dev/null || { echo "build failed"; exit 1; }

for dir in "$ROOT_DIR"/ladies/c_examples/*/; do
  [ -f "$dir/Root.lady" ] || continue
  name="$(basename "$dir")"
  work="$(mktemp -d)"

  # Front end: emit C. No output file written means a parse/type error ($$$$) or
  # a codegen panic.
  cargo run -q --bin mc -- --library "$LIB" --source "$dir" \
    --backend native -o "$work/program.c" >"$work/out.txt" 2>"$work/err.txt"

  prog=""
  if [ ! -s "$work/program.c" ]; then
    if grep -q 'panicked' "$work/err.txt"; then
      status="CRASH"
    else
      status="COMPILE-ERR"
    fi
  else
    # Companion C for this module's `foreign` declarations, if any.
    foreign_cs=""
    for f in "$dir"/*.c; do
      [ -e "$f" ] && foreign_cs="$foreign_cs $f"
    done

    # shellcheck disable=SC2086 # $foreign_cs is an intentional list of paths.
    if ! clang -std=c11 -I"$C_DIR" -o "$work/prog" \
        "$C_DIR/runtime.c" "$C_DIR/gc.c" $foreign_cs "$work/program.c" \
        2>"$work/cc.err"; then
      status="COMPILE-ERR"
    else
      "$work/prog" >"$work/out" 2>&1 &
      prog_pid=$!
      ( sleep "$TIMEOUT"; kill -9 "$prog_pid" 2>/dev/null ) &
      killer_pid=$!
      wait "$prog_pid" 2>/dev/null
      rc=$?
      kill -9 "$killer_pid" 2>/dev/null
      wait "$killer_pid" 2>/dev/null

      prog="$(sed -n '/^##TC$/,$p' "$work/out" | sed '1d')"

      if [ "$rc" -eq 137 ]; then
        status="CRASH"
      elif [ -n "$prog" ]; then
        if [ -f "$dir/expected" ]; then
          exp="$(cat "$dir/expected")"
          [ "$prog" = "$exp" ] && status="ok" || status="MISMATCH"
        else
          status="no-expected"
        fi
      else
        status="no-output"
      fi
    fi
  fi

  printf '%-34s [%s]\n' "$name" "$status"
  [ -n "$prog" ] && printf '%s\n' "$prog" | sed 's/^/    /'
  case "$status" in
    CRASH)       grep 'panicked at' "$work/err.txt" | head -1 | sed 's/^/    ! /' ;;
    COMPILE-ERR) { grep '^\$\$\$\$' "$work/out.txt"; head -3 "$work/cc.err" 2>/dev/null; } | head -1 | sed 's/^/    ! /' ;;
    MISMATCH)    printf '%s\n' "$exp" | sed 's/^/    ! expected: /' ;;
  esac

  rm -rf "$work"
done
