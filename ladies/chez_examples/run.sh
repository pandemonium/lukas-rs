#!/usr/bin/env sh
# Compile each program through the CHEZ backend (compile-lady.sh) and CHECK its
# output against `expected`. These programs use `external`/foreign functions, so
# they only run through the backend -- not the tree-walking interpreter.
#
# Each `start` prints a "##TC" sentinel before its results; we carve everything
# after it (the native run has no "####"/"$$$$" epilogue) and diff it against
# ladies/chez_examples/<name>/expected.
#
# Status:
#   [ok]          carved output matches expected exactly
#   [MISMATCH]    ran, but produced the wrong value
#   [no-expected] ran and produced output, but no expected file to check against
#   [COMPILE-ERR] mc / chez failed to build the program
#   [no-output]   built and ran but produced no ##TC output
set -u

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)"
export LADY_LIBRARY="$ROOT_DIR/ladies/stdlib"

for dir in "$ROOT_DIR"/ladies/chez_examples/*/; do
  [ -f "$dir/Root.lady" ] || continue
  name="$(basename "$dir")"
  run_sh="$ROOT_DIR/build/$name/run.sh"

  rm -f "$run_sh"
  build_out="$("$ROOT_DIR/compile-lady.sh" "$dir" 2>&1)"

  if [ ! -f "$run_sh" ]; then
    status="COMPILE-ERR"; prog=""
  else
    out="$(sh "$run_sh" 2>&1)"
    prog="$(printf '%s\n' "$out" | sed -n '/^##TC$/,$p' | sed '1d')"
    if [ -n "$prog" ]; then
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

  printf '%-34s [%s]\n' "$name" "$status"
  [ -n "$prog" ] && printf '%s\n' "$prog" | sed 's/^/    /'
  case "$status" in
    COMPILE-ERR) printf '%s\n' "$build_out" | grep -iE '\$\$\$\$|error|Exception|no such' | head -1 | sed 's/^/    ! /' ;;
    MISMATCH)    printf '%s\n' "$exp" | sed 's/^/    ! expected: /' ;;
  esac
done
