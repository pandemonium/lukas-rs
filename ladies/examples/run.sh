#!/usr/bin/env sh
# Run the example gallery and CHECK each program's output against its `expected`
# file. Every `start` prints a "##TC" sentinel before its results; the compiler
# epilogue prints "####"/"$$$$". We carve the program output out from between and
# diff it against ladies/examples/<name>/expected.
#
# Status:
#   [ok]          carved output matches expected exactly
#   [MISMATCH]    ran, but produced the wrong value (a genuine failure)
#   [no-expected] ran and produced output, but no expected file to check against
#   [COMPILE-ERR] $$$$ from the front end
#   [CRASH]       panicked / overflowed
#   [no-output]   no ##TC output and no error — a genuine failure
set -u

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)"
LIB="$ROOT_DIR/ladies/stdlib"

cargo build -q --bin lukas 2>/dev/null || { echo "build failed"; exit 1; }

for dir in "$ROOT_DIR"/ladies/examples/*/; do
  [ -f "$dir/Root.lady" ] || continue
  name="$(basename "$dir")"

  out="$(cargo run -q --bin lukas -- --library "$LIB" --source "$dir" 2>&1)"
  prog="$(printf '%s\n' "$out" | sed -n '/^##TC$/,/^\(####\|\$\$\$\$\)/p' | sed '1d;$d')"

  if printf '%s\n' "$out" | grep -qE 'panicked|overflowed'; then
    status="PANIC"
  elif [ -n "$prog" ]; then
    if [ -f "$dir/expected" ]; then
      exp="$(cat "$dir/expected")"
      if [ "$prog" = "$exp" ]; then
        status="ok"
      else
        status="MISMATCH"
      fi
    else
      status="no-expected"
    fi
  elif printf '%s\n' "$out" | grep -q '^\$\$\$\$'; then
    status="COMPILE-ERR"
  else
    status="no-output"
  fi

  printf '%-34s [%s]\n' "$name" "$status"
  [ -n "$prog" ] && printf '%s\n' "$prog" | sed 's/^/    /'
  case "$status" in
    PANIC)       printf '%s\n' "$out" | grep -E 'panicked at|Expected a return value|overflowed' | head -1 | sed 's/^/    ! /' ;;
    COMPILE-ERR) printf '%s\n' "$out" | grep '^\$\$\$\$' | head -1 | sed 's/^/    ! /' ;;
    MISMATCH)    printf '%s\n' "$exp" | sed 's/^/    ! expected: /' ;;
  esac
done
