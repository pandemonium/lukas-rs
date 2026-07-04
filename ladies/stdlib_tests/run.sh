#!/usr/bin/env sh
# Run the standard-library panel and CHECK each program's output against its
# `expected` file. Each program `use Stdlib.` and exercises one feature; each
# `start` prints a "##TC" sentinel before its results; the compiler epilogue
# prints "####"/"$$$$". We carve the output out from between and compare it to
# <name>/expected. See README.md for the current status of each.
#
# Status: [ok] matches expected; [MISMATCH] wrong value; [no-expected] ran but no
# expected file; [COMPILE-ERR] $$$$; [PANIC] crashed; [no-output] genuine failure.
set -u

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)"
LIB="$ROOT_DIR/ladies/stdlib"

cargo build -q --bin lukas 2>/dev/null || { echo "build failed"; exit 1; }

for dir in "$ROOT_DIR"/ladies/stdlib_tests/*/; do
  [ -f "$dir/Root.lady" ] || continue
  name="$(basename "$dir")"

  out="$(cargo run -q --bin lukas -- --library "$LIB" --source "$dir" 2>&1)"
  prog="$(printf '%s\n' "$out" | sed -n '/^##TC$/,/^\(####\|\$\$\$\$\)/p' | sed '1d;$d')"

  if printf '%s\n' "$out" | grep -qE 'panicked|overflowed'; then
    status="PANIC"
  elif [ -n "$prog" ]; then
    if [ -f "$dir/expected" ]; then
      exp="$(cat "$dir/expected")"
      if [ "$prog" = "$exp" ]; then status="ok"; else status="MISMATCH"; fi
    else
      status="no-expected"
    fi
  elif printf '%s\n' "$out" | grep -q '^\$\$\$\$'; then
    status="COMPILE-ERR"
  else
    status="no-output"
  fi

  printf '%-24s [%s]  %s\n' "$name" "$status" "$(printf '%s' "$prog" | tr '\n' ' ')"
  case "$status" in
    PANIC)       printf '%s\n' "$out" | grep -E 'panicked at|Expected a return value' | head -1 | sed 's/^/    ! /' ;;
    COMPILE-ERR) printf '%s\n' "$out" | grep '^\$\$\$\$' | head -1 | sed 's/^/    ! /' ;;
    MISMATCH)    printf '%s\n' "$exp" | sed 's/^/    ! expected: /' ;;
  esac
done
