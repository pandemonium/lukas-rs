#!/usr/bin/env sh
# Run the example gallery through the interpreter and show each program's output.
# Each `start` prints a "##TC" sentinel before its results; the compiler epilogue
# prints "####"/"$$$$". We carve the program output out from between.
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
    status="CRASH"
  elif [ -n "$prog" ]; then
    status="ok"
  elif printf '%s\n' "$out" | grep -q '^\$\$\$\$'; then
    status="COMPILE-ERR"
  else
    status="no-output"
  fi

  printf '%-34s [%s]\n' "$name" "$status"
  [ -n "$prog" ] && printf '%s\n' "$prog" | sed 's/^/    /'
  case "$status" in
    CRASH)       printf '%s\n' "$out" | grep -E 'panicked at|Expected a return value|overflowed' | head -1 | sed 's/^/    ! /' ;;
    COMPILE-ERR) printf '%s\n' "$out" | grep '^\$\$\$\$' | head -1 | sed 's/^/    ! /' ;;
  esac
done
