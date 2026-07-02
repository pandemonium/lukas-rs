#!/usr/bin/env sh
# Run the standard-library test panel: each program `use Stdlib.` and exercises
# one feature. See README.md for the current status of each.
set -u

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)"
LIB="$ROOT_DIR/ladies/stdlib"

cargo build -q --bin lukas 2>/dev/null || { echo "build failed"; exit 1; }

for dir in "$ROOT_DIR"/ladies/stdlib_tests/*/; do
  [ -f "$dir/Root.lady" ] || continue
  name="$(basename "$dir")"

  out="$(cargo run -q --bin lukas -- --library "$LIB" --source "$dir" 2>&1)"
  prog="$(printf '%s\n' "$out" | sed -n '/^##TC$/,/^\(####\|\$\$\$\$\)/p' | sed '1d;$d')"

  if printf '%s\n' "$out" | grep -q 'panicked'; then
    status="PANIC"
  elif [ -n "$prog" ]; then
    status="ran"
  elif printf '%s\n' "$out" | grep -q '^\$\$\$\$'; then
    status="COMPILE-ERR"
  else
    status="no-output"
  fi

  printf '%-20s [%s]  %s\n' "$name" "$status" "$(printf '%s' "$prog" | tr '\n' ' ')"
  case "$status" in
    PANIC)       printf '%s\n' "$out" | grep -E 'panicked at|Expected a return value' | head -1 | sed 's/^/    ! /' ;;
    COMPILE-ERR) printf '%s\n' "$out" | grep '^\$\$\$\$' | head -1 | sed 's/^/    ! /' ;;
  esac
done
