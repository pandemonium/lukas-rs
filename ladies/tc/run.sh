#!/usr/bin/env sh
# Run the type-class test panel through the interpreter and report status.
#
# The typer is currently very chatty on stdout, so each test's `start` prints a
# plain "##TC" sentinel before its results; the compiler epilogue prints a line
# starting with "####" (a return value) or "$$$$" (a compilation error). We
# carve the program's own output out from between the sentinel and the epilogue.
set -u

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)"
LIB="$ROOT_DIR/ladies/stdlib"

cargo build -q --bin lukas 2>/dev/null || { echo "build failed"; exit 1; }

for dir in "$ROOT_DIR"/ladies/tc/*/; do
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

  printf '%-22s [%s]\n' "$name" "$status"
  [ -n "$prog" ] && printf '%s\n' "$prog" | sed 's/^/    = /'
  case "$status" in
    PANIC)       printf '%s\n' "$out" | grep -E 'panicked at|expr\.typed|static init' | head -2 | sed 's/^/    ! /' ;;
    COMPILE-ERR) printf '%s\n' "$out" | grep '^\$\$\$\$' | head -1 | sed 's/^/    ! /' ;;
  esac
done
