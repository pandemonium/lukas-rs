#!/usr/bin/env sh
# Survey the known-bug repros: each should FAIL (parse/type error or crash),
# except the *_ok boundary programs. Prints the status + first error line.
set -u

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)"
LIB="$ROOT_DIR/ladies/stdlib"

cargo build -q --bin lukas 2>/dev/null || { echo "build failed"; exit 1; }

for dir in "$ROOT_DIR"/ladies/known_bugs/*/; do
  [ -f "$dir/Root.lady" ] || continue
  name="$(basename "$dir")"

  out="$(cargo run -q --bin lukas -- --library "$LIB" --source "$dir" 2>&1)"
  prog="$(printf '%s\n' "$out" | sed -n '/^##TC$/,/^\(####\|\$\$\$\$\)/p' | sed '1d;$d')"

  if printf '%s\n' "$out" | grep -qiE 'panicked|overflowed'; then
    status="CRASH"; detail="$(printf '%s\n' "$out" | grep -oiE 'panicked at [^ ]*' | head -1)"
  elif printf '%s\n' "$out" | grep -qE '^\$\$\$\$'; then
    status="ERR";   detail="$(printf '%s\n' "$out" | grep -E '^\$\$\$\$' | head -1 | cut -c1-72)"
  elif [ -n "$prog" ]; then
    status="ok";    detail="$(printf '%s' "$prog" | tr '\n' ' ')"
  else
    status="????";  detail=""
  fi

  printf '%-24s [%s]  %s\n' "$name" "$status" "$detail"
done
