#!/usr/bin/env sh
# Run the whole test panel: every ladies/<panel>/run.sh in turn, then a summary.
#
# Pass tokens differ by panel ([ran] for tc/lang/stdlib_tests, [ok] for
# examples); anything else ([PANIC] [CRASH] [COMPILE-ERR] [no-output]) counts as
# a failure. `known_bugs/` is a catalogue of expected-failure repros, so it is
# deliberately NOT part of this aggregate.
#
# Known intentional red in the lang panel: 09_pattern_matching (a match-
# exhaustiveness bug we keep exposed on purpose) plus 10_syntax and
# 11_broken_syntax (syntax-exploration repros with no `expected` output). So a
# "green" run is currently lang 8/11, every other panel full -- including
# c_examples, which run through the C backend (mc + companion `.c`), not the
# interpreter. Exit code is 0 only when every counted case passes.
set -u

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"

# Build once up front; each panel's own `cargo build` is then a no-op.
cargo build -q --bin lukas 2>/dev/null || { echo "build failed"; exit 1; }

PANELS="tc lang stdlib_tests examples c_examples"

total_pass=0
total_count=0
summary=""

for panel in $PANELS; do
  script="$ROOT_DIR/$panel/run.sh"
  [ -f "$script" ] || continue

  printf '\n========== %s ==========\n' "$panel"
  out="$(sh "$script" 2>&1)"
  printf '%s\n' "$out"

  pass="$(printf '%s\n' "$out" | grep -cE '\[(ran|ok)\]')"
  fail="$(printf '%s\n' "$out" | grep -cE '\[(PANIC|CRASH|COMPILE-ERR|no-output|MISMATCH|no-expected)\]')"
  count=$((pass + fail))

  total_pass=$((total_pass + pass))
  total_count=$((total_count + count))
  summary="${summary}$(printf '  %-14s %s/%s' "$panel" "$pass" "$count")
"
done

printf '\n========== summary ==========\n'
printf '%s' "$summary"
printf '  %-14s %s/%s\n' "TOTAL" "$total_pass" "$total_count"

[ "$total_pass" -eq "$total_count" ]
