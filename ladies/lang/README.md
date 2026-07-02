# Language-feature panel

A condensed, self-contained tour of the core Marmelade language (the pieces that
show up across the other `ladies/` programs), separate from the type-class panel in
`ladies/tc/`. Each test depends only on builtins (`print_endline`, `prim_show`,
arithmetic/comparison, `Int`/`Text`/`Bool`) plus what it defines itself — so nothing
here relies on the standard library (which currently does not elaborate).

Run one:

```
cargo run -q --bin lukas -- --library ladies/stdlib --source ladies/lang/03_recursion
```

Or the whole panel: `./ladies/lang/run.sh`. Each program prints a `##TC` sentinel then
its result lines.

| # | Test | Features | Expected |
|---|------|----------|----------|
| 01 | `01_basics` | int/text/bool literals, `+ - * / %`, comparison, `and`/`or`, `if/then/else`, `let … in`, nested let + shadowing | `12` / `yes` / `100` / `30` |
| 02 | `02_functions` | λ, currying, partial application, higher-order combinators (`id`, `compose`, `flip`, `const`) | `42` / `42` / `7` / `5` |
| 03 | `03_recursion` | self-recursive top-level functions | `120` / `89` |
| 04 | `04_adt` | ADT declaration, `deconstruct` over constructors, literal + `otherwise` clauses | `300` / `12` / `0` / `zero` / `many` |
| 05 | `05_tuples` | tuple construction, ordinal projection (`.0/.1/.2`), tuple patterns | `6` / `100` / `12` |
| 06 | `06_records` | record declaration, construction (`{ F := v }`), field projection (`.F`), record patterns (`{ F: x }`) | `25` / `7` |
| 07 | `07_modules` | `module M:` grouping, qualified access `M.f` (incl. self-qualified refs) | `27` / `6` |
| 08 | `08_interpolation` | string interpolation `` "`expr`" `` (renders each segment via a `Display` instance in scope) | `Hello Ada, you are 36, and next year you will be 37.` |

## Notes / deliberately omitted corners

- **String interpolation desugars to a `display` call**, so `08` defines a local
  `Display` signature + `Int`/`Text` witnesses. Without a `Display` in scope,
  interpolation raises `Unknown name 'display'`.
- **`let*` / `let+`** (monadic/functor bind sugar, seen in `ladies/bindops`) are *not*
  covered: they desugar to a symbol that currently only resolves through the standard
  library, which does not elaborate at the moment, so a hermetic test isn't possible
  yet.
- **Record type declarations** need each field on its own line (layout-sensitive); a
  single-line `{ X :: Int  Y :: Int }` does not parse.
- **Layout gotcha:** a single-clause `deconstruct` on its own line immediately
  followed by another top-level declaration mis-parses (the following declaration gets
  swallowed) — the same clause-attachment bug as `ladies/nested_deconstruct/`. Here
  `swap` is written with projections to avoid it; the tuple-pattern `deconstruct` is
  still exercised inside `start` (where nothing follows it).
