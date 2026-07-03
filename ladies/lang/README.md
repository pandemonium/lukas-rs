# Language-feature panel

A condensed, self-contained tour of the core Marmelade language (the pieces that
show up across the other `ladies/` programs), separate from the type-class panel in
`ladies/tc/`. Each test depends only on builtins (`print_endline`, `prim_show`,
arithmetic/comparison, `Int`/`Text`/`Bool`) plus what it defines itself — so each test
is a hermetic, minimal reproduction.

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
| 05 | `05_tuples` | tuple construction, ordinal projection (`.0/.1/.2`), inline tuple pattern (`λ(a, b). …`), tuple pattern in `deconstruct` | `6` / `100` / `12` |
| 06 | `06_records` | record declaration, construction (`{ F := v }`), field projection (`.F`), record patterns (`{ F: x }`) | `25` / `7` |
| 07 | `07_modules` | `module M:` grouping, qualified access `M.f` (incl. self-qualified refs) | `27` / `6` |
| 08 | `08_interpolation` | string interpolation `` "`expr`" `` (renders each segment via a `Display` instance in scope) | `Hello Ada, you are 36, and next year you will be 37.` |
| 09 | `09_pattern_matching` | `deconstruct` in depth: list-prefix matching (`Cons a (Cons b _)`), deep constructor nesting (`Branch (Leaf _) (Leaf _)`), tree recursion, record patterns with literal fields, **bare nullary constructors in record fields** (first/middle/adjacent positions, and nested under `Cons`), record patterns nested under `Cons`, multiple scrutinees, wildcards | ⚠ **`COMPILE-ERR`** (see coverage-checker note) |

> **No workarounds.** These programs are written in their natural form, *not* bent
> around compiler bugs. As a result `09` currently fails to compile — it exercises a
> genuine open bug (documented below). Removing the contortions is deliberate: the
> panel should reflect what the compiler actually does.

## Notes / deliberately omitted corners

- **String interpolation desugars to a `display` call**, so `08` defines a local
  `Display` signature + `Int`/`Text` witnesses. Without a `Display` in scope,
  interpolation raises `Unknown name 'display'`.
- **`let*` / `let+`** (monadic/functor bind sugar) desugar through the standard library,
  so they aren't hermetically testable here; they do work now that Stdlib elaborates
  (see `ladies/examples/`).
- **Record type declarations** need each field on its own line (layout-sensitive); a
  single-line `{ X :: Int  Y :: Int }` does not parse.
- **Coverage-checker bug (makes `09` fail):** `merge` enumerates all four two-scrutinee
  cases explicitly. The compiler rejects the last one — `type error: Root.Nope,
  Root.Nope -> #2 is not useful` — a false positive: the multi-scrutinee usefulness
  check thinks the earlier `This`/`Nope` combinations already cover the whole space.
  (Collapsing the final cases into `otherwise` sidesteps it, but that's the workaround
  we removed.)
- **Fixed — bare nullary constructor before another record field.** A record-field
  pattern accepts binders, wildcards, literals, and *applied* constructors (`{ item:
  This n; … }`). A **bare nullary** constructor followed by another field —
  `{ colour: Red; alpha: a }` — used to crash the parser (`parser.rs:2090`): the
  constructor-application argument loop terminated on `}` but not `;`, so with no
  arguments to consume it ran into the `;` and panicked. Fixed by adding
  `TokenKind::Semicolon` to that loop's terminator set (`parse_constructor_pattern`),
  so `09` now uses the bare form directly — `paint`/`blend`/`theme_name` exercise a
  bare nullary constructor in the first, middle, and adjacent field positions, and
  `first_red_alpha` matches one inside a record nested under a `Cons`.
- **Inline patterns.** `swap` destructures its argument directly in the binder —
  `λ(a, b). (b, a)` — which is the natural way to demonstrate a tuple pattern (no
  `deconstruct` block, and not the `λp. (p.1, p.0)` projection workaround we removed).
  Note this sidesteps a *separate* open bug: writing it as a single-clause `deconstruct`
  on its own line immediately before another top-level declaration mis-parses (the
  declaration gets swallowed) — the same clause-attachment bug as
  `ladies/nested_deconstruct/`. The inline pattern is genuinely idiomatic, not a dodge.
- **Tuple parentheses are usually optional.** A tuple constructor needs no parens in
  expression position — `let t = 1, 2, 3` and a bare `b, a` result both parse. Parens
  are only needed for precedence, and a **tuple pattern in a lambda binder is one such
  case**: `λ(a, b). …` is required, since bare `λa, b. …` fails (`parse error: expected
  .` — the `,` collides with lambda-parameter syntax).
