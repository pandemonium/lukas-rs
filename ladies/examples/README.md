# Example gallery

A guided tour of Marmelade, one concept per folder, building up to combinations.
Each program is self-contained (except where it demonstrates the standard library),
prints a `##TC` sentinel followed by its results, and is verified to run.

Run one:

```
cargo run -q --bin lukas -- --library ladies/stdlib --source ladies/examples/09_pattern_matching
```

Or the whole gallery: `./ladies/examples/run.sh`.

## Core language

| # | Folder | Concept | Output |
|---|--------|---------|--------|
| 01 | `literals_and_operators` | Int/Text/Char/Bool literals, arithmetic, comparison, boolean ops, `if` | `10` / `yes` / `t` / … |
| 02 | `let_bindings` | `let … in`, nested lets, shadowing | `30` |
| 03 | `functions` | lambdas, currying, partial application | `42` / `42` |
| 04 | `higher_order_functions` | `id`, `compose`, `flip`, `const` | `42` / `2` / `5` |
| 05 | `recursion` | self-recursive definitions | `120` / `89` |
| 06 | `algebraic_data_types` | sum types, constructors, `deconstruct` | `300` / `12` / `0` |
| 07 | `records` | declaration, construction, projection, patterns | `25` / `7` |
| 08 | `tuples` | construction, ordinal projection, tuple patterns | `6` / `100` / `12` |
| 09 | `pattern_matching` | matching several scrutinees, `otherwise` | `42` / `nope` |
| 10 | `switch` | literal patterns with a catch-all | `two` / `many` |

## Types, modules, strings

| # | Folder | Concept | Output |
|---|--------|---------|--------|
| 11 | `polymorphism` | `∀`-quantified definitions used at several types | `3` / `2` |
| 12 | `type_ascription` | pinning a type with `::` | `66` / `3` |
| 13 | `higher_kinded_types` | a `* -> *` type constructor used generically | `41` |
| 14 | `modules` | `module M:` grouping and qualified access | `27` / `6` |
| 15 | `string_interpolation` | `` "`expr`" `` rendered via a `Display` instance | `Hello Ada, next year you will be 37.` |

## Type classes

| # | Folder | Concept | Output |
|---|--------|---------|--------|
| 16 | `type_classes` | `signature` (class) + `witness` (instance), dispatch on a type | `42` / `true` |
| 17 | `constrained_functions` | a `Monoid α \|- …` function threading a dictionary | `6` |
| 18 | `derived_instances` | a conditional instance `Eq α \|- Eq (List α)` | `true` / `false` |
| 19 | `functor` | a higher-kinded class over `* -> *` | `42` / `-` |
| 20 | `method_constraints` | a method that itself carries a constraint | `5` |

## Combinations

| # | Folder | Concept | Output |
|---|--------|---------|--------|
| 21 | `functor_applicative_monad` | the whole hierarchy on one type | `41` |
| 22 | `monoid_and_foldable` | fold a structure into a monoid (`fold_map`) | `6` |
| 23 | `traversable` | `traverse` under a *distinct* `Applicative` | `3` |
| 24 | `state_monad` | the standard-library `State` monad | `41` / `42` |
| 25 | `error_handling` | a `Result` type with custom errors and chaining | `42` / `error: divide by zero` |
| 26 | `expression_evaluator` | a tiny interpreter: recursive ADT + pattern matching | `30` |

## Notes on layout (learned building these)

The parser is layout-sensitive in a few ways worth knowing:

- A record **type** declaration's closing `}` must be on its own line, not on the
  last field's line.
- A record field whose value is a multi-line `deconstruct` can't be followed by
  another field — delegate such fields to a top-level helper (as the stdlib does).
- A single-clause `deconstruct` on its own line, immediately before another top-level
  declaration, mis-parses; put such a definition last, or bind its result in a `let`.
