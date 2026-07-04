# Standard-library test panel

Each test `use Stdlib.` and exercises one standard-library feature. Run with
`./ladies/stdlib_tests/run.sh`.

## Current status: the whole library works

All ten features pass, deterministically (`use Stdlib.` elaborates and runs).

| # | Test | Feature | Expected | Status |
|---|------|---------|----------|--------|
| 01 | list_fold | `List.tabulate` / `map` / `fold_right` | `12` | ✅ |
| 02 | perhaps | `Perhaps.map` | `42` | ✅ |
| 03 | functor | `Functor` `fmap` (Perhaps) | `42` | ✅ |
| 04 | monad | `Monad` `bind` (Perhaps) | `42` | ✅ |
| 05 | applicative | `Applicative` `apply` (Perhaps) | `42` | ✅ |
| 06 | monoid | `Monoid` `mappend` (Text) | `abcd` | ✅ |
| 07 | foldable | `fold_map` (`Monoid m + Foldable t`) | `ab` | ✅ |
| 08 | state | `State` monad (`State.pure`/`eval`) | `7` | ✅ |
| 09 | interpolation | string interpolation via `Display` | `val is 42.` | ✅ |
| 10 | traversable | `traverse` (`Applicative f + Traversable t`) | `123` | ✅ |

## What was broken, and the fixes

Getting `use Stdlib.` working end-to-end took several fixes (all in the compiler except
the last):

1. **Stale self-reference (`Bound(0)`).** `bind_term(Bound(0))` *pushed* onto a shared
   `bound` stack that was never cleared between symbols, so every symbol's `#0`
   (recursion) resolved to the *first* self-referential constrained symbol elaborated.
   This is what made `Text.from_list` panic (`Text` vs `Char`). Fixed by resetting the
   self-reference slot per symbol (`TypingContext::reset_self_reference`).

2. **Nondeterminism.** Witness registration (`self.witnesses`), signature-method
   placeholders (`self.signatures`), and the dependency sort all iterated
   `HashSet`/`HashMap`s, so fresh-variable allocation — and therefore constraint
   resolution — varied run to run, crashing intermittently. All are now sorted
   deterministically.

3. **Multi-dictionary order** (`Traversable`/`sequence`) — see `ladies/tc/README.md`.

4. **`pure` declared in both `Applicative` and `Monad`** (a *library* issue): a method
   name shared by two signatures is ambiguous. Fixed in the library by removing `pure`
   from `signature Monad` and its witnesses (as in Haskell, `Monad` inherits `pure` from
   `Applicative`).
