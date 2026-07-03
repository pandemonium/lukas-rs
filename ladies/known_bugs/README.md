# Known bugs — failing repros

A collection of minimal programs that currently **fail** (parse error, type error,
or run-time crash), each documenting a real open bug. Nothing here is expected to
pass yet; the point is to pin the bugs down with the smallest reproduction and the
exact error, so they're easy to pick up later.

Add new cases as their own folder with a `Root.lady` whose header comment states
**Expected** vs **Actual**, following the style of the existing ones.

Run one, or survey them all with `./ladies/known_bugs/run.sh`:

```
cargo run -q --bin lukas -- --library ladies/stdlib --source ladies/known_bugs/hkt_sum_extract
```

## Cases living here

### Parser / layout

| Folder | Bug | Error |
|--------|-----|-------|
| `prefix_operator` | Prefix-expression parser has no error path: negative literals `(-5)`, operator sections `(+ 1)`, trailing comma `(1, 2,)`. | panic `src/parser.rs:1426` |
| `double_forall_adt` | A type declaration accepts only one `∀`; a second forall in the body (`∀a. ∀b. …`) panics. | panic `src/parser.rs:858` |
| `qualified_ctor_pattern` | A qualified constructor in a *pattern* (`Root.Cons`, `M.Red`) crashes the pattern parser (also blocks matching a module's constructors). | panic `src/parser.rs:2090` |
| `brace_on_last_line` | A record *type*'s closing `}` must be on its own line; on the last field's line it fails. | `parse error: expected }` |
| `multiline_application` | An application split across lines silently corrupts the parse → runtime abort. | panic `src/main.rs:87` |

### Lexer / comments

| Folder | Bug | Error |
|--------|-----|-------|
| `nested_block_comment` | Block comments don't nest: `(* a (* b *) c *)`. The first `*)` closes it, leaving a dangling `*)`. | panic `src/lexer.rs:78` |
| `comment_between_decls` | A *multi-line* block comment *between* two top-level declarations (single-line, or at top-of-file, is fine). Newlines inside the comment emit spurious layout tokens. | panic `src/main.rs:87` |

### Names / modules

| Folder | Bug | Error |
|--------|-----|-------|
| `mutual_recursion` | Two top-level functions that call each other. Self-recursion and acyclic forward references work; a dependency *cycle* doesn't — the first def can't see the second. | `type error: undefined name Root.pong` |
| `use_local_module` | `use M.` on a module defined in the same file is resolved as a file import and fails; no way to open a local module unqualified. | `I/O error: No such file or directory` |

### Types / runtime

| Folder | Bug | Error |
|--------|-----|-------|
| `div_by_zero` | Integer division by zero aborts the host process instead of a controlled error (only known at run time, so it type-checks). | panic `src/builtin.rs:337` |
| `hkt_sum_extract` | Extracting a higher-kinded `f α` payload from a sum type through a function polymorphic in `f`. Declaring/constructing/inline-matching the type is fine; generalizing over the higher-kinded `f` is not (annotation doesn't help). | `kind mismatch: cannot unify f with f α` |
| `hkt_sum_ok` | *(not a bug — the passing boundary for `hkt_sum_extract`)* | prints `41` |

## Related failing cases living elsewhere

These already have homes in the repo; listed here so the full set is discoverable.

| Where | Bug | Error |
|-------|-----|-------|
| `ladies/nested_deconstruct/` | An *inline* nested `deconstruct` mis-parses — the outer `\| …` clause is wrongly attached to the inner match (clause-attachment / layout). | parse error |
| `ladies/lang/09_pattern_matching/` | Coverage checker false positive: enumerating all four two-scrutinee `This`/`Nope` cases rejects the last as *not useful*. | `type error: … -> #2 is not useful` |

See each program's header comment / the panel READMEs for the full write-up.

## Fixed

- **Recursive dictionary method** (`ladies/examples/22_monoid_and_foldable/`) — a ground
  `Foldable List` witness whose `fold_right` recurses through the class method crashed
  with `BadProjection … Ordinal(0)`. Fixed in `resolve_constraints`: a recursive
  dictionary is rewritten to the self-slot `#0` only when the tree actually has one; a
  ground witness (record body, no self-slot) keeps its global self-reference, resolved
  via the shared live globals.

## Design critiques

- [`module_critique.md`](module_critique.md) — how the module system actually works
  (name resolution + loading) and where the design falls short. `use_local_module`,
  `qualified_ctor_pattern`, and `brace_on_last_line` are its concrete symptoms.
