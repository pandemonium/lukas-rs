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
| `multiline_application` | *Mostly a misunderstanding:* multi-line application works via the offside rule (head on its own line, args indented past it and aligned). Two real footguns remain: head left on the `:=` line with a wrapped arg **panics**; args at the *same* column as the head silently take the last one. | panic `src/main.rs:87` |

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
| `hkt_sum_extract` | *(FIXED — now a passing guard; see Fixed below)* | prints `41` |
| `hkt_sum_ok` | *(companion to `hkt_sum_extract` — the concrete-`f` contrast)* | prints `41` |

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
- **Concrete-witness method in a self-recursive function** (`recursive_witness_method/`,
  now a passing guard) — a self-recursive function (`foldExpr`, a `cata` over an `Expr`
  newtype) that calls a type-class method (`fmap`) resolved against a *concrete* global
  witness (`Functor (ExprF name a)`) crashed at run time with `ExpectedMatch`. In
  `resolve_constraints` the self-reference `#0` was bound with *all* the function's
  constraints, but only *parametric* (bare-variable-headed, e.g. `Functor f`) constraints
  become dictionary parameters; a resolvable constructor-headed one is discharged inline
  and takes no parameter. So the recursive call injected a phantom dictionary argument
  (`foldExpr <dict> alg`), shifting the value arguments and deconstructing the algebra
  closure against `MkExpr`. Fixed by binding the self-reference with only the parametric
  constraints. (Non-recursive uses, and the generic `cata` whose `Functor f` dictionary is
  a real parameter, always worked.)
- **Higher-kinded payload extraction** (`hkt_sum_extract/`, now a passing guard) — pulling
  an `f α` payload out of a sum type in a context polymorphic in the `* -> *` constructor
  `f` (e.g. `unwrap :: ∀f : *->* α. Wrap f α -> f α`, or `unfix`/`cata` over
  `Fix ::= ∀f : *->*. MkFix (f (Fix f))`) failed with `kind mismatch: cannot unify f with
  f α`. Root cause in `reduce_applied_constructor`: normalizing an applied type peels the
  arguments off the spine, but when the head is a *variable* (`f`) rather than a named
  constructor, the fallback returned just the head and **dropped the arguments**, so `f α`
  collapsed to `f`. The pattern binder then bound the payload at the truncated, mis-kinded
  type `f` instead of `f α`. Fixed by rebuilding the applied spine in that fallback. This
  is what unblocks `Fix`/`cata` and the whole recursion-schemes layer.
- **Cyclic substitution in multi-clause `deconstruct`** (`functor_partial_multi_ctor/`,
  now a passing guard) — elaborating a `Functor` witness for a *partially applied*,
  *multi-constructor* type (e.g. `Functor (Q a)` where `Q ::= ∀a r. MkQ1 a r | MkQ2 a r`)
  overflowed the stack in the typer. Each match clause normalizes the scrutinee to its
  own freshly-instantiated constructor spine; unifying those spines across clauses
  composed a substitution with a variable↔variable cycle (`$a ↦ $b`, `$b ↦ $a`) that the
  single-step occurs-check couldn't catch, and `Type::apply` chased it forever. Fixed by
  resolving variable chains iteratively to a canonical representative in `Type::apply`
  (the cycle is sound — the variables were unified, hence equal). `ExprF`
  (`ladies/examples/29_ExprF/`) is the real program that hit this.

## Design critiques

- [`module_critique.md`](module_critique.md) — how the module system actually works
  (name resolution + loading) and where the design falls short. `use_local_module`,
  `qualified_ctor_pattern`, and `brace_on_last_line` are its concrete symptoms.
