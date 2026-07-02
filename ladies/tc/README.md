# Type-class test panel

A graduated set of self-contained ("hermetic") programs exercising the type-class
machinery (`signature` / `witness`), from the trivial to the known-broken. Each test
depends only on builtins (`print_endline`, `prim_show`, arithmetic/comparison, `Bool`
/`Int`/`Text`) plus what it defines itself — so a failure localizes to one mechanism
rather than to the stdlib.

Run one through the interpreter (fast, no Chez needed):

```
cargo run -q --bin lukas -- --library ladies/stdlib --source ladies/tc/03_monoid
```

Or run the whole panel: `./ladies/tc/run.sh`.

Each program prints a plain `##TC` sentinel and then its result value(s) via
`print_endline`; the runner carves those lines out of the (currently very chatty)
typer output. Note: string interpolation desugars to a `Display` (`display`) call, so
these hermetic tests avoid interpolation and print `prim_show`/method results directly.

| # | Test | Mechanism exercised | Expected | Status |
|---|------|---------------------|----------|--------|
| 01 | `01_dispatch` | single method, instance dispatched from an argument's type | `42` | ✅ ran |
| 02 | `02_two_instances` | selecting among several concrete witnesses (`Int` vs `Bool`) | `7` / `true` | ✅ ran |
| 03 | `03_monoid` | multi-method class; return-type-polymorphic `mempty` resolved by unification | `7` | ✅ ran |
| 04 | `04_constrained_fn` | a `Monoid α \|- ...` function: premise → dictionary parameter, threaded and discharged | `6` | ✅ ran |
| 05 | `05_derived_instance` | conditional instance `Eq α \|- Eq (List α)`; discharge the premise recursively | `true` / `false` | ✅ ran |
| 06 | `06_functor` | higher-kinded class over `* -> *`; method with its own `∀α β` | `60` | ✅ ran |
| 07 | `07_applicative` | constrained HKT helper `liftA2`; `pure`/`apply` with quantified methods | `7` | ✅ ran |
| 08 | `08_method_constraint` | **method itself constrained** (`mconcat :: ∀α. Monoid α \|- m α -> α`) | `6` | ✅ ran |
| 09 | `09_traversable` | `traverse` constrained by a *distinct* `Applicative f` — the hardest | `6` | ✅ ran |

Difficulty rises roughly monotonically: 01–03 are concrete dispatch, 04–05 add
premises on functions and instances, 06–07 add higher kinds, and 08–09 put constraints
on the class *methods* themselves — which is where the current machinery breaks.

## Current breakage map (interpreter path)

- **01–07 pass.** Concrete dispatch, return-type `mempty`, a dictionary-passing
  constrained *free* function, a higher-kinded `Functor`, a constrained higher-kinded
  helper (`liftA2` over `Applicative`), and — after the fixes below — **derived
  instances** including the recursive `Eq α |- Eq (List α)`.
- **08 and 09 still panic** (method-level constraints; see the last bullet).

### Fixed #1: evidence-slot off-by-one for witness premises

`resolve_constraints` (`src/typer.rs`) bound a non-ground constraint's evidence to de
Bruijn slot `#i` for non-self-referential trees, but `add_dictionary_parameter_slot`
always makes the tree self-referential (self at `#0`, dictionaries from `#1`). So a
witness whose body is a record put the evidence on the *self* slot — the dictionary
*builder* closure — and projecting a method off it gave `BadProjection { Ordinal(0) }`.
Fixed by binding evidence at `#(1+i)` unconditionally.

### Fixed #2: recursive derived instances (the `05` case)

`resolve_constraints` treated *all* non-ground constraints as dictionary parameters, but
only **variable-headed** ones (`Eq α` — no instance can match a bare variable) should be
parameters. **Constructor-headed** ones (`Eq (List α)`) are now discharged by their
instance instead (`Constraint::is_parametric` draws the line), with the instance's own
premises satisfied by those parameters — `WitnessEnvironment::resolve_witness` takes an
`assumptions` map for this. Two supporting details:

- The witness-vs-query unification direction was flipped so a resolved premise stays
  expressed in the *parameter's* type variable (otherwise the `assumptions` lookup
  missed).
- A constraint that resolves to the witness *currently being elaborated* refers to it
  through the self-reference slot `#0` (like ordinary recursion), not its global name —
  otherwise it became an undefined global self-dependency (`NoSuchSymbol`).

Both `derived_instance_discharges_premise` (non-recursive `Box`) and
`recursive_derived_instance` (`List`) pass in `tests/typeclass.rs`.

### Fixed #3: method-level constraints (the `08` case)

`mconcat :: ∀α. Monoid α |- m α -> α` is a *rank-2* field: its value must be a
polymorphic, dictionary-taking function, so the constraint has to be discharged
*inside the field*, not at the witness/builder level. Three changes:

- `check_record` no longer bubbles a constrained (rank-2) method field's constraints to
  the witness, and applies `subst` to the field's declared constraints (previously two
  un-unified `Monoid` metavariables).
- **Witness method bodies are lifted to top-level symbols** — mirroring how accessor
  selectors are emitted. `lift_constrained_witness_methods` turns
  `{ mconcat := λb. … }` into a top-level `<witness>$mconcat := λb. …` plus a witness
  record `{ mconcat := <witness>$mconcat }`. The lifted term rides the ordinary
  type + discharge path, so its `Monoid α` becomes a leading dictionary parameter.
- `add_dictionary_parameter_slot` now also slots the parameter into *non-ascribed*
  trees (inferred functions / lifted bodies), not just `Ascription`s.

`method_level_constraint_discharges` in `tests/typeclass.rs` passes.

### Fixed #4: Traversable / recursive methods (09)

`traverse` is method-constrained (`Applicative f`) *and* recursive, so it stressed three
more things, all now fixed:

1. **Dependency sort.** `in_resolvable_order` (Kahn's) filtered self-loops but not mutual
   cycles, so a recursive dictionary and its lifted method (which reference each other)
   — and everything downstream, like `start` — were dropped. It now breaks cycles by
   emitting a remaining node (non-witness first, so an eager witness record comes after
   the lifted method body it holds).

2. **Live, shared globals.** `Compiler::typecheck_and_initialize` snapshotted globals per
   symbol (`globals.clone()`), so a closure captured a *dead* snapshot and could not see
   a symbol defined later in a cycle (failing nondeterministically by hash order).
   `Globals` now wraps `Rc<RefCell<HashMap>>` and is shared live (`global()` returns an
   owned `Val`) — the todo "Make Env.globals … shared".

3. **Multi-dictionary order.** `ConstraintSet` is a `BTreeSet`, so a method's dictionaries
   are injected at call sites in class-name order, but an accessor selector's *body*
   projected the signature method from a fixed slot (signature dictionary first). When
   the signature class does not sort first (`Traversable` after `Applicative`) the
   dictionaries swapped. `elaborate_signature_method_selectors` now builds the body in
   the same sorted order, so it agrees with the injection. (`Mconcat/Monoid` and
   `Monoid/Foldable` already agreed, which is why 07/08 worked before this.)

`09` returns `6`; `tests/typeclass.rs::traversable_multi_dictionary_order` guards it.
