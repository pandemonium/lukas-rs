//! A behaviour-preserving `Expr<Types> -> Expr<Types>` optimiser that runs on the
//! native (C) pipeline between elaboration and closure conversion. See
//! `notes/simplifier.md` for the design.
//!
//! The whole pass hinges on one fact about the namer (`ast/namer.rs`): term ids use
//! De Bruijn **LEVELS**, not indices. `Bound(k)` names the binder at absolute depth
//! `k` counted from the root, so a variable and its binder carry the *same* number
//! regardless of where the sub-tree is spliced. That makes relocation a flat map
//! (`shift`) and beta-reduction a plain `let` with no index arithmetic.
//!
//! This first cut ships the always-safe local rewrites only:
//!   * beta-to-let                `(λp. body) arg`            -> `let p = arg in body`
//!   * case-of-known-constructor  `deconstruct (C a..) { .. }`-> the C clause's let-chain
//!   * tuple-deconstruct          `deconstruct (a, b) { .. }` -> a let-chain
//!   * projection-of-literal      `(a, b).0`                  -> `a`  (siblings must be values)
//!
//! The top-level inliner (the enabler that actually exposes these redexes on the
//! monadic byte path) is a follow-on; see the note.

use std::{
    cell::Cell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use crate::{
    ast::{
        Apply, Array, Binding, Deconstruct, Expr, IfThenElse, Injection, Interpolate, Lambda,
        Literal, ProductElement, Projection, Record, Segment, SelfReferential, Sequence, Tree,
        Tuple, TypeAscription,
        namer::{Identifier, QualifiedName, Symbol, TermSymbol},
        pattern::{ConstructorPattern, MatchClause, Pattern, StructPattern, TuplePattern},
    },
    lexer::BindingOperator,
    phase,
    typer::Types,
};

/// Largest term body (in AST nodes) the inliner will unfold. Combinators, method
/// selectors, constructor wrappers and dictionaries are all well under this.
///
/// Swept 2026-08-03 (`MARM_INLINE_BUDGET`, all benchmarks): 100 sits just above a SHARP
/// deforestation cliff and is load-bearing. binary_codec drops from 9115 to 7765 lines of
/// emitted C between budget 70 and 60 -- a single ~61-70-node monad-plumbing helper stops
/// being inlined, so the transformer construct/deconstruct pairs no longer cancel: 6.8s ->
/// 7.15s at 60, and 16.7s (2.5x!) at 50; utf8_get is 2.3x slower at 50. Above 70 the codec C
/// is byte-identical; raising the budget to 4000 changes NOTHING on any benchmark (the only
/// remaining un-inlined bodies are recursive, gated by the recursion guard, not by size). So
/// 100 = the knee + ~30 nodes of margin; there is no perf to win by tuning it either way.
const INLINE_BUDGET: usize = 100;
/// Whether the IO-deforestation reductions (single-use let-forwarding, case-of-case
/// commuting, saturated-constructor-application folding) are enabled. Default on; set
/// `MARM_NO_IODEFOREST` to disable, for A/B and regression bisection.
fn iodeforest_on() -> bool {
    std::env::var_os("MARM_NO_IODEFOREST").is_none()
}

/// Effective inline budget, overridable via `MARM_INLINE_BUDGET` for tuning sweeps.
fn inline_budget() -> usize {
    std::env::var("MARM_INLINE_BUDGET")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(INLINE_BUDGET)
}
/// Ceiling on inlines per term body, so an accidental miss in the acyclicity check
/// can only under-optimise, never loop.
const INLINE_FUEL: usize = 200_000;
/// Ceiling on inline/reduce rounds per term body (each round peels one layer of the
/// monad stack); the fixpoint normally converges well inside this.
const MAX_ROUNDS: usize = 24;

impl phase::SymbolTable<Types> {
    /// Simplify every term body in place. Types, foreign terms and all the
    /// bookkeeping tables are carried through untouched.
    pub fn simplify(self) -> Self {
        // Escape hatch for A/B measurement and bisecting a suspected miscompile.
        if std::env::var_os("MARM_NO_SIMPLIFY").is_some() {
            return self;
        }
        let Self {
            symbols,
            module_members,
            member_modules,
            imports,
            foreign_terms,
            signatures,
            witnesses,
            constructor_opacity,
            member_visibility,
        } = self;

        // Inlining exposes the monad-transformer redexes that the local rules then
        // collapse (dictionaries via projection-of-literal, `MkGet`/`MkState` boxes via
        // case-of-known-constructor, both unblocked by let-forwarding). We do NOT inline
        // into recursive bodies (see `build_inlinables`): inlining an effectful `bind`
        // into a loop welds the sequenced action into the recursion's closure, pinning
        // one iteration's data per turn -- a space leak. Guarded like this the pass is a
        // strict win on the codec benchmark: allocation −66%, wall ~1.5x, peak RSS below
        // baseline, output unchanged, whole C panel green. `MARM_NO_INLINE=1` keeps just
        // the local rules; `MARM_NO_SIMPLIFY=1` bypasses the pass entirely.
        let (inlinables, leaf_inlinables, recursive) =
            if std::env::var_os("MARM_NO_INLINE").is_some() {
                (Inlinables::default(), Inlinables::default(), HashSet::default())
            } else {
                build_inlinables(&symbols)
            };
        let dump = std::env::var("DUMP_SIMPLIFY").ok();

        // The recursion guard (don't inline into loops) is what keeps memory flat; the
        // 3.5x speedup on the codec comes entirely from fusing into the driver loop,
        // which is also the whole leak, so the two are inseparable by guarding.
        // `MARM_INLINE_LOOPS=1` drops the guard: faster, but peak RSS grows with the
        // loop's iteration count (batch-only; can OOM a long-running loop).
        let guard_loops = std::env::var_os("MARM_INLINE_LOOPS").is_none();

        let symbols = symbols
            .into_iter()
            .map(|(name, symbol)| {
                let symbol = match symbol {
                    Symbol::Term(term) => {
                        let TermSymbol {
                            name,
                            type_signature,
                            body,
                        } = term;
                        // A recursive body (a loop) is normally simplified WITHOUT inlining:
                        // fusing an effectful `bind` in welds the sequenced action into the
                        // recursion, which leaks (see `build_inlinables`). But the leak is
                        // exactly non-tail-recursion -- so we may keep the fused body whenever
                        // fusion left every self-call in tail position (`fusion_safe`). Try the
                        // fused body, keep it only if tail-safe, else fall back to the guarded
                        // body -- which still inlines the pure, leaf-only helpers (a monomorphic
                        // `<` -> `prim_lt` and friends) that can never weld an action into the
                        // recursion, just not the effectful combinators that cause the leak.
                        let body = if !guard_loops || !recursive.contains(&name) {
                            simplify_term(body, &inlinables)
                        } else {
                            let fused = simplify_term(body.clone(), &inlinables);
                            if fusion_safe(&fused) {
                                fused
                            } else {
                                simplify_term(body, &leaf_inlinables)
                            }
                        };
                        if dump.as_deref().is_some_and(|f| name.to_string().contains(f)) {
                            eprintln!("==== {} ====\n{}\n", name, body);
                        }
                        Symbol::Term(TermSymbol {
                            name,
                            type_signature,
                            body,
                        })
                    }
                    other => other,
                };
                (name, symbol)
            })
            .collect();

        Self {
            symbols,
            module_members,
            member_modules,
            imports,
            foreign_terms,
            signatures,
            witnesses,
            constructor_opacity,
            member_visibility,
        }
    }
}

/// Alternate inlining and local reduction to a fixpoint. Each round the inliner
/// unfolds one layer of head/base references (a `bind`, a dictionary projection, a
/// constructor wrapper) and the local rules then collapse whatever that exposed --
/// the construct/deconstruct pair, the beta redex, the case-of-known-constructor.
/// Peeling one layer per round is what walks the whole monad-transformer stack down.
fn simplify_term<A>(body: Expr<A, Identifier>, inlinables: &Inlinables<A>) -> Expr<A, Identifier>
where
    A: Clone,
{
    let mut current = simplify_expr(body);
    for _ in 0..MAX_ROUNDS {
        let inliner = Inliner {
            bodies: inlinables,
            fuel: Cell::new(INLINE_FUEL),
            changed: Cell::new(false),
        };
        let inlined = inliner.inline(&Rc::new(current), 0);
        current = simplify_expr(Rc::unwrap_or_clone(inlined));
        if !inliner.changed.get() {
            break;
        }
    }
    current
}

type Inlinables<A> = HashMap<QualifiedName, Tree<A, Identifier>>;

/// Collect the term bodies eligible to inline (small, within [`INLINE_BUDGET`], and
/// non-recursive so unfolding terminates), the *leaf-safe* subset of those (pure,
/// closure-free helpers safe to inline even into a non-tail loop), and the set of
/// *recursive* terms. All come from the same term-dependency graph. The recursive set is
/// the set of function bodies we must NOT freely inline *into*: a recursive body is a
/// loop, and inlining an effectful `bind` into a loop welds the sequenced action into the
/// recursion's closure -- the space leak. Keeping loops calling `bind` as an ordinary
/// worker leaves the action an argument that dies each turn, while the straight-line
/// callers still collapse fully. The leaf-safe subset is what a guarded loop *may* still
/// inline: those helpers contain no closure, so they cannot pin per-iteration data.
fn build_inlinables(
    symbols: &HashMap<crate::ast::namer::SymbolName, phase::Symbol<Types>>,
) -> (
    Inlinables<crate::typer::TypeInfo>,
    Inlinables<crate::typer::TypeInfo>,
    HashSet<QualifiedName>,
) {
    let terms: Vec<(&QualifiedName, &phase::Expr<Types>)> = symbols
        .values()
        .filter_map(|s| match s {
            Symbol::Term(term) => Some((&term.name, &term.body)),
            Symbol::Type(_) => None,
        })
        .collect();

    let names: HashSet<&QualifiedName> = terms.iter().map(|(name, _)| *name).collect();

    let dependencies: HashMap<QualifiedName, HashSet<QualifiedName>> = terms
        .iter()
        .map(|(name, body)| {
            let deps = body
                .free_variables()
                .into_iter()
                .filter(|q| names.contains(q))
                .cloned()
                .collect();
            ((*name).clone(), deps)
        })
        .collect();

    // A term is a "loop" we must not inline into if it reaches itself through the
    // Free-name dependency graph (mutual recursion) OR contains a self-referential
    // lambda whose self-binder it actually uses (direct recursion -- expressed as a
    // `Bound` self-reference, invisible to `free_variables`).
    let recursive: HashSet<QualifiedName> = terms
        .iter()
        .filter(|(name, body)| reaches_self(name, &dependencies) || contains_recursion(body))
        .map(|(name, _)| (*name).clone())
        .collect();

    let budget = inline_budget();
    let inlinable = |name: &QualifiedName, body: &phase::Expr<Types>| {
        // A nullary constructor's term is `Inject(C, [])` -- a shared, immutable value.
        // `free_variables` counts the constructor name (its tag), so the term looks
        // self-referential and lands in `recursive`; but unfolding it yields another
        // `Inject(C, [])` that references nothing, so it can never loop the inliner.
        // Inlining it is what lets a `deconstruct` whose scrutinee is such a singleton
        // (e.g. an `Ordering` flowing out of `compare` after case-of-`if` commuting)
        // see a known constructor and collapse. So keep it regardless of `recursive`.
        is_nullary_injection(body) || (within_budget(body, budget) && !recursive.contains(name))
    };
    let inlinables: Inlinables<_> = terms
        .iter()
        .filter(|(name, body)| inlinable(name, body))
        .map(|(name, body)| ((*name).clone(), Rc::new((*body).clone())))
        .collect();

    // The leaf-safe subset: inlinable helpers that are pure and closure-free (transitively),
    // so splicing one into a non-tail loop can never weld a per-iteration action into the
    // recursion (the leak). This is what the guarded-loop path is still allowed to inline.
    let leaf = leaf_safe_terms(&terms, &names);
    let leaf_inlinables = terms
        .iter()
        .filter(|(name, body)| leaf.contains(*name) && inlinable(name, body))
        .map(|(name, body)| ((*name).clone(), Rc::new((*body).clone())))
        .collect();

    (inlinables, leaf_inlinables, recursive)
}

/// The set of terms that are *leaf-safe*: their body, once its leading parameter lambdas
/// are peeled, contains no closure (`Lambda`/`RecursiveLambda`/`MakeClosure`), and every
/// term it references is itself leaf-safe. References to non-terms (builtin prims,
/// constructors that are not standalone terms) are leaves by construction. Such a helper
/// reduces to first-order code -- prims, constructors, `if`/`deconstruct` -- so inlining
/// it can never introduce a closure that pins per-iteration data across a non-tail
/// recursion. The monad combinators (`bind`/`fmap`/`pure`/`apply`/...) all carry a
/// continuation lambda and so are excluded -- exactly the ones whose fusion leaks.
fn leaf_safe_terms(
    terms: &[(&QualifiedName, &phase::Expr<Types>)],
    names: &HashSet<&QualifiedName>,
) -> HashSet<QualifiedName> {
    let bodies: HashMap<&QualifiedName, &phase::Expr<Types>> = terms.iter().copied().collect();
    // Start optimistic with every closure-free term, then drop any that reaches a
    // non-leaf term through its free variables until the set stops shrinking (a greatest
    // fixpoint -- mutual references among leaf helpers stay in).
    let mut leaf: HashSet<QualifiedName> = terms
        .iter()
        .filter(|(_, body)| is_closure_free(body))
        .map(|(name, _)| (*name).clone())
        .collect();
    loop {
        let doomed: Vec<QualifiedName> = leaf
            .iter()
            .filter(|name| {
                bodies[*name].free_variables().iter().any(|referenced| {
                    // A reference into `names` (another term) is only safe if that term is
                    // leaf too; a reference outside `names` is a prim/ctor -- always a leaf.
                    names.contains(referenced) && !leaf.contains(*referenced)
                })
            })
            .cloned()
            .collect();
        if doomed.is_empty() {
            break;
        }
        for name in doomed {
            leaf.remove(&name);
        }
    }
    leaf
}

/// Whether `body`, after its leading parameter lambdas (and any ascriptions) are peeled,
/// computes first-order once applied -- no closure former in the result. A dictionary is a
/// record, so a record is leaf iff every field is: this admits a witness like `Ord Int`
/// (`{ compare := λp q. if prim_lt … }`, method bodies closure-free) while excluding a
/// `Monad` witness (`{ bind := λk m. … k … }`, whose method carries a continuation lambda).
/// That is exactly the line between the dictionaries safe to fuse into a loop and the ones
/// whose fusion leaks.
fn is_closure_free<A>(body: &Expr<A, Identifier>) -> bool {
    match peel_binders(body) {
        Expr::Record(_, record) => record.fields.iter().all(|(_, v)| is_closure_free(v)),
        Expr::Tuple(_, tuple) => tuple.elements.iter().all(|e| is_closure_free(e)),
        other => has_no_closure(other),
    }
}

/// Strip the leading parameter lambdas and type ascriptions off a term body, exposing the
/// value/computation underneath (a record for a dictionary, an `if`/`deconstruct` for a
/// plain helper).
fn peel_binders<A>(body: &Expr<A, Identifier>) -> &Expr<A, Identifier> {
    let mut node = body;
    loop {
        match node {
            Expr::Lambda(_, lambda) => node = &lambda.body,
            Expr::RecursiveLambda(_, SelfReferential { lambda, .. }) => node = &lambda.body,
            Expr::Ascription(_, ascription) => node = &ascription.ascribed_tree,
            other => return other,
        }
    }
}

/// No `Lambda`/`RecursiveLambda`/`MakeClosure` anywhere in `expr`.
fn has_no_closure<A>(expr: &Expr<A, Identifier>) -> bool {
    match expr {
        Expr::Lambda(..) | Expr::RecursiveLambda(..) | Expr::MakeClosure(..) => false,
        other => children(other).into_iter().all(|c| has_no_closure(c)),
    }
}

/// Conservative structural equality on trees, ignoring annotations: `true` only when the
/// two are definitely the same value/expression. Unhandled shapes return `false` (a missed
/// merge, never an unsound one). Enough to spot the equal dead arms case-of-`if` leaves.
fn trees_equal<A>(a: &Expr<A, Identifier>, b: &Expr<A, Identifier>) -> bool {
    match (a, b) {
        (Expr::Constant(_, x), Expr::Constant(_, y)) => literal_eq(x, y),
        (Expr::Variable(_, x), Expr::Variable(_, y)) => x == y,
        (Expr::Inject(_, x), Expr::Inject(_, y)) => {
            x.constructor == y.constructor
                && x.arguments.len() == y.arguments.len()
                && x.arguments
                    .iter()
                    .zip(&y.arguments)
                    .all(|(p, q)| trees_equal(p, q))
        }
        (Expr::Apply(_, x), Expr::Apply(_, y)) => {
            trees_equal(&x.function, &y.function) && trees_equal(&x.argument, &y.argument)
        }
        (Expr::Tuple(_, x), Expr::Tuple(_, y)) => {
            x.elements.len() == y.elements.len()
                && x.elements
                    .iter()
                    .zip(&y.elements)
                    .all(|(p, q)| trees_equal(p, q))
        }
        _ => false,
    }
}

fn literal_eq(a: &Literal, b: &Literal) -> bool {
    match (a, b) {
        (Literal::Int(x), Literal::Int(y)) => x == y,
        (Literal::Float(x), Literal::Float(y)) => x == y,
        (Literal::Text(x), Literal::Text(y)) => x == y,
        (Literal::Bool(x), Literal::Bool(y)) => x == y,
        (Literal::Char(x), Literal::Char(y)) => x == y,
        (Literal::Unit, Literal::Unit) => true,
        _ => false,
    }
}

/// A term body that is a bare nullary constructor value, `Inject(C, [])` -- possibly
/// under type ascriptions, which the elaborator leaves on a constructor term and the
/// reducer strips on sight. Recognising it lets `build_inlinables` keep the singleton
/// even though `free_variables` counts its own constructor name as a (spurious) self-dep.
fn is_nullary_injection<A>(body: &Expr<A, Identifier>) -> bool {
    match body {
        Expr::Ascription(_, ascription) => is_nullary_injection(&ascription.ascribed_tree),
        Expr::Inject(_, Injection { arguments, .. }) => arguments.is_empty(),
        _ => false,
    }
}

/// Whether `expr` contains a self-referential lambda that actually uses its self-binder
/// -- i.e. a real loop. (An unused self-binder is not recursion; `derecursify` drops it.)
fn contains_recursion<A>(expr: &Expr<A, Identifier>) -> bool {
    match expr {
        Expr::RecursiveLambda(
            _,
            SelfReferential {
                own_name: Identifier::Bound(level),
                lambda,
            },
        ) if mentions_level(&lambda.body, *level) => true,
        _ => children(expr).into_iter().any(|c| contains_recursion(c)),
    }
}

/// Whether the *fused* body of a recursive term is safe to keep -- i.e. inlining did not
/// move the recursion out of tail position. The space leak that `build_inlinables`'s guard
/// exists to prevent is *exactly* non-tail recursion: fusing an effectful `bind` in turns
/// the self-call into the scrutinee of a `deconstruct` (forcing the sequenced action), which
/// clang can no longer sibling-call, so the piled-up frames each root one iteration's data.
/// A self-call that stays a tail call compiles to a clean constant-stack loop and cannot leak.
/// (Diagnosed on `binary_codec` (leaks) vs `utf8_get` (safe); see notes/loop-fusion-safety.md.)
///
/// Only direct (`RecursiveLambda`) recursion is judged safe; mutual recursion and any other
/// shape stay guarded. That is sound because `inlinables` never holds a recursive term, so
/// fusion can only splice *non-recursive* helpers into the body -- it relocates the term's own
/// `Bound` self-call but never introduces a fused call to another recursive term.
fn fusion_safe<A>(body: &Expr<A, Identifier>) -> bool {
    match body {
        Expr::RecursiveLambda(
            _,
            SelfReferential {
                own_name: Identifier::Bound(level),
                lambda,
            },
        ) => self_calls_all_tail(&lambda.body, *level, true, true),
        _ => false,
    }
}

/// Check that every self-reference (`Bound(level)` -- the absolute De Bruijn level of the
/// recursive term's own binder) occurs only as the head of an application in *tail position*.
/// `tail` tracks whether the current node is a tail context; `leading` tracks whether we are
/// still peeling the term's own parameter lambdas (its arity), the only lambdas whose body
/// stays a tail context. Tail-ness threads through leading lambdas, `if` branches, `deconstruct`
/// arms and `let` bodies only; every other position (scrutinees, let-RHS, arguments, inner
/// lambdas, tuples, ...) is conservatively non-tail, so a self-reference there fails the check.
fn self_calls_all_tail<A>(
    expr: &Expr<A, Identifier>,
    level: usize,
    tail: bool,
    leading: bool,
) -> bool {
    match expr {
        // A self-reference reached directly is NOT the head of a tail application (those are
        // consumed in the `Apply` arm below) -- so it is a leak-shaped occurrence.
        Expr::Variable(_, Identifier::Bound(k)) if *k == level => false,
        Expr::Variable(..)
        | Expr::Constant(..)
        | Expr::InvokeBridge(..)
        | Expr::MakeClosure(..) => true,

        Expr::RecursiveLambda(_, SelfReferential { lambda, .. }) => {
            self_calls_all_tail(&lambda.body, level, tail, leading)
        }
        Expr::Lambda(_, Lambda { body, .. }) => {
            // Leading lambdas are the term's arity, so their body inherits `tail`. An inner
            // lambda is a returned closure / deferred action, never a tail context here.
            if leading {
                self_calls_all_tail(body, level, tail, true)
            } else {
                self_calls_all_tail(body, level, false, false)
            }
        }

        Expr::Apply(_, Apply { function, argument }) => {
            if tail && spine_head_is_self(expr, level) {
                // A tail self-call: the head is the legitimate recursion; the arguments are
                // evaluated first, so they must be self-free (checked in non-tail position).
                spine_args_self_free(expr, level)
            } else {
                self_calls_all_tail(function, level, false, false)
                    && self_calls_all_tail(argument, level, false, false)
            }
        }

        Expr::If(
            _,
            IfThenElse {
                predicate,
                consequent,
                alternate,
            },
        ) => {
            self_calls_all_tail(predicate, level, false, false)
                && self_calls_all_tail(consequent, level, tail, false)
                && self_calls_all_tail(alternate, level, tail, false)
        }
        Expr::Deconstruct(
            _,
            Deconstruct {
                scrutinee,
                match_clauses,
            },
        ) => {
            self_calls_all_tail(scrutinee, level, false, false)
                && match_clauses
                    .iter()
                    .all(|c| self_calls_all_tail(&c.consequent, level, tail, false))
        }
        Expr::Let(_, Binding { bound, body, .. }) => {
            self_calls_all_tail(bound, level, false, false)
                && self_calls_all_tail(body, level, tail, false)
        }

        // Every other node has no tail sub-position, so any self-reference inside is
        // (conservatively) leak-shaped -- walk the children in non-tail position.
        _ => children(expr)
            .into_iter()
            .all(|c| self_calls_all_tail(c, level, false, false)),
    }
}

/// Whether the head of an application spine `((f a) b) c` is the self-reference `Bound(level)`.
fn spine_head_is_self<A>(expr: &Expr<A, Identifier>, level: usize) -> bool {
    match expr {
        Expr::Apply(_, Apply { function, .. }) => spine_head_is_self(function, level),
        Expr::Variable(_, Identifier::Bound(k)) => *k == level,
        _ => false,
    }
}

/// Whether the *arguments* of a self-call spine `((self a) b) c` are free of self-references
/// (the head itself is the recursion and is ignored). Each argument is checked non-tail.
fn spine_args_self_free<A>(expr: &Expr<A, Identifier>, level: usize) -> bool {
    match expr {
        Expr::Apply(_, Apply { function, argument }) => {
            self_calls_all_tail(argument, level, false, false)
                && spine_args_self_free(function, level)
        }
        _ => true,
    }
}

/// Whether `start` can reach itself through `dependencies` (direct self-reference or
/// any cycle) -- i.e. inlining it could fail to terminate.
fn reaches_self(
    start: &QualifiedName,
    dependencies: &HashMap<QualifiedName, HashSet<QualifiedName>>,
) -> bool {
    let mut seen = HashSet::new();
    let mut stack: Vec<&QualifiedName> = dependencies
        .get(start)
        .into_iter()
        .flat_map(|deps| deps.iter())
        .collect();

    while let Some(name) = stack.pop() {
        if name == start {
            return true;
        }
        if seen.insert(name) {
            if let Some(deps) = dependencies.get(name) {
                stack.extend(deps.iter());
            }
        }
    }
    false
}

fn within_budget<A>(expr: &Expr<A, Identifier>, budget: usize) -> bool {
    fn go<A>(expr: &Expr<A, Identifier>, budget: usize, count: &mut usize) -> bool {
        *count += 1;
        *count <= budget && children(expr).into_iter().all(|c| go(c, budget, count))
    }
    let mut count = 0;
    go(expr, budget, &mut count)
}

/// Guard for case-of-`if` commuting: the whole match is duplicated into both branches,
/// so only commute when the clauses are small enough that the copy is cheap. Bounds the
/// duplicated size to `MAX_CLAUSES * PER_CLAUSE_BUDGET` nodes -- comfortably fits the
/// `compare`-shaped matches (a couple of clauses returning `true`/`false`) this exists
/// for, while refusing to fan a large match body out across an `if`.
fn clauses_are_small<A>(clauses: &[MatchClause<A, Identifier>]) -> bool {
    const MAX_CLAUSES: usize = 4;
    const PER_CLAUSE_BUDGET: usize = 8;
    clauses.len() <= MAX_CLAUSES
        && clauses
            .iter()
            .all(|clause| within_budget(&clause.consequent, PER_CLAUSE_BUDGET))
}

/// The immediate sub-trees of a node, in evaluation order. Used by size measurement
/// (and any other structural fold that does not care which slot a child sits in).
pub(crate) fn children<A>(expr: &Expr<A, Identifier>) -> Vec<&Tree<A, Identifier>> {
    match expr {
        Expr::Variable(..)
        | Expr::InvokeBridge(..)
        | Expr::Constant(..)
        | Expr::MakeClosure(..) => {
            vec![]
        }
        Expr::RecursiveLambda(_, SelfReferential { lambda, .. }) => vec![&lambda.body],
        Expr::Lambda(_, Lambda { body, .. }) => vec![body],
        Expr::Apply(_, Apply { function, argument }) => vec![function, argument],
        Expr::Let(_, Binding { bound, body, .. }) => vec![bound, body],
        Expr::Tuple(_, Tuple { elements }) => elements.iter().collect(),
        Expr::Record(_, Record { fields }) => fields.iter().map(|(_, v)| v).collect(),
        Expr::Inject(_, Injection { arguments, .. }) => arguments.iter().collect(),
        Expr::Array(_, Array { elements }) => elements.iter().collect(),
        Expr::Project(_, Projection { base, .. }) => vec![base],
        Expr::Sequence(_, Sequence { this, and_then }) => vec![this, and_then],
        Expr::Deconstruct(
            _,
            Deconstruct {
                scrutinee,
                match_clauses,
            },
        ) => {
            let mut cs = vec![scrutinee];
            cs.extend(match_clauses.iter().map(|clause| &clause.consequent));
            cs
        }
        Expr::If(
            _,
            IfThenElse {
                predicate,
                consequent,
                alternate,
            },
        ) => {
            vec![predicate, consequent, alternate]
        }
        Expr::Interpolate(_, Interpolate(segments)) => segments
            .iter()
            .filter_map(|s| match s {
                Segment::Expression(e) => Some(e),
                Segment::Literal(..) => None,
            })
            .collect(),
        Expr::Ascription(_, TypeAscription { ascribed_tree, .. }) => vec![ascribed_tree],
    }
}

/// Context-driven, one-layer-per-pass inliner. It only unfolds a `Free` reference
/// when it sits in a position where a reduction will follow -- the **head** of an
/// application (so beta can fire) or the **base** of a projection (so
/// projection-of-literal can fire). Crucially it does *not* inline a dictionary that
/// appears in argument position: there it must stay a `Free` atom so beta-substitution
/// can carry it into the selector body, where it then meets the projection and gets
/// inlined as a record. Because inlined bodies are closed, relocating one to depth
/// `d` is a uniform `shift(_, 0, d)`.
struct Inliner<'a, A> {
    bodies: &'a Inlinables<A>,
    fuel: Cell<usize>,
    changed: Cell<bool>,
}

impl<A> Inliner<'_, A>
where
    A: Clone,
{
    /// If `tree` is an inlinable `Free`, return its body relocated to `depth`.
    fn try_head(&self, tree: &Tree<A, Identifier>, depth: usize) -> Option<Tree<A, Identifier>> {
        let Expr::Variable(_, Identifier::Free(name)) = &**tree else {
            return None;
        };
        let body = self.bodies.get(name)?;
        if self.fuel.get() == 0 {
            return None;
        }
        self.fuel.set(self.fuel.get() - 1);
        self.changed.set(true);
        Some(Rc::new(shift(body, 0, depth)))
    }

    /// Inline `tree` at absolute binder depth `depth` (the number of enclosing
    /// binders; equivalently the level the next binder would receive).
    fn inline(&self, tree: &Tree<A, Identifier>, depth: usize) -> Tree<A, Identifier> {
        let go = |t: &Tree<A, Identifier>, d: usize| self.inline(t, d);

        let rebuilt = match &**tree {
            // Head position: try to inline the callee, else recurse into it.
            Expr::Apply(a, Apply { function, argument }) => Expr::Apply(
                a.clone(),
                Apply {
                    function: self
                        .try_head(function, depth)
                        .unwrap_or_else(|| go(function, depth)),
                    argument: go(argument, depth),
                },
            ),

            // Base position: try to inline the record, else recurse into it.
            Expr::Project(a, Projection { base, select }) => Expr::Project(
                a.clone(),
                Projection {
                    base: self
                        .try_head(base, depth)
                        .unwrap_or_else(|| go(base, depth)),
                    select: select.clone(),
                },
            ),

            Expr::Lambda(a, Lambda { parameter, body }) => Expr::Lambda(
                a.clone(),
                Lambda {
                    parameter: parameter.clone(),
                    body: go(body, depth + 1),
                },
            ),

            Expr::RecursiveLambda(a, SelfReferential { own_name, lambda }) => {
                Expr::RecursiveLambda(
                    a.clone(),
                    SelfReferential {
                        own_name: own_name.clone(),
                        lambda: Lambda {
                            parameter: lambda.parameter.clone(),
                            // own_name binds at `depth`, the parameter at `depth + 1`.
                            body: go(&lambda.body, depth + 2),
                        },
                    },
                )
            }

            Expr::Let(
                a,
                Binding {
                    binder,
                    operator,
                    bound,
                    body,
                },
            ) => Expr::Let(
                a.clone(),
                Binding {
                    binder: binder.clone(),
                    operator: *operator,
                    bound: go(bound, depth),
                    body: go(body, depth + 1),
                },
            ),

            // Scrutinee position: like head/base, it is an elimination site -- a
            // known constructor here lets case-of-known-constructor fire and cancel
            // the box (this is what collapses the `MkGet`/State machinery).
            Expr::Deconstruct(
                a,
                Deconstruct {
                    scrutinee,
                    match_clauses,
                },
            ) => Expr::Deconstruct(
                a.clone(),
                Deconstruct {
                    scrutinee: self
                        .try_head(scrutinee, depth)
                        .unwrap_or_else(|| go(scrutinee, depth)),
                    match_clauses: match_clauses
                        .iter()
                        .map(|clause| MatchClause {
                            pattern: clause.pattern.clone(),
                            consequent: go(
                                &clause.consequent,
                                depth + pattern_binder_count(&clause.pattern),
                            ),
                        })
                        .collect(),
                },
            ),

            Expr::Tuple(a, Tuple { elements }) => Expr::Tuple(
                a.clone(),
                Tuple {
                    elements: elements.iter().map(|e| go(e, depth)).collect(),
                },
            ),

            Expr::Record(a, Record { fields }) => Expr::Record(
                a.clone(),
                Record {
                    fields: fields
                        .iter()
                        .map(|(k, v)| (k.clone(), go(v, depth)))
                        .collect(),
                },
            ),

            Expr::Inject(
                a,
                Injection {
                    constructor,
                    arguments,
                },
            ) => Expr::Inject(
                a.clone(),
                Injection {
                    constructor: constructor.clone(),
                    arguments: arguments.iter().map(|e| go(e, depth)).collect(),
                },
            ),

            Expr::Array(a, Array { elements }) => Expr::Array(
                a.clone(),
                Array {
                    elements: elements.iter().map(|e| go(e, depth)).collect(),
                },
            ),

            Expr::Sequence(a, Sequence { this, and_then }) => Expr::Sequence(
                a.clone(),
                Sequence {
                    this: go(this, depth),
                    and_then: go(and_then, depth),
                },
            ),

            Expr::If(
                a,
                IfThenElse {
                    predicate,
                    consequent,
                    alternate,
                },
            ) => Expr::If(
                a.clone(),
                IfThenElse {
                    predicate: go(predicate, depth),
                    consequent: go(consequent, depth),
                    alternate: go(alternate, depth),
                },
            ),

            Expr::Interpolate(a, Interpolate(segments)) => Expr::Interpolate(
                a.clone(),
                Interpolate(
                    segments
                        .iter()
                        .map(|s| match s {
                            Segment::Literal(sa, l) => Segment::Literal(sa.clone(), l.clone()),
                            Segment::Expression(e) => Segment::Expression(go(e, depth)),
                        })
                        .collect(),
                ),
            ),

            Expr::Ascription(
                a,
                TypeAscription {
                    ascribed_tree,
                    type_signature,
                },
            ) => Expr::Ascription(
                a.clone(),
                TypeAscription {
                    ascribed_tree: go(ascribed_tree, depth),
                    type_signature: type_signature.clone(),
                },
            ),

            leaf @ (Expr::Variable(..)
            | Expr::InvokeBridge(..)
            | Expr::Constant(..)
            | Expr::MakeClosure(..)) => leaf.clone(),
        };

        Rc::new(rebuilt)
    }
}

/// Number of variables a pattern binds -- one per `Bind` leaf, counted in the DFS
/// order the namer walks, since each pushes exactly one binder onto the level stack.
fn pattern_binder_count<A>(pattern: &Pattern<A, Identifier>) -> usize {
    match pattern {
        Pattern::Bind(..) => 1,
        Pattern::Literally(..) => 0,
        Pattern::Coproduct(_, ConstructorPattern { arguments, .. }) => {
            arguments.iter().map(pattern_binder_count).sum()
        }
        Pattern::Tuple(_, TuplePattern { elements }) => {
            elements.iter().map(pattern_binder_count).sum()
        }
        Pattern::Struct(_, StructPattern { fields }) => {
            fields.iter().map(|(_, p)| pattern_binder_count(p)).sum()
        }
    }
}

/// The lowest De Bruijn level a pattern binds (`None` if it binds nothing). A pattern's
/// binders occupy a contiguous `[base, base + pattern_binder_count)` range starting at the
/// scrutinee's depth, so this `base` is exactly the `shift` threshold when relocating other
/// clauses underneath these binders (see the case-of-case rule).
fn pattern_min_level<A>(pattern: &Pattern<A, Identifier>) -> Option<usize> {
    match pattern {
        Pattern::Bind(_, Identifier::Bound(level)) => Some(*level),
        Pattern::Bind(..) | Pattern::Literally(..) => None,
        Pattern::Coproduct(_, ConstructorPattern { arguments, .. }) => {
            arguments.iter().filter_map(pattern_min_level).min()
        }
        Pattern::Tuple(_, TuplePattern { elements }) => {
            elements.iter().filter_map(pattern_min_level).min()
        }
        Pattern::Struct(_, StructPattern { fields }) => {
            fields.iter().filter_map(|(_, p)| pattern_min_level(p)).min()
        }
    }
}

/// Relocate a clause list underneath `by` freshly interposed binders starting at `from`:
/// each clause's own binders (levels `>= from`) and references to them shift up by `by`;
/// references to enclosing binders (`< from`) are untouched. Used by case-of-case commuting
/// to move the outer match into an inner arm, under that arm's pattern binders.
fn shift_clauses<A>(
    clauses: &[MatchClause<A, Identifier>],
    from: usize,
    by: usize,
) -> Vec<MatchClause<A, Identifier>>
where
    A: Clone,
{
    clauses
        .iter()
        .map(|clause| MatchClause {
            pattern: walk_pattern(&clause.pattern, &|id| shift_id(id, from, by)),
            consequent: Rc::new(shift(&clause.consequent, from, by)),
        })
        .collect()
}

/// Rewrite to a fixpoint. Each sweep is `Expr::map` bottom-up (so a node's children
/// are already reduced when it is visited); we repeat whole sweeps until one changes
/// nothing, because a rule like let-forwarding can splice fresh redexes *deep* inside
/// its result that a single bottom-up pass has already walked past.
fn simplify_expr<A>(mut expr: Expr<A, Identifier>) -> Expr<A, Identifier>
where
    A: Clone,
{
    for _ in 0..SIMPLIFY_CAP {
        let changed = Cell::new(false);
        expr = expr.map(&mut |node| reduce_to_fixpoint(node, &changed));
        if !changed.get() {
            break;
        }
    }
    expr
}

/// Ceiling on whole-tree reduction sweeps; the fixpoint converges well inside this.
const SIMPLIFY_CAP: usize = 200;

fn reduce_to_fixpoint<A>(mut expr: Expr<A, Identifier>, changed: &Cell<bool>) -> Expr<A, Identifier>
where
    A: Clone,
{
    loop {
        match reduce_once(expr) {
            (true, reduced) => {
                changed.set(true);
                expr = reduced;
            }
            (false, stable) => return stable,
        }
    }
}

/// One local rewrite step. Returns `(fired, expr)`; `expr` is the rewritten node
/// when `fired`, otherwise the original node handed back unchanged.
fn reduce_once<A>(expr: Expr<A, Identifier>) -> (bool, Expr<A, Identifier>)
where
    A: Clone,
{
    match expr {
        // Strip type ascriptions: every backend compiles straight through them
        // (`compile_expr(ascribed_tree)`), and the type is already on the node
        // annotation. Removing them uncovers the lambda / constructor an ascription
        // wraps, which is what every elimination rule below needs to see.
        Expr::Ascription(_, ascription) => (true, Rc::unwrap_or_clone(ascription.ascribed_tree)),

        // derecursify: every top-level combinator is elaborated as a self-referential
        // lambda (`#L := λ…`), but the ones we inline never use their self-binder. Drop
        // it so the plain-lambda beta rules can fire. The self binder sits at level `L`
        // (its own depth) with the parameter at `L+1`; removing it slides everything
        // above `L` down by one, so the parameter lands at `L` -- a normal lambda.
        Expr::RecursiveLambda(a, SelfReferential { own_name, lambda }) if matches!(&own_name, Identifier::Bound(l) if !mentions_level(&lambda.body, *l)) =>
        {
            let Identifier::Bound(l) = own_name else {
                unreachable!("guarded by the match arm")
            };
            let body = walk(
                &lambda.body,
                &|va: &A, id: &Identifier| Expr::Variable(va.clone(), decrement_above(id, l)),
                &|id: &Identifier| decrement_above(id, l),
            );
            (
                true,
                Expr::Lambda(
                    a,
                    Lambda {
                        parameter: decrement_above(&lambda.parameter, l),
                        body: Rc::new(body),
                    },
                ),
            )
        }

        Expr::Apply(a, apply) if matches!(&*apply.function, Expr::Lambda(..)) => {
            let Apply { function, argument } = apply;
            let Expr::Lambda(_, Lambda { parameter, body }) = Rc::unwrap_or_clone(function) else {
                unreachable!("guarded by the match arm")
            };
            match &parameter {
                // beta-substitute a closed atom: keep the spine as lambdas so a
                // curried application (`bind dict k action`) can keep reducing, and
                // -- crucially -- expose the dictionary as a literal at its use sites
                // so projection can fire. Safe because an atom is an inert value:
                // dropping or duplicating it changes nothing.
                Identifier::Bound(level) if is_closed_atom(&argument) => {
                    (true, substitute_atom(&body, *level, &argument))
                }
                // beta-to-let: otherwise bind strictly. Levels make the binder line
                // up with itself, so no substitution is needed.
                _ => (
                    true,
                    Expr::Let(
                        a,
                        Binding {
                            binder: parameter,
                            operator: BindingOperator::Identity,
                            bound: argument,
                            body,
                        },
                    ),
                ),
            }
        }

        // let-float: a `let` sitting in head / base / scrutinee position blocks the
        // rule that wants a lambda / tuple / injection there. Float it outward so the
        // real redex surfaces: `C[let x=v in b] -> let x=v in C'[b]`. Sibling parts of
        // the context (the application argument, the match clauses) move under the
        // let's binder, so they shift up by one from that binder's level. The binder
        // level equals the let's own depth, an invariant every rule here preserves.
        // Always safe -- strict evaluation order is unchanged (`v` still runs first).
        Expr::Apply(a, apply) if is_floatable_let(&apply.function) => {
            let Apply { function, argument } = apply;
            let (la, binding, level) = open_let(function);
            let floated = Expr::Apply(
                a,
                Apply {
                    function: binding.body,
                    argument: Rc::new(shift(&argument, level, 1)),
                },
            );
            (
                true,
                rewrap_let(la, binding.binder, binding.operator, binding.bound, floated),
            )
        }

        Expr::Project(a, projection) if is_floatable_let(&projection.base) => {
            let Projection { base, select } = projection;
            let (la, binding, _level) = open_let(base);
            let floated = Expr::Project(
                a,
                Projection {
                    base: binding.body,
                    select,
                },
            );
            (
                true,
                rewrap_let(la, binding.binder, binding.operator, binding.bound, floated),
            )
        }

        Expr::Deconstruct(a, deconstruct) if is_floatable_let(&deconstruct.scrutinee) => {
            let Deconstruct {
                scrutinee,
                match_clauses,
            } = deconstruct;
            let (la, binding, level) = open_let(scrutinee);
            let floated = Expr::Deconstruct(
                a,
                Deconstruct {
                    scrutinee: binding.body,
                    match_clauses: match_clauses
                        .into_iter()
                        .map(|clause| MatchClause {
                            pattern: walk_pattern(&clause.pattern, &|id| shift_id(id, level, 1)),
                            consequent: Rc::new(shift(&clause.consequent, level, 1)),
                        })
                        .collect(),
                },
            );
            (
                true,
                rewrap_let(la, binding.binder, binding.operator, binding.bound, floated),
            )
        }

        // let-forwarding: substitute a value-bound `let` into its uses when every use
        // is an *elimination* (projection base / apply head / deconstruct scrutinee).
        // That is what finally lets a forwarded dictionary meet its projection and a
        // forwarded `MkGet`/`MkState` payload meet its deconstruct, so the box cancels.
        //   * value-bound -> duplicating / dropping it is effect- and termination-neutral
        //     (and it de-sugars to no allocation once it cancels);
        //   * OR forwardable-effectfully -> the bound expression's single use is the FIRST
        //     thing the body evaluates (`forwardable_effectfully`), so a possibly-effectful,
        //     non-value bound may be forwarded without reordering effects. This is what lets
        //     the `let x = ARG in deconstruct x …` that `unsafe_run_IO`'s beta-to-let leaves
        //     behind forward `ARG` into the force, exposing the inner (newtype-unwrap)
        //     deconstruct to case-of-case -- while NOT touching `let x = E in let y = F in … x`
        //     (which would flip effect order).
        //   * all-uses-eliminated (the value case) -> every use is a scrutinee / head / base,
        //     so we never turn a shared allocation into a per-use one.
        // Zero uses is the degenerate case: a dead pure `let`, simply dropped.
        Expr::Let(_a, binding)
            if matches!(&binding.binder, Identifier::Bound(l)
                if (is_value(&binding.bound) && all_uses_eliminated(&binding.body, *l))
                    || (iodeforest_on() && forwardable_effectfully(&binding.body, *l))) =>
        {
            let Identifier::Bound(level) = binding.binder else {
                unreachable!("guarded by the match arm")
            };
            (true, substitute_value(&binding.body, level, &binding.bound))
        }

        Expr::Project(a, projection) => match project_literal(&a, &projection) {
            Some(reduced) => (true, reduced),
            None => (false, Expr::Project(a, projection)),
        },

        // `if p then e else e` -> `e`: both arms agree, so the (pure) test is dead. This
        // fires after case-of-`if` commuting + case-of-known-constructor reduce a `compare`
        // chain: e.g. `a < b` becomes `if prim_lt a b then true else (if prim_eq a b then
        // false else false)`, and this collapses the inner `if prim_eq …` to `false`,
        // dropping the now-useless `prim_eq` (a real `val_eq` call) from the hot path.
        // Conditions are pure Bool expressions here, so discarding `p` is sound.
        Expr::If(_, ref ite) if trees_equal(&ite.consequent, &ite.alternate) => {
            let Expr::If(_, ite) = expr else {
                unreachable!("guarded by the match arm")
            };
            (true, Rc::unwrap_or_clone(ite.consequent))
        }

        // case-of-`if` commuting: `deconstruct (if p then t else e) into cs` becomes
        // `if p then (deconstruct t into cs) else (deconstruct e into cs)`. This pushes
        // the match down onto each branch, where -- once `t`/`e` are known constructors
        // (the `compare` witnesses expand to `if prim_lt … then Less else …`) -- the
        // case-of-known-constructor arm below fires and the `Ordering` is never built.
        // An `if` binds nothing, so both branches sit at the scrutinee's depth: with De
        // Bruijn levels the clauses move in verbatim, no shifting. Terminating: the rule
        // only moves the deconstruct strictly toward the leaves of the `if`-tree (a
        // constructor leaf then reduces, any other leaf leaves an irreducible match).
        // Guarded to small clauses since they are duplicated into both branches.
        Expr::Deconstruct(a, deconstruct)
            if matches!(&*deconstruct.scrutinee, Expr::If(..))
                && clauses_are_small(&deconstruct.match_clauses) =>
        {
            let Deconstruct {
                scrutinee,
                match_clauses,
            } = deconstruct;
            let Expr::If(
                _,
                IfThenElse {
                    predicate,
                    consequent,
                    alternate,
                },
            ) = Rc::unwrap_or_clone(scrutinee)
            else {
                unreachable!("guarded by the match arm")
            };
            let on_branch = |branch: Tree<A, Identifier>, clauses| {
                Rc::new(Expr::Deconstruct(
                    a.clone(),
                    Deconstruct {
                        scrutinee: branch,
                        match_clauses: clauses,
                    },
                ))
            };
            (
                true,
                Expr::If(
                    a.clone(),
                    IfThenElse {
                        predicate,
                        consequent: on_branch(consequent, match_clauses.clone()),
                        alternate: on_branch(alternate, match_clauses),
                    },
                ),
            )
        }

        // case-of-case commuting: `deconstruct (deconstruct s into [Pᵢ -> bᵢ]) into cs`
        // becomes `deconstruct s into [Pᵢ -> (deconstruct bᵢ into cs)]`, pushing the outer
        // match down onto each inner arm. This is the analog of case-of-`if` commuting for a
        // `deconstruct` scrutinee -- the shape a run marker `deconstruct M into Suspend v ->
        // v()` hits when `M` is a newtype unwrap `deconstruct set into Mutable arr -> Suspend
        // (λ_. raw …)`: the outer force cannot meet the `Suspend` until it floats through the
        // unwrap, after which case-of-known-constructor cancels the box and the `Suspend`
        // closure vanishes. Pure structural commute of matches already present -- it inlines
        // no combinator into any loop, so it cannot introduce the non-tail fusion leak.
        //
        // Unlike case-of-`if` (an `if` binds nothing), an inner arm `Pᵢ` binds `nᵢ` variables,
        // so the outer clauses -- duplicated into that arm -- move under those binders and must
        // shift up by `nᵢ` (from the inner binders' base level). Guarded to small outer clauses
        // (copied into every arm) and terminating: the outer match only moves strictly toward
        // the leaves of the inner match tree.
        Expr::Deconstruct(a, deconstruct)
            if iodeforest_on()
                && matches!(&*deconstruct.scrutinee, Expr::Deconstruct(..))
                && clauses_are_small(&deconstruct.match_clauses) =>
        {
            let Deconstruct {
                scrutinee,
                match_clauses: outer,
            } = deconstruct;
            let Expr::Deconstruct(
                inner_a,
                Deconstruct {
                    scrutinee: inner_scrutinee,
                    match_clauses: inner,
                },
            ) = Rc::unwrap_or_clone(scrutinee)
            else {
                unreachable!("guarded by the match arm")
            };
            let commuted = inner
                .into_iter()
                .map(|clause| {
                    let n = pattern_binder_count(&clause.pattern);
                    let outer = if n == 0 {
                        outer.clone()
                    } else {
                        let base = pattern_min_level(&clause.pattern)
                            .expect("a clause binding n > 0 variables has a bound binder");
                        shift_clauses(&outer, base, n)
                    };
                    MatchClause {
                        pattern: clause.pattern,
                        consequent: Rc::new(Expr::Deconstruct(
                            a.clone(),
                            Deconstruct {
                                scrutinee: clause.consequent,
                                match_clauses: outer,
                            },
                        )),
                    }
                })
                .collect();
            (
                true,
                Expr::Deconstruct(
                    inner_a,
                    Deconstruct {
                        scrutinee: inner_scrutinee,
                        match_clauses: commuted,
                    },
                ),
            )
        }

        Expr::Deconstruct(a, deconstruct) => match deconstruct_literal(&a, &deconstruct) {
            Some(reduced) => (true, reduced),
            None => (false, Expr::Deconstruct(a, deconstruct)),
        },

        other => (false, other),
    }
}

/// Substitute a **value** `value` for the binder at level `level` in `body`, dropping
/// the binder. Unlike [`substitute_atom`], `value` may have its own binders, so at each
/// use it is relocated to that use's depth; the traversal tracks depth for exactly this.
/// A use at depth `d` lands (after the binder is removed) at depth `d - 1`, so the value
/// -- which lives at `level` -- shifts up by `d - 1 - level`.
fn substitute_value<A>(
    body: &Tree<A, Identifier>,
    level: usize,
    value: &Tree<A, Identifier>,
) -> Expr<A, Identifier>
where
    A: Clone,
{
    let on_var = |depth: usize, a: &A, id: &Identifier| match id {
        Identifier::Bound(k) if *k == level => shift(value, level, depth - 1 - level),
        other => Expr::Variable(a.clone(), decrement_above(other, level)),
    };
    let on_binder = |id: &Identifier| decrement_above(id, level);
    walk_d(body, level + 1, &on_var, &on_binder)
}

/// Whether every occurrence of `level` in `expr` is the thing being eliminated -- the
/// head of an application, the base of a projection, or the scrutinee of a deconstruct.
/// Any other occurrence (an argument, a returned value, a `let` bound) makes this false.
fn all_uses_eliminated<A>(expr: &Expr<A, Identifier>, level: usize) -> bool {
    match expr {
        Expr::Variable(_, Identifier::Bound(k)) => *k != level,
        Expr::Apply(_, Apply { function, argument }) => {
            eliminated_head(function, level) && all_uses_eliminated(argument, level)
        }
        Expr::Project(_, Projection { base, .. }) => eliminated_head(base, level),
        Expr::Deconstruct(
            _,
            Deconstruct {
                scrutinee,
                match_clauses,
            },
        ) => {
            eliminated_head(scrutinee, level)
                && match_clauses
                    .iter()
                    .all(|clause| all_uses_eliminated(&clause.consequent, level))
        }
        other => children(other)
            .into_iter()
            .all(|c| all_uses_eliminated(c, level)),
    }
}

/// A tree in elimination position: a bare variable there is fine (that is the use we
/// want to eliminate, or an unrelated one); anything else must have all *its* uses of
/// `level` eliminated too (handles curried heads like `((x a) b)`).
fn eliminated_head<A>(tree: &Tree<A, Identifier>, level: usize) -> bool {
    match &**tree {
        Expr::Variable(..) => true,
        other => all_uses_eliminated(other, level),
    }
}

/// Depth-carrying structural traversal (companion to [`walk`], which is depth-free).
/// `on_var` sees the absolute depth of each `Variable`; `on_binder` remaps binder ids.
/// Child depths follow the namer's level discipline exactly (see the inliner).
fn walk_d<A>(
    tree: &Tree<A, Identifier>,
    depth: usize,
    on_var: &dyn Fn(usize, &A, &Identifier) -> Expr<A, Identifier>,
    on_binder: &dyn Fn(&Identifier) -> Identifier,
) -> Expr<A, Identifier>
where
    A: Clone,
{
    let go = |t: &Tree<A, Identifier>, d: usize| Rc::new(walk_d(t, d, on_var, on_binder));

    match &**tree {
        Expr::Variable(a, id) => on_var(depth, a, id),
        Expr::InvokeBridge(a, b) => Expr::InvokeBridge(a.clone(), b.clone()),
        Expr::Constant(a, l) => Expr::Constant(a.clone(), l.clone()),
        Expr::MakeClosure(a, info) => Expr::MakeClosure(a.clone(), info.clone()),

        Expr::RecursiveLambda(a, SelfReferential { own_name, lambda }) => Expr::RecursiveLambda(
            a.clone(),
            SelfReferential {
                own_name: on_binder(own_name),
                lambda: Lambda {
                    parameter: on_binder(&lambda.parameter),
                    body: go(&lambda.body, depth + 2),
                },
            },
        ),

        Expr::Lambda(a, Lambda { parameter, body }) => Expr::Lambda(
            a.clone(),
            Lambda {
                parameter: on_binder(parameter),
                body: go(body, depth + 1),
            },
        ),

        Expr::Apply(a, Apply { function, argument }) => Expr::Apply(
            a.clone(),
            Apply {
                function: go(function, depth),
                argument: go(argument, depth),
            },
        ),

        Expr::Let(
            a,
            Binding {
                binder,
                operator,
                bound,
                body,
            },
        ) => Expr::Let(
            a.clone(),
            Binding {
                binder: on_binder(binder),
                operator: *operator,
                bound: go(bound, depth),
                body: go(body, depth + 1),
            },
        ),

        Expr::Tuple(a, Tuple { elements }) => Expr::Tuple(
            a.clone(),
            Tuple {
                elements: elements.iter().map(|e| go(e, depth)).collect(),
            },
        ),

        Expr::Record(a, Record { fields }) => Expr::Record(
            a.clone(),
            Record {
                fields: fields
                    .iter()
                    .map(|(k, v)| (k.clone(), go(v, depth)))
                    .collect(),
            },
        ),

        Expr::Inject(
            a,
            Injection {
                constructor,
                arguments,
            },
        ) => Expr::Inject(
            a.clone(),
            Injection {
                constructor: constructor.clone(),
                arguments: arguments.iter().map(|e| go(e, depth)).collect(),
            },
        ),

        Expr::Array(a, Array { elements }) => Expr::Array(
            a.clone(),
            Array {
                elements: elements.iter().map(|e| go(e, depth)).collect(),
            },
        ),

        Expr::Project(a, Projection { base, select }) => Expr::Project(
            a.clone(),
            Projection {
                base: go(base, depth),
                select: select.clone(),
            },
        ),

        Expr::Sequence(a, Sequence { this, and_then }) => Expr::Sequence(
            a.clone(),
            Sequence {
                this: go(this, depth),
                and_then: go(and_then, depth),
            },
        ),

        Expr::Deconstruct(
            a,
            Deconstruct {
                scrutinee,
                match_clauses,
            },
        ) => Expr::Deconstruct(
            a.clone(),
            Deconstruct {
                scrutinee: go(scrutinee, depth),
                match_clauses: match_clauses
                    .iter()
                    .map(|clause| MatchClause {
                        pattern: walk_pattern(&clause.pattern, on_binder),
                        consequent: go(
                            &clause.consequent,
                            depth + pattern_binder_count(&clause.pattern),
                        ),
                    })
                    .collect(),
            },
        ),

        Expr::If(
            a,
            IfThenElse {
                predicate,
                consequent,
                alternate,
            },
        ) => Expr::If(
            a.clone(),
            IfThenElse {
                predicate: go(predicate, depth),
                consequent: go(consequent, depth),
                alternate: go(alternate, depth),
            },
        ),

        Expr::Interpolate(a, Interpolate(segments)) => Expr::Interpolate(
            a.clone(),
            Interpolate(
                segments
                    .iter()
                    .map(|s| match s {
                        Segment::Literal(sa, l) => Segment::Literal(sa.clone(), l.clone()),
                        Segment::Expression(e) => Segment::Expression(go(e, depth)),
                    })
                    .collect(),
            ),
        ),

        Expr::Ascription(
            a,
            TypeAscription {
                ascribed_tree,
                type_signature,
            },
        ) => Expr::Ascription(
            a.clone(),
            TypeAscription {
                ascribed_tree: go(ascribed_tree, depth),
                type_signature: type_signature.clone(),
            },
        ),
    }
}

/// Whether `let level = E in body` may forward a *non-value* (possibly effectful) `E` into
/// `body` without reordering effects. Sound only when `E`'s single use is the FIRST thing
/// `body` evaluates -- i.e. `body` is directly a `deconstruct`/`project` whose scrutinee/base
/// spine-head is `level`, with the binder used exactly once and nowhere else. Then `E` runs
/// first either way. This is the `let x = ARG in deconstruct x into Suspend v -> v()` shape
/// that `unsafe_run_IO`'s beta-to-let leaves; it deliberately EXCLUDES `let x = E in let y =
/// F in … x …`, where forwarding `x` past `F` would flip their effect order (the bug that
/// reversed `traverse`'s left-to-right prints in stdlib_tests/14_io_effect).
fn forwardable_effectfully<A>(body: &Expr<A, Identifier>, level: usize) -> bool {
    match body {
        Expr::Deconstruct(_, d) => {
            eliminated_head(&d.scrutinee, level) && count_level_uses(&d.scrutinee, level) == 1
        }
        Expr::Project(_, p) => {
            eliminated_head(&p.base, level) && count_level_uses(&p.base, level) == 1
        }
        _ => false,
    }
}

/// Count how many times `level` occurs as a `Variable`. Levels are absolute, so this is
/// correct regardless of nesting depth. Used to spot a *linearly* used `let` binder, which
/// may be forwarded even when its bound expression is not a syntactic value (one use cannot
/// duplicate work).
fn count_level_uses<A>(expr: &Expr<A, Identifier>, level: usize) -> usize {
    match expr {
        Expr::Variable(_, Identifier::Bound(k)) => usize::from(*k == level),
        _ => children(expr)
            .into_iter()
            .map(|c| count_level_uses(c, level))
            .sum(),
    }
}

/// Whether `level` is used anywhere in `expr`. Sound for checking an outer binder's
/// self-reference: the body's own binders all sit strictly deeper, so any `Bound(level)`
/// there is necessarily a use of that outer binder.
fn mentions_level<A>(expr: &Expr<A, Identifier>, level: usize) -> bool {
    match expr {
        Expr::Variable(_, Identifier::Bound(k)) => *k == level,
        _ => children(expr).into_iter().any(|c| mentions_level(c, level)),
    }
}

/// An inert, self-contained value with no bound variables -- safe to substitute for
/// a binder without any level bookkeeping and without changing behaviour.
fn is_closed_atom<A>(expr: &Expr<A, Identifier>) -> bool {
    matches!(
        expr,
        Expr::Variable(_, Identifier::Free(_)) | Expr::Constant(..) | Expr::InvokeBridge(..)
    )
}

/// A `let` whose binder is a `Bound` level -- the shape `let-float` can move (it needs
/// the level to shift the siblings that slide under the binder).
fn is_floatable_let<A>(tree: &Tree<A, Identifier>) -> bool {
    matches!(
        &**tree,
        Expr::Let(
            _,
            Binding {
                binder: Identifier::Bound(_),
                ..
            }
        )
    )
}

/// Unwrap a floatable `let`, yielding its annotation, its binding, and its binder
/// level. Guarded by [`is_floatable_let`].
fn open_let<A>(tree: Tree<A, Identifier>) -> (A, Binding<A, Identifier>, usize)
where
    A: Clone,
{
    let Expr::Let(a, binding) = Rc::unwrap_or_clone(tree) else {
        unreachable!("guarded by is_floatable_let")
    };
    let Identifier::Bound(level) = binding.binder else {
        unreachable!("guarded by is_floatable_let")
    };
    (a, binding, level)
}

fn rewrap_let<A>(
    a: A,
    binder: Identifier,
    operator: BindingOperator,
    bound: Tree<A, Identifier>,
    body: Expr<A, Identifier>,
) -> Expr<A, Identifier> {
    Expr::Let(
        a,
        Binding {
            binder,
            operator,
            bound,
            body: Rc::new(body),
        },
    )
}

/// `(a, b).0 -> a` and `{x: a; y: b}.x -> a`, but only when the discarded siblings
/// are values: this language is strict, so dropping a sibling that could diverge or
/// carry an effect would change behaviour. (Effects are reified as IO values, so a
/// value is genuinely inert.)
fn project_literal<A>(_a: &A, projection: &Projection<A, Identifier>) -> Option<Expr<A, Identifier>>
where
    A: Clone,
{
    match (&*projection.base, &projection.select) {
        (Expr::Tuple(_, Tuple { elements }), ProductElement::Ordinal(index)) => {
            let index = *index;
            (index < elements.len() && siblings_are_values(elements, index))
                .then(|| Rc::unwrap_or_clone(elements[index].clone()))
        }

        (Expr::Record(_, Record { fields }), ProductElement::Name(name)) => {
            let position = fields.iter().position(|(label, _)| label == name)?;
            project_field(fields, position)
        }

        // Dictionaries are records but elaborated code projects their methods by
        // ordinal (`dict.&1`), not by name. Record fields are stored in sorted label
        // order (see `Record::from_fields`), so ordinal `i` is field `i`. This is the
        // case that fires on an inlined witness -- the heart of the dictionary collapse.
        (Expr::Record(_, Record { fields }), ProductElement::Ordinal(index)) => (*index
            < fields.len())
        .then(|| project_field(fields, *index))
        .flatten(),

        _ => None,
    }
}

fn project_field<A>(
    fields: &[(crate::parser::Identifier, Tree<A, Identifier>)],
    position: usize,
) -> Option<Expr<A, Identifier>>
where
    A: Clone,
{
    let values = fields.iter().map(|(_, v)| v.clone()).collect::<Vec<_>>();
    siblings_are_values(&values, position).then(|| Rc::unwrap_or_clone(fields[position].1.clone()))
}

fn siblings_are_values<A>(elements: &[Tree<A, Identifier>], keep: usize) -> bool {
    elements
        .iter()
        .enumerate()
        .all(|(i, e)| i == keep || is_value(e))
}

/// A syntactic value: something already in weak-head normal form that can neither
/// diverge nor perform an effect when reduced. Deliberately conservative.
fn is_value<A>(expr: &Expr<A, Identifier>) -> bool {
    match expr {
        Expr::Variable(..)
        | Expr::Constant(..)
        | Expr::Lambda(..)
        | Expr::RecursiveLambda(..)
        | Expr::InvokeBridge(..) => true,
        Expr::Tuple(_, Tuple { elements }) => elements.iter().all(|e| is_value(e)),
        Expr::Record(_, Record { fields }) => fields.iter().all(|(_, v)| is_value(v)),
        Expr::Inject(_, Injection { arguments, .. }) => arguments.iter().all(|e| is_value(e)),
        // A `let` binding a value inside a value is itself pure and terminating -- this
        // is what lets projection-of-literal see past a dictionary super-field that is
        // still wrapped in a (pending) `let`.
        Expr::Let(_, Binding { bound, body, .. }) => is_value(bound) && is_value(body),
        // Projecting a value is pure and terminating (reading a field of a record).
        Expr::Project(_, Projection { base, .. }) => is_value(base),
        _ => false,
    }
}

/// case-of-known-constructor and tuple-deconstruct. The scrutinee is a literal
/// `Inject`/`Tuple`, so the matching clause is known statically; splice it in as a
/// let-chain that binds each pattern variable to the matching argument. Every
/// argument is still evaluated (the pattern binds them all), so evaluation order is
/// preserved.
fn deconstruct_literal<A>(
    a: &A,
    deconstruct: &Deconstruct<A, Identifier>,
) -> Option<Expr<A, Identifier>>
where
    A: Clone,
{
    let Deconstruct {
        scrutinee,
        match_clauses,
    } = deconstruct;

    match &**scrutinee {
        Expr::Inject(_, injection) => {
            select_constructor_clause(a, scrutinee, injection, match_clauses)
        }
        Expr::Tuple(_, tuple) => select_tuple_clause(a, scrutinee, tuple, match_clauses),

        // A constructor referenced as a *value* and then applied -- `Apply(Variable(C), args)`
        // -- is never built as an `Inject` (only a syntactic `C args` is), so it never meets
        // its `deconstruct` and the box never cancels. Fold a *saturated* such application into
        // an injection view so the ordinary case-of-known-constructor selection fires. Guarded
        // to a head whose name actually matches one of the clause constructors, so it only ever
        // touches genuine constructor values, never an ordinary function application; arity is
        // enforced downstream by `build_let_chain` (a partial application declines). This is
        // what finally collapses `IO.suspend` / `MkGet` / `MkExceptT` / `MkState` values that a
        // `let*`-desugared `bind` applies, once they reach a force -- the monad-ceremony boxes.
        Expr::Apply(..) if iodeforest_on() => {
            let (head, arguments) = peel_apply_spine(scrutinee);
            let qn = match head {
                Expr::Variable(_, id) => id.try_as_free()?,
                _ => return None,
            };
            let names_a_clause = match_clauses.iter().any(|clause| {
                matches!(&clause.pattern,
                    Pattern::Coproduct(_, cp) if cp.constructor.try_as_free() == Some(qn))
            });
            if !names_a_clause {
                return None;
            }
            let injection = Injection {
                constructor: qn.clone(),
                arguments,
            };
            select_constructor_clause(a, scrutinee, &injection, match_clauses)
        }
        _ => None,
    }
}

/// Peel a left-nested application spine `((h a₁) a₂ …) aₙ` into its head `h` and the argument
/// list `[a₁, …, aₙ]` in source order. A non-application returns itself and no arguments.
fn peel_apply_spine<A>(
    scrutinee: &Tree<A, Identifier>,
) -> (&Expr<A, Identifier>, Vec<Tree<A, Identifier>>) {
    let mut node: &Expr<A, Identifier> = &**scrutinee;
    let mut arguments = Vec::new();
    while let Expr::Apply(_, apply) = node {
        arguments.push(apply.argument.clone());
        node = &apply.function;
    }
    arguments.reverse();
    (node, arguments)
}

fn select_constructor_clause<A>(
    a: &A,
    scrutinee: &Tree<A, Identifier>,
    injection: &Injection<A, Identifier>,
    clauses: &[MatchClause<A, Identifier>],
) -> Option<Expr<A, Identifier>>
where
    A: Clone,
{
    for clause in clauses {
        match &clause.pattern {
            // A wildcard binder reached before the constructor clause: it matches,
            // binding the whole scrutinee.
            Pattern::Bind(_, Identifier::Bound(level)) => {
                return Some(bind_whole(a, *level, scrutinee, &clause.consequent));
            }

            Pattern::Coproduct(
                _,
                ConstructorPattern {
                    constructor: Identifier::Free(name),
                    arguments,
                },
            ) => {
                if **name == injection.constructor {
                    return build_let_chain(a, &injection.arguments, arguments, &clause.consequent);
                }
                // A different constructor can never match this injection; skip it.
            }

            // A literal pattern can never match an injection; skip it. Anything
            // else on a coproduct scrutinee is unexpected, so bail conservatively.
            Pattern::Literally(..) => {}
            _ => return None,
        }
    }
    None
}

fn select_tuple_clause<A>(
    a: &A,
    scrutinee: &Tree<A, Identifier>,
    tuple: &Tuple<A, Identifier>,
    clauses: &[MatchClause<A, Identifier>],
) -> Option<Expr<A, Identifier>>
where
    A: Clone,
{
    // A tuple pattern is irrefutable, so the first clause is the one selected.
    let clause = clauses.first()?;
    match &clause.pattern {
        Pattern::Bind(_, Identifier::Bound(level)) => {
            Some(bind_whole(a, *level, scrutinee, &clause.consequent))
        }
        Pattern::Tuple(_, TuplePattern { elements }) => {
            build_let_chain(a, &tuple.elements, elements, &clause.consequent)
        }
        _ => None,
    }
}

/// `let <level> = <scrutinee> in <consequent>` -- the wildcard case, where the
/// whole scrutinee is bound to a single variable.
fn bind_whole<A>(
    a: &A,
    level: usize,
    scrutinee: &Tree<A, Identifier>,
    consequent: &Tree<A, Identifier>,
) -> Expr<A, Identifier>
where
    A: Clone,
{
    Expr::Let(
        a.clone(),
        Binding {
            binder: Identifier::Bound(level),
            operator: BindingOperator::Identity,
            bound: scrutinee.clone(),
            body: consequent.clone(),
        },
    )
}

/// Build the let-chain that binds each destructured argument. Only fires when every
/// sub-pattern is a simple binder whose levels are `base, base+1, .., base+n-1` in
/// positional order (the shape the monadic cascade produces); anything nested or
/// out of order bails so the deconstruct is left untouched.
///
/// Argument `i` ends up nested under `i` new binders, so its own internal levels
/// (`>= base`) shift up by `i`; there are no references to `base..base+i-1` inside
/// it (those binders did not exist when it was named), so a flat `shift` is exact.
fn build_let_chain<A>(
    a: &A,
    arguments: &[Tree<A, Identifier>],
    patterns: &[Pattern<A, Identifier>],
    consequent: &Tree<A, Identifier>,
) -> Option<Expr<A, Identifier>>
where
    A: Clone,
{
    if arguments.len() != patterns.len() {
        return None;
    }

    let levels = patterns
        .iter()
        .map(|p| match p {
            Pattern::Bind(_, Identifier::Bound(level)) => Some(*level),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;

    // Nullary constructor (e.g. `Nil`): nothing to bind, the clause is its consequent.
    let Some(&base) = levels.first() else {
        return Some(Rc::unwrap_or_clone(consequent.clone()));
    };

    if levels
        .iter()
        .enumerate()
        .any(|(i, &level)| level != base + i)
    {
        return None;
    }

    let mut body = consequent.clone();
    for i in (0..arguments.len()).rev() {
        let bound = if i == 0 {
            arguments[i].clone()
        } else {
            Rc::new(shift(&arguments[i], base, i))
        };
        body = Rc::new(Expr::Let(
            a.clone(),
            Binding {
                binder: Identifier::Bound(base + i),
                operator: BindingOperator::Identity,
                bound,
                body,
            },
        ));
    }

    Some(Rc::unwrap_or_clone(body))
}

/// Relocate a sub-tree by `by`, bumping every `Bound(k)` with `k >= from` (both uses
/// *and* binders *and* pattern binders -- levels are absolute, so this is a flat
/// map). `Free` names are global and untouched.
fn shift<A>(tree: &Tree<A, Identifier>, from: usize, by: usize) -> Expr<A, Identifier>
where
    A: Clone,
{
    let on_var = |a: &A, id: &Identifier| Expr::Variable(a.clone(), shift_id(id, from, by));
    let on_binder = |id: &Identifier| shift_id(id, from, by);
    walk(tree, &on_var, &on_binder)
}

fn shift_id(id: &Identifier, from: usize, by: usize) -> Identifier {
    match id {
        Identifier::Bound(k) if *k >= from => Identifier::Bound(k + by),
        other => other.clone(),
    }
}

/// Substitute a **closed atom** (a `Free`/`Constant`/`InvokeBridge` -- something with
/// no bound variables of its own) for the binder at absolute level `level`, and drop
/// that binder: every `Bound(k)` with `k > level` moves down one level (the body has
/// lost an enclosing binder). Because the atom is closed there is nothing in it to
/// relocate, so no shifting of the atom is needed. `level` itself never occurs as a
/// binder inside the body (the namer numbers strictly by depth), only as a use.
fn substitute_atom<A>(
    body: &Tree<A, Identifier>,
    level: usize,
    atom: &Expr<A, Identifier>,
) -> Expr<A, Identifier>
where
    A: Clone,
{
    let on_var = |a: &A, id: &Identifier| match id {
        Identifier::Bound(k) if *k == level => atom.clone(),
        other => Expr::Variable(a.clone(), decrement_above(other, level)),
    };
    let on_binder = |id: &Identifier| decrement_above(id, level);
    walk(body, &on_var, &on_binder)
}

/// `Bound(k) -> Bound(k - 1)` for `k > level`; everything else untouched.
fn decrement_above(id: &Identifier, level: usize) -> Identifier {
    match id {
        Identifier::Bound(k) if *k > level => Identifier::Bound(k - 1),
        other => other.clone(),
    }
}

/// The single structural traversal shared by every level-remapping rewrite. `on_var`
/// rewrites a `Variable` node (it may expand to any expression -- that is what lets
/// substitution splice an atom in); `on_binder` rewrites every identifier that sits
/// in a *binding* position (lambda/let/self binders, pattern binds, and the `Free`
/// constructor of a coproduct pattern -- left untouched by every current caller).
/// The remap is depth-independent because levels are absolute, so children recurse
/// with the very same closures.
fn walk<A>(
    tree: &Tree<A, Identifier>,
    on_var: &dyn Fn(&A, &Identifier) -> Expr<A, Identifier>,
    on_binder: &dyn Fn(&Identifier) -> Identifier,
) -> Expr<A, Identifier>
where
    A: Clone,
{
    let go = |t: &Tree<A, Identifier>| Rc::new(walk(t, on_var, on_binder));

    match &**tree {
        Expr::Variable(a, id) => on_var(a, id),
        Expr::InvokeBridge(a, bridge) => Expr::InvokeBridge(a.clone(), bridge.clone()),
        Expr::Constant(a, literal) => Expr::Constant(a.clone(), literal.clone()),

        Expr::RecursiveLambda(a, SelfReferential { own_name, lambda }) => Expr::RecursiveLambda(
            a.clone(),
            SelfReferential {
                own_name: on_binder(own_name),
                lambda: Lambda {
                    parameter: on_binder(&lambda.parameter),
                    body: go(&lambda.body),
                },
            },
        ),

        Expr::Lambda(a, Lambda { parameter, body }) => Expr::Lambda(
            a.clone(),
            Lambda {
                parameter: on_binder(parameter),
                body: go(body),
            },
        ),

        Expr::Apply(a, Apply { function, argument }) => Expr::Apply(
            a.clone(),
            Apply {
                function: go(function),
                argument: go(argument),
            },
        ),

        Expr::Let(
            a,
            Binding {
                binder,
                operator,
                bound,
                body,
            },
        ) => Expr::Let(
            a.clone(),
            Binding {
                binder: on_binder(binder),
                operator: *operator,
                bound: go(bound),
                body: go(body),
            },
        ),

        Expr::Tuple(a, Tuple { elements }) => Expr::Tuple(
            a.clone(),
            Tuple {
                elements: elements.iter().map(&go).collect(),
            },
        ),

        Expr::Record(a, Record { fields }) => Expr::Record(
            a.clone(),
            Record {
                fields: fields.iter().map(|(k, v)| (k.clone(), go(v))).collect(),
            },
        ),

        Expr::Inject(
            a,
            Injection {
                constructor,
                arguments,
            },
        ) => Expr::Inject(
            a.clone(),
            Injection {
                constructor: constructor.clone(),
                arguments: arguments.iter().map(&go).collect(),
            },
        ),

        Expr::Array(a, Array { elements }) => Expr::Array(
            a.clone(),
            Array {
                elements: elements.iter().map(&go).collect(),
            },
        ),

        Expr::Project(a, Projection { base, select }) => Expr::Project(
            a.clone(),
            Projection {
                base: go(base),
                select: select.clone(),
            },
        ),

        Expr::Sequence(a, Sequence { this, and_then }) => Expr::Sequence(
            a.clone(),
            Sequence {
                this: go(this),
                and_then: go(and_then),
            },
        ),

        Expr::Deconstruct(
            a,
            Deconstruct {
                scrutinee,
                match_clauses,
            },
        ) => Expr::Deconstruct(
            a.clone(),
            Deconstruct {
                scrutinee: go(scrutinee),
                match_clauses: match_clauses
                    .iter()
                    .map(|clause| MatchClause {
                        pattern: walk_pattern(&clause.pattern, on_binder),
                        consequent: go(&clause.consequent),
                    })
                    .collect(),
            },
        ),

        Expr::If(
            a,
            IfThenElse {
                predicate,
                consequent,
                alternate,
            },
        ) => Expr::If(
            a.clone(),
            IfThenElse {
                predicate: go(predicate),
                consequent: go(consequent),
                alternate: go(alternate),
            },
        ),

        Expr::Interpolate(a, Interpolate(segments)) => Expr::Interpolate(
            a.clone(),
            Interpolate(
                segments
                    .iter()
                    .map(|segment| match segment {
                        Segment::Literal(sa, literal) => {
                            Segment::Literal(sa.clone(), literal.clone())
                        }
                        Segment::Expression(expr) => Segment::Expression(go(expr)),
                    })
                    .collect(),
            ),
        ),

        Expr::Ascription(
            a,
            TypeAscription {
                ascribed_tree,
                type_signature,
            },
        ) => Expr::Ascription(
            a.clone(),
            TypeAscription {
                ascribed_tree: go(ascribed_tree),
                type_signature: type_signature.clone(),
            },
        ),

        // Only appears after lambda-lift, which runs strictly later.
        Expr::MakeClosure(a, info) => Expr::MakeClosure(a.clone(), info.clone()),
    }
}

fn walk_pattern<A>(
    pattern: &Pattern<A, Identifier>,
    on_binder: &dyn Fn(&Identifier) -> Identifier,
) -> Pattern<A, Identifier>
where
    A: Clone,
{
    match pattern {
        Pattern::Coproduct(
            a,
            ConstructorPattern {
                constructor,
                arguments,
            },
        ) => Pattern::Coproduct(
            a.clone(),
            ConstructorPattern {
                constructor: on_binder(constructor),
                arguments: arguments
                    .iter()
                    .map(|p| walk_pattern(p, on_binder))
                    .collect(),
            },
        ),

        Pattern::Tuple(a, TuplePattern { elements }) => Pattern::Tuple(
            a.clone(),
            TuplePattern {
                elements: elements
                    .iter()
                    .map(|p| walk_pattern(p, on_binder))
                    .collect(),
            },
        ),

        Pattern::Struct(a, StructPattern { fields }) => Pattern::Struct(
            a.clone(),
            StructPattern {
                fields: fields
                    .iter()
                    .map(|(label, p)| (label.clone(), walk_pattern(p, on_binder)))
                    .collect(),
            },
        ),

        Pattern::Literally(a, literal) => Pattern::Literally(a.clone(), literal.clone()),
        Pattern::Bind(a, id) => Pattern::Bind(a.clone(), on_binder(id)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Literal, ProductElement};

    type E = Expr<(), Identifier>;

    fn var(k: usize) -> Tree<(), Identifier> {
        Rc::new(Expr::Variable((), Identifier::Bound(k)))
    }

    fn free_id(name: &str) -> Identifier {
        Identifier::Free(Box::new(
            crate::ast::namer::QualifiedName::from_root_symbol(
                crate::parser::Identifier::from_str(name),
            ),
        ))
    }

    fn free(name: &str) -> Tree<(), Identifier> {
        Rc::new(Expr::Variable((), free_id(name)))
    }

    fn int(n: i64) -> Tree<(), Identifier> {
        Rc::new(Expr::Constant((), Literal::Int(n)))
    }

    fn lam(param: usize, body: Tree<(), Identifier>) -> Tree<(), Identifier> {
        Rc::new(Expr::Lambda(
            (),
            Lambda {
                parameter: Identifier::Bound(param),
                body,
            },
        ))
    }

    fn apply(f: Tree<(), Identifier>, x: Tree<(), Identifier>) -> E {
        Expr::Apply(
            (),
            Apply {
                function: f,
                argument: x,
            },
        )
    }

    fn simplify(e: E) -> E {
        simplify_expr(e)
    }

    // ---- shift ----

    #[test]
    fn shift_bumps_bound_at_or_above_threshold() {
        // Bound(3) with from=2 by=5 -> Bound(8)
        assert!(matches!(
            shift(&var(3), 2, 5),
            Expr::Variable((), Identifier::Bound(8))
        ));
    }

    #[test]
    fn shift_leaves_below_threshold_alone() {
        assert!(matches!(
            shift(&var(1), 2, 5),
            Expr::Variable((), Identifier::Bound(1))
        ));
    }

    #[test]
    fn shift_at_threshold_is_shifted() {
        assert!(matches!(
            shift(&var(2), 2, 5),
            Expr::Variable((), Identifier::Bound(7))
        ));
    }

    #[test]
    fn shift_leaves_free_untouched() {
        assert!(matches!(
            shift(&free("g"), 0, 9),
            Expr::Variable((), Identifier::Free(_))
        ));
    }

    #[test]
    fn shift_hits_binders_and_uses_uniformly() {
        // λ#2. #2  with from=2 by=3  ->  λ#5. #5   (binder and use move together)
        let e = Rc::new(Expr::Lambda(
            (),
            Lambda {
                parameter: Identifier::Bound(2),
                body: var(2),
            },
        ));
        let Expr::Lambda((), Lambda { parameter, body }) = shift(&e, 2, 3) else {
            panic!("expected lambda")
        };
        assert!(matches!(parameter, Identifier::Bound(5)));
        assert!(matches!(&*body, Expr::Variable((), Identifier::Bound(5))));
    }

    #[test]
    fn shift_reaches_pattern_binders() {
        // deconstruct #0 { C #1 -> #1 }  shifted from=1 by=4
        let clause = MatchClause {
            pattern: Pattern::Coproduct(
                (),
                ConstructorPattern {
                    constructor: Identifier::Free(Box::new(
                        crate::ast::namer::QualifiedName::from_root_symbol(
                            crate::parser::Identifier::from_str("C"),
                        ),
                    )),
                    arguments: vec![Pattern::Bind((), Identifier::Bound(1))],
                },
            ),
            consequent: var(1),
        };
        let e = Rc::new(Expr::Deconstruct(
            (),
            Deconstruct {
                scrutinee: var(0),
                match_clauses: vec![clause],
            },
        ));
        let Expr::Deconstruct((), d) = shift(&e, 1, 4) else {
            panic!("expected deconstruct")
        };
        // scrutinee #0 stays (below threshold)
        assert!(matches!(
            &*d.scrutinee,
            Expr::Variable((), Identifier::Bound(0))
        ));
        let Pattern::Coproduct((), cp) = &d.match_clauses[0].pattern else {
            panic!("expected coproduct pattern")
        };
        assert!(matches!(
            cp.arguments[0],
            Pattern::Bind((), Identifier::Bound(5))
        ));
        assert!(matches!(
            &*d.match_clauses[0].consequent,
            Expr::Variable((), Identifier::Bound(5))
        ));
    }

    // ---- substitute_atom ----

    #[test]
    fn substitute_atom_replaces_binder_and_decrements_deeper_uses() {
        // body = (#2, #1); substitute g for level 1 -> (#1, g)
        //   #1 is the binder -> g;  #2 is deeper (2 > 1) -> #1
        let body = Rc::new(Expr::Tuple(
            (),
            Tuple {
                elements: vec![var(2), var(1)],
            },
        ));
        let g = Expr::Variable((), free_id("g"));
        let Expr::Tuple((), t) = substitute_atom(&body, 1, &g) else {
            panic!("expected tuple")
        };
        assert!(matches!(
            &*t.elements[0],
            Expr::Variable((), Identifier::Bound(1))
        ));
        assert!(matches!(
            &*t.elements[1],
            Expr::Variable((), Identifier::Free(_))
        ));
    }

    #[test]
    fn substitute_atom_decrements_inner_binders() {
        // body = λ#2. #2; substitute for level 1 -> λ#1. #1  (binder and use both -1)
        let body = lam(2, var(2));
        let g = Expr::Variable((), free_id("g"));
        let Expr::Lambda((), Lambda { parameter, body }) = substitute_atom(&body, 1, &g) else {
            panic!("expected lambda")
        };
        assert!(matches!(parameter, Identifier::Bound(1)));
        assert!(matches!(&*body, Expr::Variable((), Identifier::Bound(1))));
    }

    #[test]
    fn beta_substitutes_closed_atom_keeping_spine() {
        // (λ#0. #0) g  ->  g   (closed atom substituted, not let-bound)
        let e = apply(lam(0, var(0)), free("g"));
        assert!(matches!(
            simplify(e),
            Expr::Variable((), Identifier::Free(_))
        ));
    }

    // ---- let-float ----

    // A non-value bound (an application that could diverge / carry an effect) so that
    // let-forwarding deliberately abstains and the let-float is observable on its own.
    fn effectful_let(body: Tree<(), Identifier>) -> Tree<(), Identifier> {
        Rc::new(Expr::Let(
            (),
            Binding {
                binder: Identifier::Bound(0),
                operator: BindingOperator::Identity,
                bound: Rc::new(apply(free("g"), free("y"))),
                body,
            },
        ))
    }

    #[test]
    fn let_floats_out_of_application() {
        // (let #0 = (g y) in k) 5  ->  let #0 = (g y) in (k 5)
        let e = apply(effectful_let(free("k")), int(5));
        let Expr::Let((), binding) = simplify(e) else {
            panic!("expected let")
        };
        assert!(matches!(binding.binder, Identifier::Bound(0)));
        assert!(matches!(&*binding.bound, Expr::Apply(..)));
        assert!(matches!(&*binding.body, Expr::Apply(..)));
    }

    #[test]
    fn let_float_shifts_argument_under_the_binder() {
        // (let #0 = (g y) in k) (λ#0. #0)
        //   -> let #0 = (g y) in (k (λ#1. #1))   -- the argument slid under binder #0
        let e = apply(effectful_let(free("k")), lam(0, var(0)));
        let Expr::Let((), binding) = simplify(e) else {
            panic!("expected let")
        };
        let Expr::Apply((), inner) = &*binding.body else {
            panic!("expected application")
        };
        assert!(matches!(
            &*inner.argument,
            Expr::Lambda(
                (),
                Lambda {
                    parameter: Identifier::Bound(1),
                    ..
                }
            )
        ));
    }

    // ---- let-forwarding ----

    #[test]
    fn forwards_value_let_into_projection_and_cancels() {
        // let #0 = (7, 8) in #0.&1  ->  (7, 8).&1  ->  8
        let pair = Rc::new(Expr::Tuple(
            (),
            Tuple {
                elements: vec![int(7), int(8)],
            },
        ));
        let e = Expr::Let(
            (),
            Binding {
                binder: Identifier::Bound(0),
                operator: BindingOperator::Identity,
                bound: pair,
                body: Rc::new(Expr::Project(
                    (),
                    Projection {
                        base: var(0),
                        select: ProductElement::Ordinal(1),
                    },
                )),
            },
        );
        assert!(matches!(simplify(e), Expr::Constant((), Literal::Int(8))));
    }

    #[test]
    fn drops_dead_pure_let() {
        // let #0 = 9 in k  ->  k   (binder unused, value bound is pure)
        let e = Expr::Let(
            (),
            Binding {
                binder: Identifier::Bound(0),
                operator: BindingOperator::Identity,
                bound: int(9),
                body: free("k"),
            },
        );
        assert!(matches!(
            simplify(e),
            Expr::Variable((), Identifier::Free(_))
        ));
    }

    #[test]
    fn keeps_let_used_outside_elimination_position() {
        // let #0 = 9 in (#0, #0): #0 is returned in a tuple, not eliminated, so the
        // let is kept (forwarding here would de-share with no cancelling reduction).
        let e = Expr::Let(
            (),
            Binding {
                binder: Identifier::Bound(0),
                operator: BindingOperator::Identity,
                bound: int(9),
                body: Rc::new(Expr::Tuple(
                    (),
                    Tuple {
                        elements: vec![var(0), var(0)],
                    },
                )),
            },
        );
        assert!(matches!(simplify(e), Expr::Let(..)));
    }

    #[test]
    fn substitute_value_relocates_to_use_depth() {
        // substitute (#7,) for level 0 in  λ#1. #0
        //   -> λ#0. (#8,)   -- binder #1 drops to #0; the value, used one binder deep,
        //      shifts its free level #7 up to #8.
        let value = Rc::new(Expr::Tuple(
            (),
            Tuple {
                elements: vec![var(7)],
            },
        ));
        let body = lam(1, var(0));
        let Expr::Lambda((), Lambda { parameter, body }) = substitute_value(&body, 0, &value)
        else {
            panic!("expected lambda")
        };
        assert!(matches!(parameter, Identifier::Bound(0)));
        let Expr::Tuple((), t) = &*body else {
            panic!("expected tuple")
        };
        assert!(matches!(
            &*t.elements[0],
            Expr::Variable((), Identifier::Bound(8))
        ));
    }

    // ---- beta-to-let ----

    #[test]
    fn beta_to_let_rewrites_application_of_lambda() {
        // A non-atom argument (an application that could diverge / carry an effect)
        // is bound with a strict `let`, not substituted:
        //   (λ#0. #0) (f 0)  ->  let #0 = (f 0) in #0
        let e = apply(lam(0, var(0)), Rc::new(apply(free("f"), int(0))));
        let Expr::Let((), binding) = simplify(e) else {
            panic!("expected let")
        };
        assert!(matches!(binding.binder, Identifier::Bound(0)));
        assert!(matches!(&*binding.bound, Expr::Apply(..)));
        assert!(matches!(
            &*binding.body,
            Expr::Variable((), Identifier::Bound(0))
        ));
    }

    #[test]
    fn beta_to_let_leaves_ordinary_application_alone() {
        let e = apply(free("f"), int(1));
        assert!(matches!(simplify(e), Expr::Apply(..)));
    }

    // ---- projection-of-literal ----

    #[test]
    fn projects_tuple_when_siblings_are_values() {
        // (10, 20).1 -> 20
        let e = Expr::Project(
            (),
            Projection {
                base: Rc::new(Expr::Tuple(
                    (),
                    Tuple {
                        elements: vec![int(10), int(20)],
                    },
                )),
                select: ProductElement::Ordinal(1),
            },
        );
        assert!(matches!(simplify(e), Expr::Constant((), Literal::Int(20))));
    }

    #[test]
    fn does_not_project_when_a_sibling_is_effectful() {
        // (f x, 20).1 must not drop `f x` (an application may diverge / carry effects)
        let e = Expr::Project(
            (),
            Projection {
                base: Rc::new(Expr::Tuple(
                    (),
                    Tuple {
                        elements: vec![Rc::new(apply(free("f"), int(0))), int(20)],
                    },
                )),
                select: ProductElement::Ordinal(1),
            },
        );
        assert!(matches!(simplify(e), Expr::Project(..)));
    }

    // ---- case-of-known-constructor ----

    fn ctor(name: &str) -> crate::ast::namer::QualifiedName {
        crate::ast::namer::QualifiedName::from_root_symbol(crate::parser::Identifier::from_str(
            name,
        ))
    }

    #[test]
    fn selects_matching_constructor_clause_as_let_chain() {
        // deconstruct (Pair 10 20) { Nil -> 0 | Pair #0 #1 -> (#0, #1) }
        //   -> let #0 = 10 in let #1 = 20 in (#0, #1)
        // (The consequent uses both binders in non-elimination position, so
        // let-forwarding leaves the chain intact.)
        let scrutinee = Rc::new(Expr::Inject(
            (),
            Injection {
                constructor: ctor("Pair"),
                arguments: vec![int(10), int(20)],
            },
        ));
        let nil_clause = MatchClause {
            pattern: Pattern::Coproduct(
                (),
                ConstructorPattern {
                    constructor: Identifier::Free(Box::new(ctor("Nil"))),
                    arguments: vec![],
                },
            ),
            consequent: int(0),
        };
        let pair_clause = MatchClause {
            pattern: Pattern::Coproduct(
                (),
                ConstructorPattern {
                    constructor: Identifier::Free(Box::new(ctor("Pair"))),
                    arguments: vec![
                        Pattern::Bind((), Identifier::Bound(0)),
                        Pattern::Bind((), Identifier::Bound(1)),
                    ],
                },
            ),
            consequent: Rc::new(Expr::Tuple(
                (),
                Tuple {
                    elements: vec![var(0), var(1)],
                },
            )),
        };
        let e = Expr::Deconstruct(
            (),
            Deconstruct {
                scrutinee,
                match_clauses: vec![nil_clause, pair_clause],
            },
        );

        let Expr::Let((), outer) = simplify(e) else {
            panic!("expected outer let")
        };
        assert!(matches!(outer.binder, Identifier::Bound(0)));
        assert!(matches!(
            &*outer.bound,
            Expr::Constant((), Literal::Int(10))
        ));
        let Expr::Let((), inner) = &*outer.body else {
            panic!("expected inner let")
        };
        assert!(matches!(inner.binder, Identifier::Bound(1)));
        assert!(matches!(
            &*inner.bound,
            Expr::Constant((), Literal::Int(20))
        ));
        assert!(matches!(&*inner.body, Expr::Tuple(..)));
    }

    #[test]
    fn nullary_constructor_selects_bare_consequent() {
        // deconstruct Nil { Nil -> 42 | Cons #0 #1 -> #0 } -> 42
        let scrutinee = Rc::new(Expr::Inject(
            (),
            Injection {
                constructor: ctor("Nil"),
                arguments: vec![],
            },
        ));
        let nil_clause = MatchClause {
            pattern: Pattern::Coproduct(
                (),
                ConstructorPattern {
                    constructor: Identifier::Free(Box::new(ctor("Nil"))),
                    arguments: vec![],
                },
            ),
            consequent: int(42),
        };
        let cons_clause = MatchClause {
            pattern: Pattern::Coproduct(
                (),
                ConstructorPattern {
                    constructor: Identifier::Free(Box::new(ctor("Cons"))),
                    arguments: vec![
                        Pattern::Bind((), Identifier::Bound(0)),
                        Pattern::Bind((), Identifier::Bound(1)),
                    ],
                },
            ),
            consequent: var(0),
        };
        let e = Expr::Deconstruct(
            (),
            Deconstruct {
                scrutinee,
                match_clauses: vec![nil_clause, cons_clause],
            },
        );
        assert!(matches!(simplify(e), Expr::Constant((), Literal::Int(42))));
    }

    #[test]
    fn tuple_deconstruct_shifts_later_arguments() {
        // deconstruct (#5, λ#0.#0) { (#5, #6) -> (#5, #6) }
        //  -> let #5 = #5 in let #6 = shift(λ#0.#0, from=5, by=1) in (#5, #6)
        // The lambda's binder #0 is below the shift threshold, so it stays #0. Both
        // binders are used in non-elimination position, so the chain stays intact.
        let scrutinee = Rc::new(Expr::Tuple(
            (),
            Tuple {
                elements: vec![var(5), lam(0, var(0))],
            },
        ));
        let clause = MatchClause {
            pattern: Pattern::Tuple(
                (),
                TuplePattern {
                    elements: vec![
                        Pattern::Bind((), Identifier::Bound(5)),
                        Pattern::Bind((), Identifier::Bound(6)),
                    ],
                },
            ),
            consequent: Rc::new(Expr::Tuple(
                (),
                Tuple {
                    elements: vec![var(5), var(6)],
                },
            )),
        };
        let e = Expr::Deconstruct(
            (),
            Deconstruct {
                scrutinee,
                match_clauses: vec![clause],
            },
        );
        let Expr::Let((), outer) = simplify(e) else {
            panic!("expected outer let")
        };
        assert!(matches!(outer.binder, Identifier::Bound(5)));
        assert!(matches!(
            &*outer.bound,
            Expr::Variable((), Identifier::Bound(5))
        ));
        let Expr::Let((), inner) = &*outer.body else {
            panic!("expected inner let")
        };
        assert!(matches!(inner.binder, Identifier::Bound(6)));
        // shifted lambda still has its own binder at #0 (below threshold 5)
        assert!(matches!(
            &*inner.bound,
            Expr::Lambda(
                (),
                Lambda {
                    parameter: Identifier::Bound(0),
                    ..
                }
            )
        ));
    }

    #[test]
    fn wildcard_clause_binds_whole_scrutinee() {
        // deconstruct (Pair 1 2) { #0 -> #0 } -> let #0 = Pair 1 2 in #0
        let scrutinee = Rc::new(Expr::Inject(
            (),
            Injection {
                constructor: ctor("Pair"),
                arguments: vec![int(1), int(2)],
            },
        ));
        let clause = MatchClause {
            pattern: Pattern::Bind((), Identifier::Bound(0)),
            consequent: var(0),
        };
        let e = Expr::Deconstruct(
            (),
            Deconstruct {
                scrutinee,
                match_clauses: vec![clause],
            },
        );
        let Expr::Let((), binding) = simplify(e) else {
            panic!("expected let")
        };
        assert!(matches!(binding.binder, Identifier::Bound(0)));
        assert!(matches!(&*binding.bound, Expr::Inject(..)));
    }

    #[test]
    fn leaves_nested_subpattern_deconstruct_alone() {
        // A nested constructor sub-pattern is not a simple bind, so bail.
        let scrutinee = Rc::new(Expr::Inject(
            (),
            Injection {
                constructor: ctor("Wrap"),
                arguments: vec![int(1)],
            },
        ));
        let clause = MatchClause {
            pattern: Pattern::Coproduct(
                (),
                ConstructorPattern {
                    constructor: Identifier::Free(Box::new(ctor("Wrap"))),
                    arguments: vec![Pattern::Coproduct(
                        (),
                        ConstructorPattern {
                            constructor: Identifier::Free(Box::new(ctor("Inner"))),
                            arguments: vec![Pattern::Bind((), Identifier::Bound(0))],
                        },
                    )],
                },
            ),
            consequent: var(0),
        };
        let e = Expr::Deconstruct(
            (),
            Deconstruct {
                scrutinee,
                match_clauses: vec![clause],
            },
        );
        assert!(matches!(simplify(e), Expr::Deconstruct(..)));
    }
}
