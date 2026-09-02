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
        Literal, ProductElement, Projection, Record, RecordUpdate, RecordUpdateField, Segment,
        SelfReferential, Sequence, Tree, Tuple, TypeAscription,
        namer::{Identifier, QualifiedName, Symbol, TermSymbol},
        pattern::{ConstructorPattern, MatchClause, Pattern, StructPattern, TuplePattern},
    },
    lexer::BindingOperator,
    phase,
    typer::{MetaVariable, Substitutable, Substitutions, Type, TypeInfo, Types},
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
/// 100 was the knee + ~30 nodes of margin for those benchmarks.
///
/// RAISED 100 -> 200 (2026-08-30). The note above claimed raising it "changes NOTHING on any
/// benchmark", the remaining un-inlined bodies being recursive rather than oversized. That is
/// no longer true: `billions`' `parse_temperature` is non-recursive and gated purely by size,
/// and inlining it lets its multiple-return tuple meet its destructuring and cancel.
///
/// Tune this against ALLOCATION, not wall time. Wall conflates this inliner with clang's, and
/// the two are not interchangeable -- clang cannot remove a `gc_new`, so only this pass can
/// cancel a construct/destruct pair. These are HISTORICAL, same-revision A/B figures from the
/// 2026-08-30 sweep, not totals for the current pipeline (later work reduced `billions` much
/// further). On wall the sweep looked like noise (7.42/7.23/7.29/7.30/7.40s at
/// 100/200/300/600/1200); on allocation it had a sharp knee and then a fixpoint:
///   billions      100: 37086 MB / 1.26 bn objs / 144 GCs
///                 200: 32966 MB / 1.08 bn objs / 128 GCs
///                 300, 600, 1200: identical to 200
///   binary_codec, utf8_get, flat_records: identical at 100/200/400/800 (already saturated)
/// So 200 is the smallest value reaching the fixpoint. Beyond it there is nothing left to
/// cancel and the extra body size only costs compile time (mc 7.3 -> 7.5s) and, at 1200, wall.
const INLINE_BUDGET: usize = 200;
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
            base_imports,
            module_imports,
            scope_roots,
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
                (
                    Inlinables::default(),
                    Inlinables::default(),
                    HashSet::default(),
                )
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
                            let safe = fusion_safe(&fused);
                            if std::env::var_os("DUMP_FUSION").is_some() {
                                eprintln!("[fusion] {name}  fusion_safe={safe}");
                                if !safe {
                                    let mut live = Vec::new();
                                    let mut found = Vec::new();
                                    scope_collisions(&fused, &mut live, &mut found);
                                    found.dedup();
                                    for line in found.iter().take(6) {
                                        eprintln!("[fusion]   COLLISION: {line}");
                                    }
                                }
                            }
                            if safe {
                                fused
                            } else {
                                simplify_term(body, &leaf_inlinables)
                            }
                        };
                        if dump
                            .as_deref()
                            .is_some_and(|f| name.to_string().contains(f))
                        {
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
            base_imports,
            module_imports,
            scope_roots,
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
fn simplify_term(
    body: Expr<TypeInfo, Identifier>,
    inlinables: &Inlinables<TypeInfo>,
) -> Expr<TypeInfo, Identifier> {
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
    // `recursive` above answers "may we inline INTO this term?" -- fusing an effectful
    // combinator into a loop is the space leak `fusion_safe` exists to police. It is the
    // WRONG question for "may this term be inlined elsewhere?", and using it for both is
    // why `Cheeky_Map.modify` never inlines: `modify` is not recursive, it merely CONTAINS
    // a local tail-recursive probe loop, which loopifies to a `for(;;)` and comes along
    // intact when the body is spliced.
    //
    // For the inliner to diverge, unfolding `f` must reintroduce a call to `f` -- that is,
    // `f` must reference itself by FREE NAME, which is exactly `reaches_self`. A local
    // `RecursiveLambda` refers to itself through a `Bound` level, self-contained inside the
    // spliced body, so it can never loop the inliner. Size is policed separately by
    // `within_budget`, and inlining into loops by `guard_loops`.
    //
    // `MARM_INLINE_LOCAL_LOOPS` frees terms judged by the narrow rule. Panel-green at
    // 85/87 with it fully on (`*`), and byte-identical with it unset.
    //
    // What it buys: `Cheeky_Map.modify` and `FNV1a.hash` become inlinable, which is the
    // precondition for ever unboxing 1BRC's per-row slice -- the slice's producer and its
    // consumers have to end up in ONE body before any escape analysis can see them.
    //
    // What still blocks that: actually splicing `modify` into the row loop also needs
    // inlining INTO a loop, i.e. `MARM_INLINE_LOOPS=1`, and THAT is independently broken --
    // 83/87 on the panel with it alone, no flag of ours involved. Fix that first.
    //
    // Value is a comma-separated list of name substrings, or `*` for every term. Only a
    // matching term is judged by the narrow rule; everything else keeps the conservative
    // `recursive` exclusion. Selective on purpose: it lets a single term be freed and
    // measured without betting the whole program on the narrow predicate being right.
    let local_loops = std::env::var("MARM_INLINE_LOCAL_LOOPS").ok();
    let unfold_hazard: HashSet<QualifiedName> = match local_loops.as_deref() {
        None => recursive.clone(),
        Some(pattern) => terms
            .iter()
            .filter(|(name, body)| {
                let text = name.to_string();
                let freed = pattern == "*"
                    || pattern.split(',').any(|p| !p.is_empty() && text.contains(p));
                if freed {
                    // narrow rule: only genuine self-recursion is a hazard
                    reaches_self(name, &dependencies) || is_self_recursive(body)
                } else {
                    recursive.contains(*name)
                }
            })
            .map(|(name, _)| (*name).clone())
            .collect(),
    };
    if std::env::var_os("DUMP_INLINE_EXCLUSION").is_some() {
        let budget = inline_budget();
        for (name, body) in &terms {
            eprintln!(
                "[inline?] {name}  recursive={} self_rec={} reaches_self={} hazard={} within_budget={}",
                recursive.contains(*name),
                is_self_recursive(body),
                reaches_self(name, &dependencies),
                unfold_hazard.contains(*name),
                within_budget(body, budget)
            );
        }
    }

    let budget = inline_budget();
    let inlinable = |name: &QualifiedName, body: &phase::Expr<Types>| {
        // This public wrapper is a compiler-recognised diagnostic boundary. Keeping
        // the call intact preserves its caller's source annotation for codegen.
        if name.to_string().ends_with("Prelude.omg_wtf_bbq") {
            return false;
        }
        // A nullary constructor's term is `Inject(C, [])` -- a shared, immutable value.
        // `free_variables` counts the constructor name (its tag), so the term looks
        // self-referential and lands in `recursive`; but unfolding it yields another
        // `Inject(C, [])` that references nothing, so it can never loop the inliner.
        // Inlining it is what lets a `deconstruct` whose scrutinee is such a singleton
        // (e.g. an `Ordering` flowing out of `compare` after case-of-`if` commuting)
        // see a known constructor and collapse. So keep it regardless of `recursive`.
        is_nullary_injection(body) || (within_budget(body, budget) && !unfold_hazard.contains(name))
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
/// Is this term ITSELF recursive, as opposed to merely CONTAINING a recursive function?
///
/// The distinction is the whole point. `Tree_Map.insert` IS recursive: its body is a root
/// `RecursiveLambda` whose self-binder it uses, so unfolding it splices a copy of a
/// recursive function -- which the inliner has no business doing. `Cheeky_Map.modify` and
/// `FNV1a.hash` merely CONTAIN a local tail-recursive loop nested inside an ordinary lambda
/// chain; that loop loopifies to a `for(;;)` and travels intact when the body is spliced.
///
/// `reaches_self` alone cannot make this call: direct recursion is expressed as a `Bound`
/// self-reference inside the `RecursiveLambda`, invisible to the free-name graph. So this
/// checks the ROOT specifically -- `contains_recursion` searches the whole tree and so
/// cannot tell the two apart.
fn is_self_recursive<A>(body: &Expr<A, Identifier>) -> bool {
    // A top-level symbol's own self-binder is ALWAYS level 0 -- it is the outermost thing
    // the term introduces. A local loop is introduced further in and receives whatever
    // level was next, which is necessarily > 0. So "is this term itself recursive?" is
    // "does it introduce a self-referential lambda AT LEVEL 0?", and that survives however
    // specialization has wrapped the body -- which the spine/root/peel checks did not,
    // because `build_inlinables` runs once per pass and reshapes the term between them.
    //
    // `contains_recursion` asks the weaker question (is there ANY self-referential lambda
    // anywhere), which is right for "may we inline INTO this" and wrong for this.
    fn search<A>(expr: &Expr<A, Identifier>) -> bool {
        if let Expr::RecursiveLambda(
            _,
            SelfReferential {
                own_name: Identifier::Bound(0),
                lambda,
            },
        ) = expr
        {
            if mentions_level(&lambda.body, 0) {
                return true;
            }
        }
        children(expr).into_iter().any(|c| search(c))
    }
    search(body)
}

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
/// Debug check: does any binder introduce a de Bruijn LEVEL that an enclosing binder
/// already holds? With levels-as-depth, sibling scopes legitimately reuse a level, so only
/// re-binding along one PATH is wrong -- and that is exactly what a splice that failed to
/// shift produces: the callee's levels 0.. land inside a caller that already bound them.
/// Reported under `DUMP_FUSION=1`; costs nothing otherwise.
fn scope_collisions<A>(expr: &Expr<A, Identifier>, live: &mut Vec<usize>, out: &mut Vec<String>) {
    let mut note = |live: &Vec<usize>, l: &usize, what: &str, out: &mut Vec<String>| {
        if live.contains(l) {
            out.push(format!("{what} re-binds level {l} (already bound by an ancestor)"));
        }
    };
    match expr {
        Expr::Lambda(_, Lambda { parameter, body }) => {
            if let Identifier::Bound(l) = parameter {
                note(live, l, "lambda parameter", out);
                live.push(*l);
                scope_collisions(body, live, out);
                live.pop();
                return;
            }
            scope_collisions(body, live, out);
        }
        Expr::RecursiveLambda(_, SelfReferential { own_name, lambda }) => {
            let mut pushed = 0;
            if let Identifier::Bound(o) = own_name {
                note(live, o, "recursive-lambda self-binder", out);
                live.push(*o);
                pushed += 1;
            }
            if let Identifier::Bound(p) = &lambda.parameter {
                note(live, p, "recursive-lambda parameter", out);
                live.push(*p);
                pushed += 1;
            }
            scope_collisions(&lambda.body, live, out);
            for _ in 0..pushed {
                live.pop();
            }
        }
        Expr::Let(_, Binding { binder, bound, body, .. }) => {
            scope_collisions(bound, live, out);
            if let Identifier::Bound(l) = binder {
                note(live, l, "let binder", out);
                live.push(*l);
                scope_collisions(body, live, out);
                live.pop();
                return;
            }
            scope_collisions(body, live, out);
        }
        _ => {
            for child in children(expr) {
                scope_collisions(child, live, out);
            }
        }
    }
}

fn fusion_safe<A>(body: &Expr<A, Identifier>) -> bool {
    // EVERY recursive-lambda introduction has to survive fusion in tail position, not just
    // one at the root. The old form matched the root only and returned `false` for anything
    // else, so a term that merely CONTAINS local loops -- `Cheeky_Map.modify`, `FNV1a.hash`,
    // `process_chunk_into`, i.e. most functional code -- could never pass and always fell
    // back to `leaf_inlinables`. That is why inlining into loops looked like it needed the
    // blunt `MARM_INLINE_LOOPS` escape hatch: the safe path was rejecting by construction
    // rather than by analysis.
    //
    // For each introduction, check the level IT received against its own body: a top-level
    // term's own recursion binds level 0, a local loop binds whatever came next. Same rule,
    // applied everywhere instead of once.
    fn go<A>(expr: &Expr<A, Identifier>) -> bool {
        let here = match expr {
            Expr::RecursiveLambda(
                _,
                SelfReferential {
                    own_name: Identifier::Bound(level),
                    lambda,
                },
            ) => {
                let ok = self_calls_all_tail(&lambda.body, *level, true, true);
                if !ok && std::env::var_os("DUMP_FUSION").is_some() {
                    eprintln!("[fusion]   non-tail self-call at level {level}");
                }
                ok
            }
            _ => true,
        };
        here && children(expr).into_iter().all(|c| go(c))
    }
    go(body)
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
            // A NESTED recursive lambda -- the term's OWN root one is consumed by
            // `fusion_safe` before this walk starts, so anything reached here is a local
            // loop inside the body. It is a deferred closure exactly like an inner
            // `Lambda`, so an outer self-call occurring inside it is NOT a tail call of
            // the outer term: it runs with that closure's frame still live. Inheriting
            // `tail`/`leading` here judged such a call safe, the fused body was kept, and
            // the outer recursion stopped being a tail call -- one stack frame per
            // iteration. Caught by `32_trees` (1e6 `fill` iterations) only once bodies
            // containing local loops became inlinable at all.
            self_calls_all_tail(&lambda.body, level, false, false)
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
pub(crate) fn children<A, Id>(expr: &Expr<A, Id>) -> Vec<&Tree<A, Id>> {
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
        Expr::RecordUpdate(_, update) => {
            let mut children = vec![&update.base];
            children.extend(update.fields.iter().map(|field| &field.value));
            children
        }
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
struct Inliner<'a> {
    bodies: &'a Inlinables<TypeInfo>,
    fuel: Cell<usize>,
    changed: Cell<bool>,
}

impl Inliner<'_> {
    /// If `tree` is an inlinable `Free`, return its body relocated to `depth`.
    fn try_head(
        &self,
        tree: &Tree<TypeInfo, Identifier>,
        depth: usize,
    ) -> Option<Tree<TypeInfo, Identifier>> {
        let Expr::Variable(call_info, Identifier::Free(name)) = &**tree else {
            return None;
        };
        let body = self.bodies.get(name)?;
        if self.fuel.get() == 0 {
            return None;
        }
        self.fuel.set(self.fuel.get() - 1);
        self.changed.set(true);
        let instantiated = if std::env::var_os("MARM_NO_TYPED_INLINE").is_some() {
            (**body).clone()
        } else {
            inline_type_substitutions(&body.annotation().inferred_type, &call_info.inferred_type)
                .map_or_else(
                    || (**body).clone(),
                    |substitutions| (**body).apply(&substitutions),
                )
        };
        Some(Rc::new(shift(&Rc::new(instantiated), 0, depth)))
    }

    /// Inline `tree` at absolute binder depth `depth` (the number of enclosing
    /// binders; equivalently the level the next binder would receive).
    fn inline(
        &self,
        tree: &Tree<TypeInfo, Identifier>,
        depth: usize,
    ) -> Tree<TypeInfo, Identifier> {
        let go = |t: &Tree<TypeInfo, Identifier>, d: usize| self.inline(t, d);

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
            Expr::RecordUpdate(a, update) => Expr::RecordUpdate(
                a.clone(),
                RecordUpdate {
                    base: go(&update.base, depth),
                    fields: update
                        .fields
                        .iter()
                        .map(|field| RecordUpdateField {
                            path: field.path.clone(),
                            indices: field.indices.clone(),
                            arities: field.arities.clone(),
                            value: go(&field.value, depth),
                        })
                        .collect(),
                    field_order: update.field_order.clone(),
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

/// Instantiate annotations in an inlined polymorphic body from the type of the
/// particular free-variable occurrence being unfolded. Elaboration has already
/// checked this application, so this pass only needs directional pattern matching;
/// it must not invent new unification constraints.
fn inline_type_substitutions(template: &Type, concrete: &Type) -> Option<Substitutions> {
    fn match_pattern(
        template: &Type,
        concrete: &Type,
        bindings: &mut HashMap<MetaVariable, Type>,
    ) -> Option<()> {
        match (template, concrete) {
            (Type::Variable(variable), concrete) => match bindings.get(variable) {
                Some(previous) if previous != concrete => None,
                Some(_) => Some(()),
                None => {
                    bindings.insert(variable.clone(), concrete.clone());
                    Some(())
                }
            },
            (
                Type::Apply {
                    constructor: tc,
                    argument: ta,
                    ..
                },
                Type::Apply {
                    constructor: cc,
                    argument: ca,
                    ..
                },
            ) => {
                match_pattern(tc, cc, bindings)?;
                match_pattern(ta, ca, bindings)
            }
            (
                Type::Arrow {
                    domain: td,
                    codomain: tc,
                    ..
                },
                Type::Arrow {
                    domain: cd,
                    codomain: cc,
                    ..
                },
            ) => {
                match_pattern(td, cd, bindings)?;
                match_pattern(tc, cc, bindings)
            }
            (Type::Array(template), Type::Array(concrete)) => {
                match_pattern(template, concrete, bindings)
            }
            (Type::Tuple(template), Type::Tuple(concrete))
                if template.arity() == concrete.arity() =>
            {
                for (template, concrete) in template.elements().iter().zip(concrete.elements()) {
                    match_pattern(template, concrete, bindings)?;
                }
                Some(())
            }
            (template, concrete) if template == concrete => Some(()),
            _ => None,
        }
    }

    fn arrow_arity(mut function: &Type) -> usize {
        let mut arity = 0;
        while let Type::Arrow { codomain, .. } = function {
            arity += 1;
            function = codomain;
        }
        arity
    }

    let mut bindings = HashMap::new();
    if match_pattern(template, concrete, &mut bindings).is_some() {
        return Some(bindings.into_iter().collect::<Vec<_>>().into());
    }

    // A constrained definition (`Memory_Layout a |- Mutable_Array a -> ...`) carries a
    // leading dictionary arrow per premise, but the occurrence being unfolded records
    // only the source type. Matching those two directly fails on the very first domain
    // -- and the silent fallback then inlines the body with its *polymorphic*
    // annotations, so codegen lowers it at the type variable instead of the ground type
    // the call site fixed. Peel exactly the premise prefix and match the source types.
    let premises = arrow_arity(template).checked_sub(arrow_arity(concrete))?;
    let mut source = template;
    for _ in 0..premises {
        let Type::Arrow { codomain, .. } = source else {
            return None;
        };
        source = codomain;
    }
    let mut bindings = HashMap::new();
    match_pattern(source, concrete, &mut bindings)?;
    Some(bindings.into_iter().collect::<Vec<_>>().into())
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
        Pattern::Struct(_, StructPattern { fields }) => fields
            .iter()
            .filter_map(|(_, p)| pattern_min_level(p))
            .min(),
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
                && (clauses_are_small(&deconstruct.match_clauses)
                    || matches!(&*deconstruct.scrutinee, Expr::Deconstruct(_, inner)
                        if inner.match_clauses.len() == 1)) =>
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
        Expr::RecordUpdate(a, update) => Expr::RecordUpdate(
            a.clone(),
            RecordUpdate {
                base: go(&update.base, depth),
                fields: update
                    .fields
                    .iter()
                    .map(|field| RecordUpdateField {
                        path: field.path.clone(),
                        indices: field.indices.clone(),
                        arities: field.arities.clone(),
                        value: go(&field.value, depth),
                    })
                    .collect(),
                field_order: update.field_order.clone(),
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
            elimination_spine_head_is(&d.scrutinee, level) && count_level_uses(body, level) == 1
        }
        Expr::Project(_, p) => {
            elimination_spine_head_is(&p.base, level) && count_level_uses(body, level) == 1
        }
        _ => false,
    }
}

/// Whether the value eliminated by `tree` is specifically `level`.  This is stricter
/// than [`eliminated_head`]: that helper answers whether all occurrences are in safe
/// elimination positions and therefore quite correctly accepts an unrelated variable.
/// Effectful forwarding, however, must prove that the target binder is the value evaluated
/// *first*; accepting any variable here can move the target's effect into a later match arm.
fn elimination_spine_head_is<A>(tree: &Tree<A, Identifier>, level: usize) -> bool {
    match &**tree {
        Expr::Variable(_, Identifier::Bound(k)) => *k == level,
        Expr::Apply(_, Apply { function, .. }) => elimination_spine_head_is(function, level),
        Expr::Project(_, Projection { base, .. }) => elimination_spine_head_is(base, level),
        Expr::Deconstruct(_, Deconstruct { scrutinee, .. }) => {
            elimination_spine_head_is(scrutinee, level)
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

        // The record twin of the tuple case: a record LITERAL taken apart by a record
        // PATTERN. `{ City := c; Temperature := t }` immediately consumed by
        // `λ({ City: c; Temperature: t }). …` builds the record only to project it back
        // out on the next line -- the same construct/deconstruct pair, one allocation.
        Expr::Record(_, record) => select_record_clause(a, scrutinee, record, match_clauses),

        // A tuple-valued `if` taken apart by a tuple pattern -- the shape every
        // multiple-return produces: `let i, w = if neg then 2, x else 1, y`.
        Expr::If(_, ite) => split_tuple_if(a, ite, match_clauses),

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

/// `deconstruct (if p then (x₁..xₙ) else (y₁..yₙ)) into (a₁..aₙ) -> body`
/// becomes `let a₁ = if p then x₁ else y₁ in … let aₙ = … in body`.
///
/// The tuple is built only to be taken apart on the very next line, so this removes the
/// allocation outright. Case-of-`if` commuting cannot reach this shape: it would copy
/// `body` into BOTH branches, and `clauses_are_small` rightly forbids that when `body`
/// is the whole rest of the function -- which is exactly the situation a multiple-return
/// tuple creates. Splitting per component moves only the components, never the body.
///
/// The predicate is duplicated once per component, so it is restricted to a variable or
/// a constant: free to re-read, and no effect or work can be duplicated. `build_let_chain`
/// enforces that the pattern binds a contiguous run of De Bruijn levels, so the let-chain
/// lands on exactly the levels the tuple pattern bound.
fn split_tuple_if<A>(
    a: &A,
    ite: &IfThenElse<A, Identifier>,
    clauses: &[MatchClause<A, Identifier>],
) -> Option<Expr<A, Identifier>>
where
    A: Clone,
{
    let (Expr::Tuple(_, consequent), Expr::Tuple(_, alternate)) =
        (&*ite.consequent, &*ite.alternate)
    else {
        return None;
    };
    if consequent.elements.len() != alternate.elements.len() {
        return None;
    }

    // A tuple pattern is irrefutable, so the first clause is the one selected.
    let clause = clauses.first()?;
    let Pattern::Tuple(_, TuplePattern { elements }) = &clause.pattern else {
        return None;
    };
    if elements.len() != consequent.elements.len() {
        return None;
    }

    let split = |predicate: &Tree<A, Identifier>,
                 patterns: &[Pattern<A, Identifier>],
                 body: &Tree<A, Identifier>| {
        let components = consequent
            .elements
            .iter()
            .zip(alternate.elements.iter())
            .map(|(then_branch, else_branch)| {
                Rc::new(Expr::If(
                    a.clone(),
                    IfThenElse {
                        predicate: predicate.clone(),
                        consequent: then_branch.clone(),
                        alternate: else_branch.clone(),
                    },
                ))
            })
            .collect::<Vec<_>>();
        build_let_chain(a, &components, patterns, body)
    };

    // An atom predicate is free to re-read, so use it directly and introduce no binder.
    if matches!(
        &*ite.predicate,
        Expr::Variable(..) | Expr::Constant(..) | Expr::InvokeBridge(..)
    ) {
        return split(&ite.predicate, elements, &clause.consequent);
    }

    // Otherwise bind the predicate once and split against that. This is not merely a
    // guard-dodge: evaluating `p` a single time is what the original `if` did, so an
    // effectful or expensive predicate is preserved exactly -- whereas duplicating it
    // per component would re-run it. `let value, consumed = if <byte read> then …` is
    // the case that matters, and it is the common one: a multiple return whose choice
    // is made by a real test rather than a variable already in hand.
    //
    // The new binder takes the level the tuple pattern's FIRST binder had; the pattern's
    // binders and the body therefore move up by one (`shift_id`/`shift` from that level,
    // the same idiom as the let-float rule above). The branch components sit at the
    // scrutinee's depth and can only mention binders OUTSIDE the pattern, so they are
    // unaffected by a shift starting at it.
    let base = pattern_min_level(&clause.pattern)?;
    let shifted_patterns = elements
        .iter()
        .map(|p| walk_pattern(p, &|id| shift_id(id, base, 1)))
        .collect::<Vec<_>>();
    let shifted_body = Rc::new(shift(&clause.consequent, base, 1));

    let bound_predicate = Rc::new(Expr::Variable(
        ite.predicate.annotation().clone(),
        Identifier::Bound(base),
    ));
    let inner = split(&bound_predicate, &shifted_patterns, &shifted_body)?;

    Some(Expr::Let(
        a.clone(),
        Binding {
            binder: Identifier::Bound(base),
            operator: BindingOperator::Identity,
            bound: ite.predicate.clone(),
            body: Rc::new(inner),
        },
    ))
}

/// Cancel a record literal against the record pattern that immediately takes it apart.
///
/// The components are ordered by the PATTERN's field order, not the record literal's: the
/// namer assigns De Bruijn levels walking the pattern, so that is the order
/// `build_let_chain` needs to see them in for its contiguous-level check to hold.
///
/// Requires the pattern to bind every field. A partial pattern would let a field's
/// expression be dropped, which is only sound if it is pure -- not worth assuming here,
/// and the shape that matters (a record built purely to be destructured) binds all of them.
fn select_record_clause<A>(
    a: &A,
    scrutinee: &Tree<A, Identifier>,
    record: &Record<A, Identifier>,
    clauses: &[MatchClause<A, Identifier>],
) -> Option<Expr<A, Identifier>>
where
    A: Clone,
{
    // A record pattern is irrefutable, so the first clause is the one selected.
    let clause = clauses.first()?;
    match &clause.pattern {
        Pattern::Bind(_, Identifier::Bound(level)) => {
            Some(bind_whole(a, *level, scrutinee, &clause.consequent))
        }
        Pattern::Struct(_, StructPattern { fields }) => {
            if fields.len() != record.fields.len() {
                return None;
            }
            let mut values = Vec::with_capacity(fields.len());
            let mut patterns = Vec::with_capacity(fields.len());
            for (name, field_pattern) in fields {
                let value = record.fields.iter().find(|(n, _)| n == name)?.1.clone();
                values.push(value);
                patterns.push(field_pattern.clone());
            }
            build_let_chain(a, &values, &patterns, &clause.consequent)
        }
        _ => None,
    }
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
        Expr::RecordUpdate(a, update) => Expr::RecordUpdate(
            a.clone(),
            RecordUpdate {
                base: go(&update.base),
                fields: update
                    .fields
                    .iter()
                    .map(|field| RecordUpdateField {
                        path: field.path.clone(),
                        indices: field.indices.clone(),
                        arities: field.arities.clone(),
                        value: go(&field.value),
                    })
                    .collect(),
                field_order: update.field_order.clone(),
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

// =========================== Strict-IO deforestation (worker/wrapper) ===========================
//
// The [[io-deforest-simplifier]] rules already collapse the `Suspend` ceremony of *straight-line*
// IO. What they structurally cannot reach is a recursive IO loop: `fill`'s self-call lives inside
// `bind`'s continuation (`Suspend (λ_. … #self …)`), so forcing the recursive result is the real
// tail -- inlining `bind` there just makes the C recursion non-tail (a stack overflow) without
// removing an allocation. See `notes/deforest-io.md`.
//
// This pass performs force-local worker/wrapper conversion. At every exact `run` marker
// `deconstruct E into Suspend v -> (v ())`, it opens the actual typed bodies of small acyclic
// functions, pushes the force into the resulting concrete `Suspend` program, and synthesises
// strict α-returning workers for local recursive IO functions whose uses are all run-only. It
// assigns no semantics to `bind`, `pure`, or any other library name. Top-level definitions are
// never rewritten: escaping actions and nullary IO CAFs retain their ordinary lazy wrappers.
// Every shape that cannot be proved safe falls back to an unchanged force marker, and the later
// `simplify()` finishes the adjacent beta/case cancellation.

pub(crate) fn deforest_io_on() -> bool {
    let Some(value) = std::env::var_os("MARM_DEFOREST_IO") else {
        return true;
    };
    value.to_str().is_none_or(|value| {
        let value = value.trim();
        !value.is_empty()
            && !["0", "false", "off", "no"]
                .iter()
                .any(|disabled| value.eq_ignore_ascii_case(disabled))
    })
}

/// Strict workers are copied only at an actual `run` site and do not participate
/// in the ordinary inliner's multi-round fixpoint, so they can be somewhat larger
/// than [`INLINE_BUDGET`] without risking combinatorial expansion.  The bound still
/// keeps this local-worker implementation from duplicating arbitrarily large API
/// functions; 512 comfortably admits normal IO drivers containing a local loop
/// (`billions.process_file_bytes` is 173 nodes after the first simplify pass).
const STRICT_IO_INLINE_BUDGET: usize = 512;

/// Whether a term's type is IO-returning: peel the parameter arrows, then check the result is the
/// `IO` type -- a `Suspend`-carrying coproduct, or an application headed by the `Prelude.IO`
/// constructor. Only such local function values are strict-worker candidates; a pure recursive
/// helper (e.g. `List.concat`) must never be run-transformed.
fn returns_io(ty: &Type) -> bool {
    let mut result = ty;
    while let Type::Arrow { codomain, .. } = result {
        result = codomain;
    }
    fn io_headed(t: &Type) -> bool {
        match t {
            Type::Apply { constructor, .. } => io_headed(constructor),
            Type::Constructor(qn) => *qn == crate::typer::io_type_name(),
            // Before it is applied, `IO` appears elaborated as its coproduct (the `Suspend`
            // constructor); recognise that shape too.
            Type::Coproduct(cop) => cop
                .constructors()
                .any(|(c, _)| *c == crate::typer::suspend_constructor_name()),
            _ => false,
        }
    }
    io_headed(result)
}

/// A strict worker can replace a locally bound function value `f : A -> IO B` while preserving
/// an inert lambda at the binding. A nullary action `main : IO B` is a value rather than a worker
/// candidate: stripping its wrapper would execute it merely by evaluating the binding.
fn is_io_function(ty: &Type) -> bool {
    matches!(ty, Type::Arrow { .. }) && returns_io(ty)
}

/// Strip the `IO` wrapper off a type: `IO α -> α`. `run E : α` where `E : IO α`, so this is the
/// annotation a synthesised force marker carries. Unknown shapes are left untouched (harmless: the
/// node it annotates is transient and eliminated by `simplify()` once the box cancels).
fn strip_io(ty: &Type) -> Type {
    match ty {
        Type::Apply { argument, .. } => (**argument).clone(),
        _ => ty.clone(),
    }
}

/// Recognise a `run` marker -- `unsafe_run_IO`'s inlined force -- i.e. a single-clause deconstruct
/// `deconstruct E into Suspend v -> (v ())` where the sole bound thunk is applied (to `Unit`) and
/// used nowhere else. Returns the forced expression `E` and the clause (reused as the annotation
/// template when synthesising fresh force markers deeper in).
fn as_run_marker<'a>(
    expr: &'a Expr<TypeInfo, Identifier>,
) -> Option<(
    &'a Tree<TypeInfo, Identifier>,
    &'a MatchClause<TypeInfo, Identifier>,
)> {
    let Expr::Deconstruct(_, deconstruct) = expr else {
        return None;
    };
    if deconstruct.match_clauses.len() != 1 {
        return None;
    }
    let clause = &deconstruct.match_clauses[0];
    let Pattern::Coproduct(_, cp) = &clause.pattern else {
        return None;
    };
    let Identifier::Free(qn) = &cp.constructor else {
        return None;
    };
    if **qn != crate::typer::suspend_constructor_name() || cp.arguments.len() != 1 {
        return None;
    }
    let Pattern::Bind(_, Identifier::Bound(v)) = &cp.arguments[0] else {
        return None;
    };
    // The consequent must apply exactly the bound thunk: `(v ())`.
    let Expr::Apply(_, ap) = &*clause.consequent else {
        return None;
    };
    let Expr::Variable(_, Identifier::Bound(k)) = &*ap.function else {
        return None;
    };
    if k != v {
        return None;
    }
    Some((&deconstruct.scrutinee, clause))
}

/// Recognise the more general force eliminator left after simplifying a mapped
/// action:
///
/// ```text
/// deconstruct E into Suspend thunk -> K (thunk ())
/// ```
///
/// where the thunk binder occurs exactly once.  `K` is ordinary pure Marmelade
/// expression context (most commonly a data constructor such as `Return`).  We
/// must keep the strict computation at the `thunk ()` occurrence rather than
/// hoisting it to the scrutinee, since `K` may contain other computations whose
/// evaluation order is observable through their eventual IO actions.
fn as_embedded_run<'a>(
    expr: &'a Expr<TypeInfo, Identifier>,
) -> Option<(
    &'a Tree<TypeInfo, Identifier>,
    &'a MatchClause<TypeInfo, Identifier>,
    usize,
)> {
    let Expr::Deconstruct(_, deconstruct) = expr else {
        return None;
    };
    if deconstruct.match_clauses.len() != 1 {
        return None;
    }
    let clause = &deconstruct.match_clauses[0];
    let Pattern::Coproduct(_, cp) = &clause.pattern else {
        return None;
    };
    let Identifier::Free(qn) = &cp.constructor else {
        return None;
    };
    if **qn != crate::typer::suspend_constructor_name() || cp.arguments.len() != 1 {
        return None;
    }
    let Pattern::Bind(_, Identifier::Bound(thunk)) = &cp.arguments[0] else {
        return None;
    };
    if count_level_uses(&clause.consequent, *thunk) != 1 {
        return None;
    }

    fn contains_force(e: &Expr<TypeInfo, Identifier>, thunk: usize) -> bool {
        match e {
            Expr::Apply(_, Apply { function, .. }) if matches!(&**function, Expr::Variable(_, Identifier::Bound(k)) if *k == thunk) => {
                true
            }
            other => children(other)
                .into_iter()
                .any(|child| contains_force(child, thunk)),
        }
    }
    contains_force(&clause.consequent, *thunk).then_some((&deconstruct.scrutinee, clause, *thunk))
}

/// Whether every occurrence of the local function `target` is consumed in a position
/// where its resulting `IO` action is immediately run.  Calls in a run position are
/// inspected by opening the actual typed function body, not by assigning special
/// meaning to library names such as `bind`: after beta/case reduction, the concrete
/// `Suspend` construction tells us where demand flows.  A definition-cycle or an
/// unavailable/large body simply stops the proof and therefore keeps the local wrapper.
fn local_io_function_is_run_only(
    e: &Expr<TypeInfo, Identifier>,
    target: usize,
    running: bool,
    depth: usize,
    definitions: &Inlinables<TypeInfo>,
    expanding: &mut HashSet<QualifiedName>,
) -> bool {
    if let Some((scrutinee, _)) = as_run_marker(e) {
        return local_io_function_is_run_only(
            scrutinee,
            target,
            true,
            depth,
            definitions,
            expanding,
        );
    }

    let check = |expr: &Expr<TypeInfo, Identifier>, running, depth, expanding: &mut HashSet<_>| {
        local_io_function_is_run_only(expr, target, running, depth, definitions, expanding)
    };
    match e {
        Expr::Variable(_, Identifier::Bound(level)) => *level != target || running,
        Expr::If(_, ite) => {
            check(&ite.predicate, false, depth, expanding)
                && check(&ite.consequent, running, depth, expanding)
                && check(&ite.alternate, running, depth, expanding)
        }
        Expr::Let(_, binding) => {
            check(&binding.bound, false, depth, expanding)
                && check(&binding.body, running, depth + 1, expanding)
        }
        Expr::Deconstruct(_, deconstruct) => {
            check(&deconstruct.scrutinee, false, depth, expanding)
                && deconstruct.match_clauses.iter().all(|clause| {
                    check(
                        &clause.consequent,
                        running,
                        depth + pattern_binder_count(&clause.pattern),
                        expanding,
                    )
                })
        }
        Expr::Apply(..) if running => {
            let tree = Rc::new(e.clone());
            let (head, args) = peel_apply_spine(&tree);
            let ordinary_args = |args: &[Tree<TypeInfo, Identifier>],
                                 expanding: &mut HashSet<_>| {
                args.iter().all(|arg| check(arg, false, depth, expanding))
            };
            match head {
                Expr::Variable(_, Identifier::Bound(level)) if *level == target => {
                    ordinary_args(&args, expanding)
                }
                Expr::Variable(_, Identifier::Free(name))
                    if definitions.contains_key(&**name) && expanding.insert((**name).clone()) =>
                {
                    let body = &definitions[&**name];
                    let instantiated = inline_type_substitutions(
                        &body.annotation().inferred_type,
                        &head.annotation().inferred_type,
                    )
                    .map_or_else(
                        || (**body).clone(),
                        |substitutions| (**body).apply(&substitutions),
                    );
                    let relocated = shift(&Rc::new(instantiated), 0, depth);
                    let opened = simplify_expr(replace_spine_head(e, relocated));
                    let safe = check(&opened, true, depth, expanding);
                    expanding.remove(&**name);
                    safe
                }
                Expr::Lambda(_, lambda) => {
                    ordinary_args(&args, expanding)
                        && check(&lambda.body, true, depth + 1, expanding)
                }
                Expr::RecursiveLambda(_, recursive) => {
                    ordinary_args(&args, expanding)
                        && check(&recursive.lambda.body, true, depth + 2, expanding)
                }
                _ => children(e)
                    .into_iter()
                    .all(|child| check(child, false, depth, expanding)),
            }
        }
        Expr::Lambda(_, lambda) => check(&lambda.body, false, depth + 1, expanding),
        Expr::RecursiveLambda(_, recursive) => {
            check(&recursive.lambda.body, false, depth + 2, expanding)
        }
        _ => children(e)
            .into_iter()
            .all(|child| check(child, false, depth, expanding)),
    }
}

/// Rebuild an application spine, replacing only its innermost head and reusing every original
/// `Apply` annotation and argument. `((h a) b) c` with new head `h'` becomes `((h' a) b) c`.
fn replace_spine_head(
    spine: &Expr<TypeInfo, Identifier>,
    new_head: Expr<TypeInfo, Identifier>,
) -> Expr<TypeInfo, Identifier> {
    match spine {
        Expr::Apply(a, Apply { function, argument }) => Expr::Apply(
            a.clone(),
            Apply {
                function: Rc::new(replace_spine_head(function, new_head)),
                argument: argument.clone(),
            },
        ),
        _ => new_head,
    }
}

struct DeforestCtx<'a> {
    /// Small, acyclic functions whose lazy wrapper may be opened at a
    /// particular run site.  These functions themselves stay untouched: a use
    /// that stores or passes the action still receives the ordinary `IO alpha`
    /// value.  In a run position we splice a strict copy of the function body,
    /// which is the local worker half of worker/wrapper and, crucially, is safe
    /// inside a recursive driver because the `Suspend` closure disappears before
    /// the driver is closure-converted.
    strict_inlinables: &'a Inlinables<TypeInfo>,

    /// A canonical exact `Suspend thunk -> thunk ()` clause whose annotations
    /// are reused when an unrecognised action must retain a force boundary.
    force_template: &'a MatchClause<TypeInfo, Identifier>,
}

impl DeforestCtx<'_> {
    /// Walk `tree` tracking binder depth (mirroring `walk_d`'s increments); at every `run` marker,
    /// replace it with the strict form produced by `run`.
    fn map_markers(
        &self,
        tree: &Tree<TypeInfo, Identifier>,
        depth: usize,
        strict: &HashSet<usize>,
    ) -> Tree<TypeInfo, Identifier> {
        if let Some((scrutinee, template)) = as_run_marker(tree) {
            return Rc::new(self.run(scrutinee, strict, depth, template));
        }
        if let Some((scrutinee, clause, thunk_level)) = as_embedded_run(tree) {
            // Replace the sole thunk value by `lambda _. run E`, then let the
            // ordinary beta/let reducer expose `run E` at exactly the original
            // `thunk ()` position.  The wrapper lambda is a substitution device,
            // not runtime machinery: the following simplify pass removes it.
            let strict_value = Rc::new(self.run(scrutinee, strict, depth, self.force_template));
            let Pattern::Coproduct(_, constructor_pattern) = &clause.pattern else {
                unreachable!("as_embedded_run accepted a non-coproduct pattern")
            };
            let thunk_annotation = constructor_pattern.arguments[0].annotation().clone();
            let delayed = Rc::new(Expr::Lambda(
                thunk_annotation,
                Lambda {
                    parameter: Identifier::Bound(thunk_level),
                    body: Rc::new(shift(&strict_value, thunk_level, 1)),
                },
            ));
            let replaced = Rc::new(substitute_value(&clause.consequent, thunk_level, &delayed));
            return self.map_markers(&replaced, depth, strict);
        }
        let go = |t: &Tree<TypeInfo, Identifier>, d: usize| self.map_markers(t, d, strict);
        Rc::new(match &**tree {
            Expr::Variable(..)
            | Expr::InvokeBridge(..)
            | Expr::Constant(..)
            | Expr::MakeClosure(..) => (**tree).clone(),
            Expr::RecursiveLambda(a, SelfReferential { own_name, lambda }) => {
                Expr::RecursiveLambda(
                    a.clone(),
                    SelfReferential {
                        own_name: own_name.clone(),
                        lambda: Lambda {
                            parameter: lambda.parameter.clone(),
                            body: go(&lambda.body, depth + 2),
                        },
                    },
                )
            }
            Expr::Lambda(a, Lambda { parameter, body }) => Expr::Lambda(
                a.clone(),
                Lambda {
                    parameter: parameter.clone(),
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
                    binder: binder.clone(),
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
            Expr::RecordUpdate(a, update) => Expr::RecordUpdate(
                a.clone(),
                RecordUpdate {
                    base: go(&update.base, depth),
                    fields: update
                        .fields
                        .iter()
                        .map(|field| RecordUpdateField {
                            path: field.path.clone(),
                            indices: field.indices.clone(),
                            arities: field.arities.clone(),
                            value: go(&field.value, depth),
                        })
                        .collect(),
                    field_order: update.field_order.clone(),
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
                        .map(|c| MatchClause {
                            pattern: c.pattern.clone(),
                            consequent: go(&c.consequent, depth + pattern_binder_count(&c.pattern)),
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
        })
    }

    /// Produce the α-value of running the IO expression `e`. Pushes the force through control flow
    /// (`if`/`let`/`deconstruct`), restructures `bind`/`pure`, keeps strict self-calls (levels in
    /// `strict`) as tail calls, and force-inlines each recursive IO function it reaches (guarded by
    /// `in_progress` against non-termination on mutual recursion). Any unrecognised shape becomes an
    /// unchanged force marker via `force` -- the sound fallback. `template` supplies the `Suspend`
    /// constructor and inner annotations for those synthesised markers.
    fn run(
        &self,
        e: &Tree<TypeInfo, Identifier>,
        strict: &HashSet<usize>,
        depth: usize,
        template: &MatchClause<TypeInfo, Identifier>,
    ) -> Expr<TypeInfo, Identifier> {
        match &**e {
            // Control flow: the force distributes over the branches / body / arms (tail positions);
            // the scrutinee / predicate / bound are non-tail, so only carry `map_markers`.
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
                    predicate: self.map_markers(predicate, depth, strict),
                    consequent: Rc::new(self.run(consequent, strict, depth, template)),
                    alternate: Rc::new(self.run(alternate, strict, depth, template)),
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
            ) => {
                let strict_local = if let Identifier::Bound(level) = binder {
                    is_io_function(&bound.annotation().inferred_type)
                        && matches!(&**bound, Expr::Lambda(..) | Expr::RecursiveLambda(..))
                        && local_io_function_is_run_only(
                            body,
                            *level,
                            true,
                            depth + 1,
                            self.strict_inlinables,
                            &mut HashSet::new(),
                        )
                } else {
                    false
                };
                if strict_local {
                    let Identifier::Bound(level) = binder else {
                        unreachable!("guarded by strict_local")
                    };
                    let mut inner = strict.clone();
                    inner.insert(*level);
                    Expr::Let(
                        a.clone(),
                        Binding {
                            binder: binder.clone(),
                            operator: *operator,
                            bound: Rc::new(self.strictify_worker(bound, strict, depth, template)),
                            body: Rc::new(self.run(body, &inner, depth + 1, template)),
                        },
                    )
                } else {
                    Expr::Let(
                        a.clone(),
                        Binding {
                            binder: binder.clone(),
                            operator: *operator,
                            bound: self.map_markers(bound, depth, strict),
                            body: Rc::new(self.run(body, strict, depth + 1, template)),
                        },
                    )
                }
            }
            Expr::Deconstruct(
                a,
                Deconstruct {
                    scrutinee,
                    match_clauses,
                },
            ) => Expr::Deconstruct(
                a.clone(),
                Deconstruct {
                    scrutinee: self.map_markers(scrutinee, depth, strict),
                    match_clauses: match_clauses
                        .iter()
                        .map(|c| MatchClause {
                            pattern: c.pattern.clone(),
                            consequent: Rc::new(self.run(
                                &c.consequent,
                                strict,
                                depth + pattern_binder_count(&c.pattern),
                                template,
                            )),
                        })
                        .collect(),
                },
            ),
            Expr::Apply(..) => self.run_apply(e, strict, depth, template),
            _ => self.force(e, depth, template),
        }
    }

    /// `run` of an application spine. Dispatches on the spine head.
    fn run_apply(
        &self,
        e: &Tree<TypeInfo, Identifier>,
        strict: &HashSet<usize>,
        depth: usize,
        template: &MatchClause<TypeInfo, Identifier>,
    ) -> Expr<TypeInfo, Identifier> {
        let (head, _) = peel_apply_spine(e);
        match head {
            // A strict-worker self-call: the head already denotes the α-returning worker and this is
            // a tail position, so keep the spine verbatim (its arguments are pure).
            Expr::Variable(_, Identifier::Bound(k)) if strict.contains(k) => (**e).clone(),

            // A function value applied in run position (e.g. a local recursive `probe`): swap it for
            // its strict worker and keep the application; `simplify()` betas the arguments in. A
            // local `probe` stays a local recursive lambda (its recursion is shallow -- a probe
            // chain -- so it needs no tail-call loopification, unlike the deep top-level driver).
            Expr::Lambda(..) | Expr::RecursiveLambda(..) => {
                let worker = self.strictify_worker(head, strict, depth, template);
                replace_spine_head(e, worker)
            }

            Expr::Variable(_, Identifier::Free(qn)) => {
                let qn: &QualifiedName = qn;
                if let Some(body) = self.strict_inlinables.get(qn) {
                    // The ordinary top-level definition remains a lazy IO wrapper
                    // for value/escaping uses.  At this run site, use a strict copy
                    // of its (small, acyclic) body.  The following simplify pass
                    // beta-reduces the parameters and cancels the now-adjacent
                    // `Suspend` constructor/force marker.  Unlike general inlining
                    // into loops, this cannot weld an action closure into the
                    // recursive frame: strictification removes that closure first.
                    // As with the ordinary inliner, instantiate a polymorphic
                    // definition from this occurrence and relocate its absolute
                    // De Bruijn levels beneath the caller's current binders before
                    // splicing it.  Omitting either step is not merely imprecise:
                    // a helper used inside a local loop would capture the caller's
                    // low-numbered binders as its own parameters.
                    let instantiated = inline_type_substitutions(
                        &body.annotation().inferred_type,
                        &head.annotation().inferred_type,
                    )
                    .map_or_else(
                        || (**body).clone(),
                        |substitutions| (**body).apply(&substitutions),
                    );
                    let relocated = shift(&Rc::new(instantiated), 0, depth);
                    let worker = self.strictify_worker(&relocated, strict, depth, template);
                    // Reduce the freshly opened worker before returning it to the
                    // surrounding recursive driver.  Delaying this to the ordinary
                    // post-pass simplifier would put the still-boxed intermediate
                    // under that simplifier's recursive-loop leak guard, precisely
                    // where it is forbidden to inline effectful plumbing.  Here the
                    // force has already been pushed into the concrete body, so local
                    // beta/case cancellation is both safe and necessary.
                    let reduced = simplify_expr(replace_spine_head(e, worker));
                    Rc::unwrap_or_clone(self.map_markers(&Rc::new(reduced), depth, strict))
                } else {
                    // A recursive definition cycle, an unavailable body, or a body over the
                    // strict-inlining budget keeps the ordinary force boundary.
                    self.force(e, depth, template)
                }
            }

            _ => self.force(e, depth, template),
        }
    }

    /// Turn a function value into a strict α-returning worker: keep its leading lambdas (recording a
    /// `RecursiveLambda`'s own level as `strict` so its self-calls stay tail), and `run` the
    /// innermost body.
    fn strictify_worker(
        &self,
        head: &Expr<TypeInfo, Identifier>,
        strict: &HashSet<usize>,
        depth: usize,
        template: &MatchClause<TypeInfo, Identifier>,
    ) -> Expr<TypeInfo, Identifier> {
        match head {
            Expr::Lambda(a, Lambda { parameter, body }) => Expr::Lambda(
                a.clone(),
                Lambda {
                    parameter: parameter.clone(),
                    body: Rc::new(self.strictify_worker(body, strict, depth + 1, template)),
                },
            ),
            Expr::RecursiveLambda(a, SelfReferential { own_name, lambda }) => {
                let mut inner = strict.clone();
                if let Identifier::Bound(l) = own_name {
                    inner.insert(*l);
                }
                Expr::RecursiveLambda(
                    a.clone(),
                    SelfReferential {
                        own_name: own_name.clone(),
                        lambda: Lambda {
                            parameter: lambda.parameter.clone(),
                            body: Rc::new(self.strictify_worker(
                                &lambda.body,
                                &inner,
                                depth + 2,
                                template,
                            )),
                        },
                    },
                )
            }
            other => self.run(&Rc::new(other.clone()), strict, depth, template),
        }
    }

    /// The sound fallback: an unchanged force marker `deconstruct e into Suspend #depth -> (#depth
    /// ())`, reusing `template`'s `Suspend` constructor and thunk / unit annotations, its binder
    /// freshened to the current `depth`, and the outer node annotated with the α (run-result) type.
    fn force(
        &self,
        e: &Tree<TypeInfo, Identifier>,
        depth: usize,
        template: &MatchClause<TypeInfo, Identifier>,
    ) -> Expr<TypeInfo, Identifier> {
        let alpha = TypeInfo {
            parse_info: e.annotation().parse_info.clone(),
            inferred_type: strip_io(&e.annotation().inferred_type),
            enclosing_term: e.annotation().enclosing_term.clone(),
        };
        let (Pattern::Coproduct(pann, cp), Expr::Apply(app_ann, ap)) =
            (&template.pattern, &*template.consequent)
        else {
            // Template is not the expected marker shape; leave `e` unforced (still IO). This never
            // happens for a genuine `as_run_marker` template, so it is only a total-match guard.
            return (**e).clone();
        };
        let Expr::Variable(var_ann, _) = &*ap.function else {
            return (**e).clone();
        };
        let thunk_ann = cp.arguments[0].annotation().clone();
        let clause = MatchClause {
            pattern: Pattern::Coproduct(
                pann.clone(),
                ConstructorPattern {
                    constructor: cp.constructor.clone(),
                    arguments: vec![Pattern::Bind(thunk_ann, Identifier::Bound(depth))],
                },
            ),
            consequent: Rc::new(Expr::Apply(
                app_ann.clone(),
                Apply {
                    function: Rc::new(Expr::Variable(var_ann.clone(), Identifier::Bound(depth))),
                    argument: ap.argument.clone(),
                },
            )),
        };
        Expr::Deconstruct(
            alpha,
            Deconstruct {
                scrutinee: e.clone(),
                match_clauses: vec![clause],
            },
        )
    }
}

/// First `run` marker anywhere in `body`, cloned (its constructor + unit + inner annotations are
/// the skeleton `force` reuses). `None` if the body has no run site.
fn find_any_marker(body: &Expr<TypeInfo, Identifier>) -> Option<MatchClause<TypeInfo, Identifier>> {
    if let Some((_, clause)) = as_run_marker(body) {
        return Some(clause.clone());
    }
    children(body).into_iter().find_map(|c| find_any_marker(c))
}

impl phase::SymbolTable<Types> {
    /// Strictify recursive IO loops (see the module comment above). Runs on the native pipeline
    /// after `specialize()` (so concrete dictionary calls can be opened) and before
    /// `simplify()` (which finishes the straight-line cancellation).
    pub fn deforest_io(self) -> Self {
        if !deforest_io_on() {
            return self;
        }
        let Self {
            symbols,
            module_members,
            member_modules,
            base_imports,
            module_imports,
            scope_roots,
            foreign_terms,
            signatures,
            witnesses,
            constructor_opacity,
            member_visibility,
        } = self;

        let terms: Vec<(&QualifiedName, &phase::Expr<Types>)> = symbols
            .values()
            .filter_map(|s| match s {
                Symbol::Term(t) => Some((&t.name, &t.body)),
                Symbol::Type(_) => None,
            })
            .collect();
        let names: HashSet<&QualifiedName> = terms.iter().map(|(n, _)| *n).collect();
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
        // General simplification deliberately refuses to inline effectful helpers
        // into recursive bodies: before strictification that can retain one action
        // closure per iteration.  Keep a separate, tightly bounded set for the
        // inverse order used here -- first make the helper strict, then inline that
        // closure-free worker at the run site.  Cyclic functions are excluded so
        // recursively strictifying an inline body always terminates. A local or
        // self-bound recursive lambda is self-contained and remains eligible; only
        // a cycle through global names falls back to ordinary boxed IO.
        let recursive: HashSet<QualifiedName> = terms
            .iter()
            // Only expansion through a *global-name* cycle can make strict
            // worker inlining recurse indefinitely.  A local `let loop =
            // RecursiveLambda ...` is self-contained in the copied body and is
            // precisely what `strictify_worker` knows how to turn into a strict
            // local loop; excluding a term merely because it contains one would
            // exclude every useful IO driver (`process_file_bytes`, folds, ...).
            .filter(|(name, _)| reaches_self(name, &dependencies))
            .map(|(name, _)| (*name).clone())
            .collect();
        let strict_inlinables: Inlinables<TypeInfo> = terms
            .iter()
            .filter(|(name, body)| {
                !recursive.contains(*name) && within_budget(body, STRICT_IO_INLINE_BUDGET)
            })
            .map(|(name, body)| ((*name).clone(), Rc::new((*body).clone())))
            .collect();

        // A `Suspend`-marker skeleton (constructor + unit + inner annotations) reused when a
        // strictified body must fall back to an unchanged force marker. Any marker in the program
        // serves; without one there are no run sites, so nothing to do.
        let Some(template) = terms.iter().find_map(|(_, body)| find_any_marker(body)) else {
            return Self {
                symbols,
                module_members,
                member_modules,
                base_imports,
                module_imports,
                scope_roots,
                foreign_terms,
                signatures,
                witnesses,
                constructor_opacity,
                member_visibility,
            };
        };
        let ctx = DeforestCtx {
            strict_inlinables: &strict_inlinables,
            force_template: &template,
        };

        let symbols = symbols
            .into_iter()
            .map(|(name, symbol)| {
                let symbol = match symbol {
                    Symbol::Term(TermSymbol {
                        name,
                        type_signature,
                        body,
                    }) => {
                        // Definitions always keep their ordinary lazy wrapper. A strict worker is
                        // copied only beneath an actual force, so a top-level IO value is never
                        // executed during global initialization and escaping actions retain their
                        // repeatable thunk semantics.
                        let body = Rc::unwrap_or_clone(ctx.map_markers(
                            &Rc::new(body),
                            0,
                            &HashSet::new(),
                        ));
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
            base_imports,
            module_imports,
            scope_roots,
            foreign_terms,
            signatures,
            witnesses,
            constructor_opacity,
            member_visibility,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Literal, ProductElement};
    use crate::typer::BaseType;

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

    type TT = Tree<TypeInfo, Identifier>;

    fn ti(ty: Type) -> TypeInfo {
        TypeInfo::new(crate::parser::ParseInfo::default(), ty)
    }

    fn io_of(payload: Type) -> Type {
        Type::application(Type::Constructor(crate::typer::io_type_name()), payload)
    }

    fn typed_var(level: usize, ty: Type) -> TT {
        Rc::new(Expr::Variable(ti(ty), Identifier::Bound(level)))
    }

    fn typed_free(name: &str, ty: Type) -> TT {
        Rc::new(Expr::Variable(ti(ty), free_id(name)))
    }

    fn typed_apply(function: TT, argument: TT, result: Type) -> TT {
        Rc::new(Expr::Apply(ti(result), Apply { function, argument }))
    }

    fn suspend_clause(
        thunk_level: usize,
        payload: Type,
        consequent: TT,
    ) -> MatchClause<TypeInfo, Identifier> {
        let thunk_type = Type::Arrow {
            capture: crate::ast::Confinement::Unconfined,
            domain: Type::Base(BaseType::Unit).into(),
            codomain: payload.clone().into(),
        };
        MatchClause {
            pattern: Pattern::Coproduct(
                ti(io_of(payload)),
                ConstructorPattern {
                    constructor: Identifier::Free(crate::typer::suspend_constructor_name().into()),
                    arguments: vec![Pattern::Bind(
                        ti(thunk_type),
                        Identifier::Bound(thunk_level),
                    )],
                },
            ),
            consequent,
        }
    }

    fn forced_thunk(thunk_level: usize, payload: Type) -> TT {
        let thunk_type = Type::Arrow {
            capture: crate::ast::Confinement::Unconfined,
            domain: Type::Base(BaseType::Unit).into(),
            codomain: payload.clone().into(),
        };
        typed_apply(
            typed_var(thunk_level, thunk_type),
            Rc::new(Expr::Constant(
                ti(Type::Base(BaseType::Unit)),
                Literal::Unit,
            )),
            payload,
        )
    }

    #[test]
    fn inline_types_instantiate_repeated_variables_consistently() {
        let variable = MetaVariable::fresh();
        let template = Type::Arrow {
            capture: crate::ast::Confinement::Unconfined,
            domain: Type::Variable(variable.clone()).into(),
            codomain: Type::Array(Type::Variable(variable).into()).into(),
        };
        let concrete = Type::Arrow {
            capture: crate::ast::Confinement::Unconfined,
            domain: Type::Base(BaseType::Int).into(),
            codomain: Type::Array(Type::Base(BaseType::Int).into()).into(),
        };

        let substitutions = inline_type_substitutions(&template, &concrete).unwrap();
        assert_eq!(template.apply(&substitutions), concrete);
    }

    #[test]
    fn inline_types_reject_inconsistent_repeated_variables() {
        let variable = MetaVariable::fresh();
        let template = Type::Arrow {
            capture: crate::ast::Confinement::Unconfined,
            domain: Type::Variable(variable.clone()).into(),
            codomain: Type::Variable(variable).into(),
        };
        let concrete = Type::Arrow {
            capture: crate::ast::Confinement::Unconfined,
            domain: Type::Base(BaseType::Int).into(),
            codomain: Type::Base(BaseType::Bool).into(),
        };

        assert!(inline_type_substitutions(&template, &concrete).is_none());
    }

    #[test]
    fn embedded_run_recognises_a_once_forced_thunk_under_a_constructor() {
        let payload = Type::Base(BaseType::Int);
        let forced = forced_thunk(0, payload.clone());
        let wrapped = Rc::new(Expr::Inject(
            ti(payload.clone()),
            Injection {
                constructor: ctor("Return"),
                arguments: vec![forced],
            },
        ));
        let expr = Expr::Deconstruct(
            ti(payload.clone()),
            Deconstruct {
                scrutinee: typed_free("action", io_of(payload.clone())),
                match_clauses: vec![suspend_clause(0, payload, wrapped)],
            },
        );

        let Some((_, _, thunk)) = as_embedded_run(&expr) else {
            panic!("expected the mapped force to be recognised")
        };
        assert_eq!(thunk, 0);
    }

    #[test]
    fn embedded_run_rejects_a_thunk_that_is_forced_twice() {
        let payload = Type::Base(BaseType::Int);
        let expr = Expr::Deconstruct(
            ti(payload.clone()),
            Deconstruct {
                scrutinee: typed_free("action", io_of(payload.clone())),
                match_clauses: vec![suspend_clause(
                    0,
                    payload.clone(),
                    Rc::new(Expr::Tuple(
                        ti(Type::Tuple(crate::typer::TupleType::from_signature(&[
                            payload.clone(),
                            payload.clone(),
                        ]))),
                        Tuple {
                            elements: vec![
                                forced_thunk(0, payload.clone()),
                                forced_thunk(0, payload),
                            ],
                        },
                    )),
                )],
            },
        );

        assert!(as_embedded_run(&expr).is_none());
    }

    #[test]
    fn local_io_worker_must_be_consumed_only_in_run_positions() {
        let payload = Type::Base(BaseType::Int);
        let function_type = Type::Arrow {
            capture: crate::ast::Confinement::Unconfined,
            domain: Type::Base(BaseType::Int).into(),
            codomain: io_of(payload.clone()).into(),
        };
        let call = typed_apply(
            typed_var(0, function_type.clone()),
            Rc::new(Expr::Constant(
                ti(Type::Base(BaseType::Int)),
                Literal::Int(1),
            )),
            io_of(payload.clone()),
        );
        let forced = Expr::Deconstruct(
            ti(payload.clone()),
            Deconstruct {
                scrutinee: call,
                match_clauses: vec![suspend_clause(
                    1,
                    payload.clone(),
                    forced_thunk(1, payload.clone()),
                )],
            },
        );
        assert!(local_io_function_is_run_only(
            &forced,
            0,
            false,
            0,
            &Inlinables::new(),
            &mut HashSet::new(),
        ));

        let escaped = Expr::Tuple(
            ti(Type::Tuple(crate::typer::TupleType::from_signature(&[
                function_type.clone(),
                function_type,
            ]))),
            Tuple {
                elements: vec![
                    typed_var(
                        0,
                        Type::Arrow {
                            capture: crate::ast::Confinement::Unconfined,
                            domain: Type::Base(BaseType::Int).into(),
                            codomain: io_of(payload.clone()).into(),
                        },
                    ),
                    typed_var(
                        0,
                        Type::Arrow {
                            capture: crate::ast::Confinement::Unconfined,
                            domain: Type::Base(BaseType::Int).into(),
                            codomain: io_of(payload).into(),
                        },
                    ),
                ],
            },
        );
        assert!(!local_io_function_is_run_only(
            &escaped,
            0,
            false,
            0,
            &Inlinables::new(),
            &mut HashSet::new(),
        ));
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
    fn effectful_forwarding_counts_uses_in_match_consequents() {
        // The scrutinee use is evaluated first, but #0 is also captured by the
        // selected continuation. Forwarding (g y) here would evaluate it twice:
        //   let #0 = (g y) in deconstruct #0 { C #1 -> (#0, #1) }
        let e = Expr::Let(
            (),
            Binding {
                binder: Identifier::Bound(0),
                operator: BindingOperator::Identity,
                bound: Rc::new(apply(free("g"), free("y"))),
                body: Rc::new(Expr::Deconstruct(
                    (),
                    Deconstruct {
                        scrutinee: var(0),
                        match_clauses: vec![MatchClause {
                            pattern: Pattern::Coproduct(
                                (),
                                ConstructorPattern {
                                    constructor: Identifier::Free(Box::new(ctor("C"))),
                                    arguments: vec![Pattern::Bind((), Identifier::Bound(1))],
                                },
                            ),
                            consequent: Rc::new(Expr::Tuple(
                                (),
                                Tuple {
                                    elements: vec![var(0), var(1)],
                                },
                            )),
                        }],
                    },
                )),
            },
        );

        assert!(matches!(simplify(e), Expr::Let(..)));
    }

    #[test]
    fn effectful_forwarding_does_not_move_a_later_use_into_a_match_arm() {
        // `#0` is used once, but it is NOT the scrutinee evaluated first.  Forwarding
        // `(read slot)` into the arm would delay that read until after evaluation of the
        // unrelated scrutinee (and, in real IO code, past intervening writes).
        //
        //   let #0 = (read slot) in deconstruct other { C #1 -> #0 }
        let e = Expr::Let(
            (),
            Binding {
                binder: Identifier::Bound(0),
                operator: BindingOperator::Identity,
                bound: Rc::new(apply(free("read"), free("slot"))),
                body: Rc::new(Expr::Deconstruct(
                    (),
                    Deconstruct {
                        scrutinee: free("other"),
                        match_clauses: vec![MatchClause {
                            pattern: Pattern::Coproduct(
                                (),
                                ConstructorPattern {
                                    constructor: Identifier::Free(Box::new(ctor("C"))),
                                    arguments: vec![Pattern::Bind((), Identifier::Bound(1))],
                                },
                            ),
                            consequent: var(0),
                        }],
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
