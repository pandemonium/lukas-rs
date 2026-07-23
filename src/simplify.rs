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
        Apply, Binding, Deconstruct, Expr, IfThenElse, Injection, Interpolate, Lambda,
        ProductElement, Projection, Record, Segment, SelfReferential, Sequence, Tree, Tuple,
        TypeAscription,
        namer::{Identifier, QualifiedName, Symbol, TermSymbol},
        pattern::{ConstructorPattern, MatchClause, Pattern, StructPattern, TuplePattern},
    },
    lexer::BindingOperator,
    phase,
    typer::Types,
};

/// Largest term body (in AST nodes) the inliner will unfold. Combinators, method
/// selectors, constructor wrappers and dictionaries are all well under this.
const INLINE_BUDGET: usize = 100;
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
        let (inlinables, recursive) = if std::env::var_os("MARM_NO_INLINE").is_some() {
            (Inlinables::default(), HashSet::default())
        } else {
            build_inlinables(&symbols)
        };
        let no_inline = Inlinables::default();
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
                        // Do not inline into a recursive body (a loop) -- that is where
                        // inlining an effectful `bind` leaks by capturing the action.
                        let inls = if guard_loops && recursive.contains(&term.name) {
                            &no_inline
                        } else {
                            &inlinables
                        };
                        let body = simplify_term(term.body, inls);
                        if dump.as_deref().is_some_and(|f| term.name.to_string().contains(f)) {
                            eprintln!("==== {} ====\n{}\n", term.name, body);
                        }
                        Symbol::Term(TermSymbol {
                            name: term.name,
                            type_signature: term.type_signature,
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
/// non-recursive so unfolding terminates), plus the set of *recursive* terms. Both come
/// from the same term-dependency graph. The recursive set is the set of function bodies
/// we must NOT inline *into*: a recursive body is a loop, and inlining an effectful `bind`
/// into a loop welds the sequenced action into the recursion's closure -- the space leak.
/// Keeping loops calling `bind` as an ordinary worker leaves the action an argument that
/// dies each turn, while the straight-line callers still collapse fully.
fn build_inlinables(
    symbols: &HashMap<crate::ast::namer::SymbolName, phase::Symbol<Types>>,
) -> (Inlinables<crate::typer::TypeInfo>, HashSet<QualifiedName>) {
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

    let inlinables = terms
        .iter()
        .filter(|(name, body)| {
            within_budget(body, INLINE_BUDGET) && !recursive.contains(*name)
        })
        .map(|(name, body)| ((*name).clone(), Rc::new((*body).clone())))
        .collect();

    (inlinables, recursive)
}

/// Whether `expr` contains a self-referential lambda that actually uses its self-binder
/// -- i.e. a real loop. (An unused self-binder is not recursion; `derecursify` drops it.)
fn contains_recursion<A>(expr: &Expr<A, Identifier>) -> bool {
    match expr {
        Expr::RecursiveLambda(_, SelfReferential { own_name: Identifier::Bound(level), lambda })
            if mentions_level(&lambda.body, *level) =>
        {
            true
        }
        _ => children(expr).into_iter().any(|c| contains_recursion(c)),
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

/// The immediate sub-trees of a node, in evaluation order. Used by size measurement
/// (and any other structural fold that does not care which slot a child sits in).
fn children<A>(expr: &Expr<A, Identifier>) -> Vec<&Tree<A, Identifier>> {
    match expr {
        Expr::Variable(..) | Expr::InvokeBridge(..) | Expr::Constant(..) | Expr::MakeClosure(..) => {
            vec![]
        }
        Expr::RecursiveLambda(_, SelfReferential { lambda, .. }) => vec![&lambda.body],
        Expr::Lambda(_, Lambda { body, .. }) => vec![body],
        Expr::Apply(_, Apply { function, argument }) => vec![function, argument],
        Expr::Let(_, Binding { bound, body, .. }) => vec![bound, body],
        Expr::Tuple(_, Tuple { elements }) => elements.iter().collect(),
        Expr::Record(_, Record { fields }) => fields.iter().map(|(_, v)| v).collect(),
        Expr::Inject(_, Injection { arguments, .. }) => arguments.iter().collect(),
        Expr::Project(_, Projection { base, .. }) => vec![base],
        Expr::Sequence(_, Sequence { this, and_then }) => vec![this, and_then],
        Expr::Deconstruct(_, Deconstruct { scrutinee, match_clauses }) => {
            let mut cs = vec![scrutinee];
            cs.extend(match_clauses.iter().map(|clause| &clause.consequent));
            cs
        }
        Expr::If(_, IfThenElse { predicate, consequent, alternate }) => {
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
                    base: self.try_head(base, depth).unwrap_or_else(|| go(base, depth)),
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

            Expr::RecursiveLambda(a, SelfReferential { own_name, lambda }) => Expr::RecursiveLambda(
                a.clone(),
                SelfReferential {
                    own_name: own_name.clone(),
                    lambda: Lambda {
                        parameter: lambda.parameter.clone(),
                        // own_name binds at `depth`, the parameter at `depth + 1`.
                        body: go(&lambda.body, depth + 2),
                    },
                },
            ),

            Expr::Let(a, Binding { binder, operator, bound, body }) => Expr::Let(
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
            Expr::Deconstruct(a, Deconstruct { scrutinee, match_clauses }) => Expr::Deconstruct(
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
                    fields: fields.iter().map(|(k, v)| (k.clone(), go(v, depth))).collect(),
                },
            ),

            Expr::Inject(a, Injection { constructor, arguments }) => Expr::Inject(
                a.clone(),
                Injection {
                    constructor: constructor.clone(),
                    arguments: arguments.iter().map(|e| go(e, depth)).collect(),
                },
            ),

            Expr::Sequence(a, Sequence { this, and_then }) => Expr::Sequence(
                a.clone(),
                Sequence {
                    this: go(this, depth),
                    and_then: go(and_then, depth),
                },
            ),

            Expr::If(a, IfThenElse { predicate, consequent, alternate }) => Expr::If(
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

            Expr::Ascription(a, TypeAscription { ascribed_tree, type_signature }) => {
                Expr::Ascription(
                    a.clone(),
                    TypeAscription {
                        ascribed_tree: go(ascribed_tree, depth),
                        type_signature: type_signature.clone(),
                    },
                )
            }

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
        Expr::Ascription(_, ascription) => {
            (true, Rc::unwrap_or_clone(ascription.ascribed_tree))
        }

        // derecursify: every top-level combinator is elaborated as a self-referential
        // lambda (`#L := λ…`), but the ones we inline never use their self-binder. Drop
        // it so the plain-lambda beta rules can fire. The self binder sits at level `L`
        // (its own depth) with the parameter at `L+1`; removing it slides everything
        // above `L` down by one, so the parameter lands at `L` -- a normal lambda.
        Expr::RecursiveLambda(a, SelfReferential { own_name, lambda })
            if matches!(&own_name, Identifier::Bound(l) if !mentions_level(&lambda.body, *l)) =>
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
            (true, rewrap_let(la, binding.binder, binding.operator, binding.bound, floated))
        }

        Expr::Project(a, projection) if is_floatable_let(&projection.base) => {
            let Projection { base, select } = projection;
            let (la, binding, _level) = open_let(base);
            let floated = Expr::Project(a, Projection { base: binding.body, select });
            (true, rewrap_let(la, binding.binder, binding.operator, binding.bound, floated))
        }

        Expr::Deconstruct(a, deconstruct) if is_floatable_let(&deconstruct.scrutinee) => {
            let Deconstruct { scrutinee, match_clauses } = deconstruct;
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
            (true, rewrap_let(la, binding.binder, binding.operator, binding.bound, floated))
        }

        // let-forwarding: substitute a value-bound `let` into its uses when every use
        // is an *elimination* (projection base / apply head / deconstruct scrutinee).
        // That is what finally lets a forwarded dictionary meet its projection and a
        // forwarded `MkGet`/`MkState` payload meet its deconstruct, so the box cancels.
        //   * value-bound only -> duplicating / dropping it is effect- and
        //     termination-neutral (and it de-sugars to no allocation once it cancels);
        //   * all-uses-eliminated -> the copy always meets an eliminator, so we never
        //     turn a shared allocation into a per-use one.
        // Zero uses is the degenerate case: a dead pure `let`, simply dropped.
        Expr::Let(_a, binding)
            if matches!(&binding.binder, Identifier::Bound(l)
                if is_value(&binding.bound) && all_uses_eliminated(&binding.body, *l)) =>
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
        Expr::Deconstruct(_, Deconstruct { scrutinee, match_clauses }) => {
            eliminated_head(scrutinee, level)
                && match_clauses
                    .iter()
                    .all(|clause| all_uses_eliminated(&clause.consequent, level))
        }
        other => children(other).into_iter().all(|c| all_uses_eliminated(c, level)),
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

        Expr::Let(a, Binding { binder, operator, bound, body }) => Expr::Let(
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
                fields: fields.iter().map(|(k, v)| (k.clone(), go(v, depth))).collect(),
            },
        ),

        Expr::Inject(a, Injection { constructor, arguments }) => Expr::Inject(
            a.clone(),
            Injection {
                constructor: constructor.clone(),
                arguments: arguments.iter().map(|e| go(e, depth)).collect(),
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

        Expr::Deconstruct(a, Deconstruct { scrutinee, match_clauses }) => Expr::Deconstruct(
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

        Expr::If(a, IfThenElse { predicate, consequent, alternate }) => Expr::If(
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

        Expr::Ascription(a, TypeAscription { ascribed_tree, type_signature }) => Expr::Ascription(
            a.clone(),
            TypeAscription {
                ascribed_tree: go(ascribed_tree, depth),
                type_signature: type_signature.clone(),
            },
        ),
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
        Expr::Let(_, Binding { binder: Identifier::Bound(_), .. })
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
        (Expr::Record(_, Record { fields }), ProductElement::Ordinal(index)) => {
            (*index < fields.len()).then(|| project_field(fields, *index)).flatten()
        }

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
        _ => None,
    }
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

    if levels.iter().enumerate().any(|(i, &level)| level != base + i) {
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

        Expr::Let(a, Binding {
            binder,
            operator,
            bound,
            body,
        }) => Expr::Let(
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

        Expr::Inject(a, Injection {
            constructor,
            arguments,
        }) => Expr::Inject(
            a.clone(),
            Injection {
                constructor: constructor.clone(),
                arguments: arguments.iter().map(&go).collect(),
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

        Expr::Deconstruct(a, Deconstruct {
            scrutinee,
            match_clauses,
        }) => Expr::Deconstruct(
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

        Expr::If(a, IfThenElse {
            predicate,
            consequent,
            alternate,
        }) => Expr::If(
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
                        Segment::Literal(sa, literal) => Segment::Literal(sa.clone(), literal.clone()),
                        Segment::Expression(expr) => Segment::Expression(go(expr)),
                    })
                    .collect(),
            ),
        ),

        Expr::Ascription(a, TypeAscription {
            ascribed_tree,
            type_signature,
        }) => Expr::Ascription(
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
        Pattern::Coproduct(a, ConstructorPattern {
            constructor,
            arguments,
        }) => Pattern::Coproduct(
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
                elements: elements.iter().map(|p| walk_pattern(p, on_binder)).collect(),
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
        Identifier::Free(Box::new(crate::ast::namer::QualifiedName::from_root_symbol(
            crate::parser::Identifier::from_str(name),
        )))
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
        Expr::Apply((), Apply { function: f, argument: x })
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
        assert!(matches!(&*d.scrutinee, Expr::Variable((), Identifier::Bound(0))));
        let Pattern::Coproduct((), cp) = &d.match_clauses[0].pattern else {
            panic!("expected coproduct pattern")
        };
        assert!(matches!(cp.arguments[0], Pattern::Bind((), Identifier::Bound(5))));
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
        let body = Rc::new(Expr::Tuple((), Tuple { elements: vec![var(2), var(1)] }));
        let g = Expr::Variable((), free_id("g"));
        let Expr::Tuple((), t) = substitute_atom(&body, 1, &g) else {
            panic!("expected tuple")
        };
        assert!(matches!(&*t.elements[0], Expr::Variable((), Identifier::Bound(1))));
        assert!(matches!(&*t.elements[1], Expr::Variable((), Identifier::Free(_))));
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
        assert!(matches!(simplify(e), Expr::Variable((), Identifier::Free(_))));
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
            Expr::Lambda((), Lambda { parameter: Identifier::Bound(1), .. })
        ));
    }

    // ---- let-forwarding ----

    #[test]
    fn forwards_value_let_into_projection_and_cancels() {
        // let #0 = (7, 8) in #0.&1  ->  (7, 8).&1  ->  8
        let pair = Rc::new(Expr::Tuple((), Tuple { elements: vec![int(7), int(8)] }));
        let e = Expr::Let(
            (),
            Binding {
                binder: Identifier::Bound(0),
                operator: BindingOperator::Identity,
                bound: pair,
                body: Rc::new(Expr::Project(
                    (),
                    Projection { base: var(0), select: ProductElement::Ordinal(1) },
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
        assert!(matches!(simplify(e), Expr::Variable((), Identifier::Free(_))));
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
                body: Rc::new(Expr::Tuple((), Tuple { elements: vec![var(0), var(0)] })),
            },
        );
        assert!(matches!(simplify(e), Expr::Let(..)));
    }

    #[test]
    fn substitute_value_relocates_to_use_depth() {
        // substitute (#7,) for level 0 in  λ#1. #0
        //   -> λ#0. (#8,)   -- binder #1 drops to #0; the value, used one binder deep,
        //      shifts its free level #7 up to #8.
        let value = Rc::new(Expr::Tuple((), Tuple { elements: vec![var(7)] }));
        let body = lam(1, var(0));
        let Expr::Lambda((), Lambda { parameter, body }) = substitute_value(&body, 0, &value) else {
            panic!("expected lambda")
        };
        assert!(matches!(parameter, Identifier::Bound(0)));
        let Expr::Tuple((), t) = &*body else {
            panic!("expected tuple")
        };
        assert!(matches!(&*t.elements[0], Expr::Variable((), Identifier::Bound(8))));
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
        assert!(matches!(&*binding.body, Expr::Variable((), Identifier::Bound(0))));
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
                    Tuple { elements: vec![int(10), int(20)] },
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
        crate::ast::namer::QualifiedName::from_root_symbol(crate::parser::Identifier::from_str(name))
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
            consequent: Rc::new(Expr::Tuple((), Tuple { elements: vec![var(0), var(1)] })),
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
        assert!(matches!(&*outer.bound, Expr::Constant((), Literal::Int(10))));
        let Expr::Let((), inner) = &*outer.body else {
            panic!("expected inner let")
        };
        assert!(matches!(inner.binder, Identifier::Bound(1)));
        assert!(matches!(&*inner.bound, Expr::Constant((), Literal::Int(20))));
        assert!(matches!(&*inner.body, Expr::Tuple(..)));
    }

    #[test]
    fn nullary_constructor_selects_bare_consequent() {
        // deconstruct Nil { Nil -> 42 | Cons #0 #1 -> #0 } -> 42
        let scrutinee = Rc::new(Expr::Inject(
            (),
            Injection { constructor: ctor("Nil"), arguments: vec![] },
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
            Tuple { elements: vec![var(5), lam(0, var(0))] },
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
            consequent: Rc::new(Expr::Tuple((), Tuple { elements: vec![var(5), var(6)] })),
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
        assert!(matches!(&*outer.bound, Expr::Variable((), Identifier::Bound(5))));
        let Expr::Let((), inner) = &*outer.body else {
            panic!("expected inner let")
        };
        assert!(matches!(inner.binder, Identifier::Bound(6)));
        // shifted lambda still has its own binder at #0 (below threshold 5)
        assert!(matches!(&*inner.bound, Expr::Lambda((), Lambda { parameter: Identifier::Bound(0), .. })));
    }

    #[test]
    fn wildcard_clause_binds_whole_scrutinee() {
        // deconstruct (Pair 1 2) { #0 -> #0 } -> let #0 = Pair 1 2 in #0
        let scrutinee = Rc::new(Expr::Inject(
            (),
            Injection { constructor: ctor("Pair"), arguments: vec![int(1), int(2)] },
        ));
        let clause = MatchClause {
            pattern: Pattern::Bind((), Identifier::Bound(0)),
            consequent: var(0),
        };
        let e = Expr::Deconstruct(
            (),
            Deconstruct { scrutinee, match_clauses: vec![clause] },
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
            Injection { constructor: ctor("Wrap"), arguments: vec![int(1)] },
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
            Deconstruct { scrutinee, match_clauses: vec![clause] },
        );
        assert!(matches!(simplify(e), Expr::Deconstruct(..)));
    }
}
