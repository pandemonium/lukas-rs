//! Concrete-witness specialization ("Int-specialization"), run to a fixpoint with
//! the simplifier. For a recursive, dictionary-constrained top-level function called
//! with a *ground* witness (e.g. `Tree_Map.insert (Ord Int) …`), clone the function
//! and repoint the dictionary parameter's uses at the witness global. Inside the
//! clone the dictionary is a literal, so the simplifier collapses `k < kk` to
//! `prim_lt`. Each simplify round also inlines wrappers, which turns their inner
//! dictionary arguments into ground witnesses too (a set insert wrapping a map
//! insert) — so we alternate specialize/simplify until no new clone is minted. The
//! dead dict parameter is left in place (no de Bruijn renumbering) and threaded,
//! unused. On by default; opt out with `MARM_SPECIALIZE` set to `0`/`off`/`no`/`false`.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::ast::namer::{Identifier, QualifiedName, Symbol, SymbolName, TermSymbol};
use crate::ast::{Apply, Expr};
use crate::phase;
use crate::typer::Types;

const SPEC_MARK: &str = "$spec$";

impl phase::SymbolTable<Types> {
    pub fn specialize(mut self) -> Self {
        // On by default; a program opts out by setting `MARM_SPECIALIZE` to a falsy
        // value (mirrors `MARM_GC=slab` opting out of the default Immix collector).
        if let Some(value) = std::env::var_os("MARM_SPECIALIZE") {
            let disabled = matches!(
                value.to_str().map(str::trim).map(str::to_ascii_lowercase).as_deref(),
                Some("0" | "off" | "no" | "false" | "")
            );
            if disabled {
                return self;
            }
        }
        // Cascade by substitution alone: substituting a wrapper's dictionary for the
        // witness turns its inner dictionary arguments into ground witnesses too (a set
        // insert wrapping a map insert), which the next round specializes. We must NOT
        // simplify between rounds -- inlining a non-recursive wrapper before the round
        // that specializes its callee severs the clone chain. The pipeline's own
        // simplify (after this returns) collapses every clone's now-literal dictionary
        // to prim ops and inlines the non-recursive links. Iterate to a fixpoint.
        for _ in 0..16 {
            let before = self.symbols.len();
            self = self.specialize_once();
            if self.symbols.len() == before {
                break;
            }
        }
        self
    }

    fn specialize_once(mut self) -> Self {
        // Recursive, dictionary-constrained functions (excluding clones we already
        // made) and the Bound level of their leading dictionary parameter.
        let dict_levels: HashMap<QualifiedName, usize> = self
            .symbols
            .iter()
            .filter_map(|(name, sym)| match (name, sym) {
                (SymbolName::Term(qn), Symbol::Term(t))
                    if !qn.member().as_str().contains(SPEC_MARK) =>
                {
                    dict_level(&t.body).map(|n| (qn.clone(), n))
                }
                _ => None,
            })
            .collect();

        // Ground call sites `f w …` (f recursive-constrained, w a ground witness).
        let mut pairs: Vec<(QualifiedName, QualifiedName)> = Vec::new();
        for sym in self.symbols.values() {
            if let Symbol::Term(t) = sym {
                collect_pairs(&t.body, &dict_levels, &self.witnesses, &mut pairs);
            }
        }
        pairs.sort();
        pairs.dedup();
        if pairs.is_empty() {
            return self;
        }

        // Mint (or reuse) a clone per (f, w) under a deterministic name.
        let mut specs: HashMap<(QualifiedName, QualifiedName), QualifiedName> = HashMap::new();
        let mut fresh = Vec::new();
        for (f, w) in &pairs {
            let clone_qn = QualifiedName::new(
                f.module().clone(),
                &format!("{}{SPEC_MARK}{}", f.member().as_str(), w.member().as_str()),
            );
            if !self.symbols.contains_key(&SymbolName::Term(clone_qn.clone())) {
                if let Some(Symbol::Term(t)) = self.symbols.get(&SymbolName::Term(f.clone())) {
                    let body = substitute_dict(t.body.clone(), dict_levels[f], own_level(&t.body), w);
                    fresh.push((clone_qn.clone(), t.type_signature.clone(), body));
                }
            }
            specs.insert((f.clone(), w.clone()), clone_qn);
        }
        for (qn, sig, body) in fresh {
            self.symbols.insert(
                SymbolName::Term(qn.clone()),
                Symbol::Term(TermSymbol {
                    name: qn,
                    type_signature: sig,
                    body,
                }),
            );
        }

        // Redirect every `f w …` to its clone (the witness arg is kept but dead).
        let symbols = std::mem::take(&mut self.symbols);
        self.symbols = symbols
            .into_iter()
            .map(|(name, sym)| {
                let sym = match sym {
                    Symbol::Term(t) => Symbol::Term(TermSymbol {
                        body: rewrite_calls(t.body, &specs),
                        ..t
                    }),
                    other => other,
                };
                (name, sym)
            })
            .collect();
        self
    }
}

/// The Bound level of a recursive function's leading (dictionary) parameter, or
/// `None` for anything but a `RecursiveLambda` (non-recursive functions are inlined
/// at their use sites, so specialization only helps the recursive ones).
fn dict_level<A>(mut body: &Expr<A, Identifier>) -> Option<usize> {
    loop {
        match body {
            Expr::Ascription(_, a) => body = a.ascribed_tree.as_ref(),
            Expr::RecursiveLambda(_, sr) => {
                return match &sr.lambda.parameter {
                    Identifier::Bound(n) => Some(*n),
                    _ => None,
                };
            }
            _ => return None,
        }
    }
}

/// The self-reference (`RecursiveLambda` own-name) Bound level of a top-level body.
fn own_level<A>(mut body: &Expr<A, Identifier>) -> usize {
    loop {
        match body {
            Expr::Ascription(_, a) => body = a.ascribed_tree.as_ref(),
            Expr::RecursiveLambda(_, sr) => {
                return match sr.own_name {
                    Identifier::Bound(m) => m,
                    _ => usize::MAX,
                };
            }
            _ => return usize::MAX,
        }
    }
}

/// Fix the dictionary parameter (`Bound(dict)`) to the concrete witness global.
///
/// The dictionary is substituted *everywhere* -- so its method accesses become
/// projection-of-literal (which the simplifier collapses to prim ops) and any inner
/// constrained call it is handed to becomes a ground witness application (exposing
/// the next cascade round). The one exception is the argument position of a
/// self-call (head = the self-reference `Bound(own)`): there we put the parameter
/// back, so it stays a live, captured parameter and the function keeps its arity --
/// worker synthesis rejects an unused parameter, which would otherwise force the
/// clone onto the slow `apply_n` path. The threaded dict is then only ever read
/// through the already-collapsed projections, so it never actually flows anywhere.
fn substitute_dict<A: Clone>(
    body: Expr<A, Identifier>,
    dict: usize,
    own: usize,
    witness: &QualifiedName,
) -> Expr<A, Identifier> {
    body.map(&mut |node| match node {
        Expr::Variable(a, Identifier::Bound(n)) if n == dict => {
            Expr::Variable(a, Identifier::Free(Box::new(witness.clone())))
        }
        // A self-call's leading argument is the dict slot; the child was just
        // witness-substituted above, so put the parameter back to keep it live.
        Expr::Apply(a, mut app)
            if matches!(&*app.function, Expr::Variable(_, Identifier::Bound(n)) if *n == own) =>
        {
            let ann = app.argument.annotation().clone();
            app.argument = Rc::new(Expr::Variable(ann, Identifier::Bound(dict)));
            Expr::Apply(a, app)
        }
        other => other,
    })
}

/// Collect ground `f w` applications: `f` a recursive-constrained function, `w` a
/// ground witness global.
fn collect_pairs<A>(
    body: &Expr<A, Identifier>,
    dict_levels: &HashMap<QualifiedName, usize>,
    witnesses: &HashSet<QualifiedName>,
    out: &mut Vec<(QualifiedName, QualifiedName)>,
) {
    if let Expr::Apply(_, app) = body {
        if let (Expr::Variable(_, Identifier::Free(f)), Expr::Variable(_, Identifier::Free(w))) =
            (&*app.function, &*app.argument)
        {
            if dict_levels.contains_key(f.as_ref()) && witnesses.contains(w.as_ref()) {
                out.push((f.as_ref().clone(), w.as_ref().clone()));
            }
        }
    }
    for child in crate::simplify::children(body) {
        collect_pairs(&**child, dict_levels, witnesses, out);
    }
}

/// Redirect `f w …` to its specialized clone (the witness argument is left in place
/// as the now-dead dictionary parameter).
fn rewrite_calls<A: Clone>(
    body: Expr<A, Identifier>,
    specs: &HashMap<(QualifiedName, QualifiedName), QualifiedName>,
) -> Expr<A, Identifier> {
    body.map(&mut |node| match node {
        Expr::Apply(a, app) => {
            let target = match (&*app.function, &*app.argument) {
                (
                    Expr::Variable(fa, Identifier::Free(f)),
                    Expr::Variable(_, Identifier::Free(w)),
                ) => specs
                    .get(&(f.as_ref().clone(), w.as_ref().clone()))
                    .map(|c| (fa.clone(), c.clone())),
                _ => None,
            };
            match target {
                Some((fa, clone)) => Expr::Apply(
                    a,
                    Apply {
                        function: Rc::new(Expr::Variable(fa, Identifier::Free(Box::new(clone)))),
                        argument: app.argument,
                    },
                ),
                None => Expr::Apply(a, app),
            }
        }
        other => other,
    })
}
