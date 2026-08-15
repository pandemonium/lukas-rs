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
use std::hash::{DefaultHasher, Hash, Hasher};
use std::rc::Rc;

use crate::ast::namer::{Identifier, QualifiedName, Symbol, SymbolName, TermSymbol};
use crate::ast::{Apply, Expr};
use crate::phase;
use crate::typer::Types;
use crate::typer::{
    MetaVariable, Substitutable, Substitutions, Type, memory_layout_class,
    memory_layout_evidence_name,
};

const SPEC_MARK: &str = "$spec$";
const LAYOUT_SPEC_MARK: &str = "$layout$";
const MAX_LAYOUT_SPECIALIZATIONS: usize = 64;

impl phase::SymbolTable<Types> {
    pub fn specialize(mut self) -> Self {
        // On by default; a program opts out by setting `MARM_SPECIALIZE` to a falsy
        // value (mirrors `MARM_GC=slab` opting out of the default Immix collector).
        if let Some(value) = std::env::var_os("MARM_SPECIALIZE") {
            let disabled = matches!(
                value
                    .to_str()
                    .map(str::trim)
                    .map(str::to_ascii_lowercase)
                    .as_deref(),
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
                    if !qn.member().as_str().contains(SPEC_MARK)
                        && !qn.member().as_str().contains(LAYOUT_SPEC_MARK) =>
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

        // Mint (or reuse) a clone per (f, w) under a deterministic name.
        let mut specs: HashMap<(QualifiedName, QualifiedName), QualifiedName> = HashMap::new();
        let mut fresh = Vec::new();
        for (f, w) in &pairs {
            let clone_qn = QualifiedName::new(
                f.module().clone(),
                &format!("{}{SPEC_MARK}{}", f.member().as_str(), w.member().as_str()),
            );
            if !self
                .symbols
                .contains_key(&SymbolName::Term(clone_qn.clone()))
            {
                if let Some(Symbol::Term(t)) = self.symbols.get(&SymbolName::Term(f.clone())) {
                    let body =
                        substitute_dict(t.body.clone(), dict_levels[f], own_level(&t.body), w);
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

        // A compiler-generated `Memory_Layout tau` value is constant evidence in
        // exactly the same sense as a concrete Ord/Eq witness. Keep this deliberately
        // narrower than monomorphisation: only the leading dictionary of recursive
        // term functions is fixed, and constructor/type symbols are never copied.
        if std::env::var_os("MARM_NO_LAYOUT_SPECIALIZE").is_none() {
            let mut layout_pairs = Vec::new();
            for sym in self.symbols.values() {
                if let Symbol::Term(t) = sym {
                    collect_layout_pairs(&t.body, &dict_levels, &mut layout_pairs);
                }
            }
            layout_pairs.sort();
            layout_pairs.dedup();
            layout_pairs.truncate(MAX_LAYOUT_SPECIALIZATIONS);

            let mut layout_specs = HashMap::new();
            let mut layout_fresh = Vec::new();
            for (function, dict_type) in layout_pairs {
                let clone_qn = QualifiedName::new(
                    function.module().clone(),
                    &format!(
                        "{}{LAYOUT_SPEC_MARK}{:016x}",
                        function.member().as_str(),
                        stable_hash(&dict_type)
                    ),
                );
                if !self
                    .symbols
                    .contains_key(&SymbolName::Term(clone_qn.clone()))
                    && let Some(Symbol::Term(term)) =
                        self.symbols.get(&SymbolName::Term(function.clone()))
                {
                    let evidence = layout_evidence(dict_type.clone());
                    let substitutions =
                        layout_substitutions(&term.body, dict_levels[&function], &dict_type)
                            .unwrap_or_default();
                    let body = substitute_evidence(
                        term.body.apply(&substitutions),
                        dict_levels[&function],
                        own_level(&term.body),
                        &evidence,
                    );
                    layout_fresh.push((clone_qn.clone(), term.type_signature.clone(), body));
                }
                layout_specs.insert((function, dict_type), clone_qn);
            }
            for (qn, sig, body) in layout_fresh {
                self.symbols.insert(
                    SymbolName::Term(qn.clone()),
                    Symbol::Term(TermSymbol {
                        name: qn,
                        type_signature: sig,
                        body,
                    }),
                );
            }

            let symbols = std::mem::take(&mut self.symbols);
            self.symbols = symbols
                .into_iter()
                .map(|(name, sym)| {
                    let sym = match sym {
                        Symbol::Term(t) => Symbol::Term(TermSymbol {
                            body: rewrite_layout_calls(t.body, &layout_specs),
                            ..t
                        }),
                        other => other,
                    };
                    (name, sym)
                })
                .collect();
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

fn stable_hash(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn layout_evidence(dict_type: Type) -> phase::Expr<Types> {
    let annotation = crate::parser::ParseInfo::default().with_inferred_type(dict_type);
    Expr::Variable(
        annotation,
        Identifier::Free(Box::new(memory_layout_evidence_name())),
    )
}

fn layout_substitutions(
    body: &phase::Expr<Types>,
    _dict: usize,
    concrete: &Type,
) -> Option<Substitutions> {
    fn leading_dict_type(mut body: &phase::Expr<Types>) -> Option<&Type> {
        while let Expr::Ascription(_, ascription) = body {
            body = &ascription.ascribed_tree;
        }
        let Expr::RecursiveLambda(annotation, _) = body else {
            return None;
        };
        let Type::Arrow { domain, .. } = &annotation.inferred_type else {
            return None;
        };
        matches!(
            domain.as_ref(),
            Type::Apply { constructor, .. }
                if matches!(constructor.as_ref(), Type::Constructor(name)
                    if *name == memory_layout_class())
        )
        .then_some(domain.as_ref())
    }

    let template = leading_dict_type(body)?;
    let mut bindings = HashMap::new();
    match_type_pattern(template, concrete, &mut bindings)?;
    Some(bindings.into_iter().collect::<Vec<_>>().into())
}

fn match_type_pattern(
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
            },
            Type::Apply {
                constructor: cc,
                argument: ca,
            },
        ) => {
            match_type_pattern(tc, cc, bindings)?;
            match_type_pattern(ta, ca, bindings)
        }
        (
            Type::Arrow {
                domain: td,
                codomain: tc,
            },
            Type::Arrow {
                domain: cd,
                codomain: cc,
            },
        ) => {
            match_type_pattern(td, cd, bindings)?;
            match_type_pattern(tc, cc, bindings)
        }
        (Type::Array(template), Type::Array(concrete)) => {
            match_type_pattern(template, concrete, bindings)
        }
        (Type::Tuple(template), Type::Tuple(concrete)) if template.arity() == concrete.arity() => {
            for (template, concrete) in template.elements().iter().zip(concrete.elements()) {
                match_type_pattern(template, concrete, bindings)?;
            }
            Some(())
        }
        (template, concrete) if template == concrete => Some(()),
        _ => None,
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

fn concrete_layout_type(expr: &phase::Expr<Types>) -> Option<Type> {
    match expr {
        Expr::Variable(annotation, Identifier::Free(name))
            if **name == memory_layout_evidence_name()
                && annotation.inferred_type.variables().is_empty() =>
        {
            Some(annotation.inferred_type.clone())
        }
        // Inside an already layout-specialized clone, the retained dictionary
        // parameter has a ground Memory_Layout type and is guaranteed to have been
        // supplied by the constant-evidence call that selected the clone. Treat it
        // as constant for the purpose of cascading to nested constrained workers,
        // while still passing the parameter so function arity remains stable.
        Expr::Variable(annotation, Identifier::Bound(_))
            if annotation.inferred_type.variables().is_empty()
                && matches!(
                    &annotation.inferred_type,
                    Type::Apply { constructor, .. }
                        if matches!(constructor.as_ref(), Type::Constructor(name)
                            if *name == memory_layout_class())
                ) =>
        {
            Some(annotation.inferred_type.clone())
        }
        _ => None,
    }
}

fn collect_layout_pairs(
    body: &phase::Expr<Types>,
    dict_levels: &HashMap<QualifiedName, usize>,
    out: &mut Vec<(QualifiedName, Type)>,
) {
    if let Expr::Apply(_, app) = body
        && let Expr::Variable(_, Identifier::Free(function)) = &*app.function
        && dict_levels.contains_key(function.as_ref())
        && let Some(dict_type) = concrete_layout_type(&app.argument)
    {
        out.push((function.as_ref().clone(), dict_type));
    }
    for child in crate::simplify::children(body) {
        collect_layout_pairs(&**child, dict_levels, out);
    }
}

fn substitute_evidence(
    body: phase::Expr<Types>,
    dict: usize,
    own: usize,
    _evidence: &phase::Expr<Types>,
) -> phase::Expr<Types> {
    body.map(&mut |node| match node {
        // Keep the dictionary parameter itself. Replacing every use with a free
        // evidence marker made the binder dead; simplification then removed it from
        // non-self-recursive workers while rewritten callers still supplied the
        // dictionary. The call-site type substitution already grounds all layout
        // annotations, which is what direct packed codegen needs.
        Expr::Apply(a, mut app)
            if matches!(&*app.function, Expr::Variable(_, Identifier::Bound(n)) if *n == own) =>
        {
            let annotation = app.argument.annotation().clone();
            app.argument = Rc::new(Expr::Variable(annotation, Identifier::Bound(dict)));
            Expr::Apply(a, app)
        }
        other => other,
    })
}

fn rewrite_layout_calls(
    body: phase::Expr<Types>,
    specs: &HashMap<(QualifiedName, Type), QualifiedName>,
) -> phase::Expr<Types> {
    body.map(&mut |node| match node {
        Expr::Apply(a, app) => {
            let target = match (&*app.function, concrete_layout_type(&app.argument)) {
                (
                    Expr::Variable(function_annotation, Identifier::Free(function)),
                    Some(dict_type),
                ) => specs
                    .get(&(function.as_ref().clone(), dict_type))
                    .map(|clone| (function_annotation.clone(), clone.clone())),
                _ => None,
            };
            match target {
                Some((function_annotation, clone)) => Expr::Apply(
                    a,
                    Apply {
                        function: Rc::new(Expr::Variable(
                            function_annotation,
                            Identifier::Free(Box::new(clone)),
                        )),
                        argument: app.argument,
                    },
                ),
                None => Expr::Apply(a, app),
            }
        }
        other => other,
    })
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
