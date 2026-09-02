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

#[derive(Debug, Clone)]
struct LayoutSlot {
    argument: usize,
    template: Type,
    saturation: usize,
}

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

        // Every compiler-derived layout dictionary among the leading constraint
        // arguments. A generic wrapper may have ordinary class dictionaries before
        // its layouts (`Eq beta, Memory_Layout entry, Memory_Layout state`), so the
        // old first-argument-only recognizer could never specialize that wrapper.
        let layout_slots: HashMap<QualifiedName, Vec<LayoutSlot>> = self
            .symbols
            .iter()
            .filter_map(|(name, sym)| match (name, sym) {
                (SymbolName::Term(qn), Symbol::Term(term))
                    if !qn.member().as_str().contains(SPEC_MARK)
                        && !qn.member().as_str().contains(LAYOUT_SPEC_MARK) =>
                {
                    let slots = leading_layout_slots(&term.body, &self.signatures);
                    (!slots.is_empty()).then(|| (qn.clone(), slots))
                }
                _ => None,
            })
            .collect();
        if std::env::var_os("DUMP_LAYOUT_SPECIALIZE").is_some() {
            let mut entries = layout_slots.iter().collect::<Vec<_>>();
            entries.sort_by_key(|(name, _)| *name);
            for (name, slots) in entries {
                eprintln!("[layout-slots] {name} {slots:?}");
            }
        }

        // Ground call sites `f w …` (f recursive-constrained, w a ground witness).
        let mut pairs: Vec<(QualifiedName, QualifiedName)> = Vec::new();
        for sym in self.symbols.values() {
            if let Symbol::Term(t) = sym {
                collect_pairs(&t.body, &dict_levels, &self.witnesses, &mut pairs);
            }
        }
        pairs.sort();
        pairs.dedup();
        if std::env::var_os("DUMP_SPECIALIZE").is_some() {
            for (f, w) in &pairs {
                eprintln!("[spec-pair] {f}  <-  {w}  (dict level {})", dict_levels[f]);
            }
        }

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
                    collect_layout_pairs(&t.body, &layout_slots, &mut layout_pairs);
                }
            }
            layout_pairs.sort();
            layout_pairs.dedup();
            layout_pairs.truncate(MAX_LAYOUT_SPECIALIZATIONS);
            if std::env::var_os("DUMP_LAYOUT_SPECIALIZE").is_some() {
                for pair in &layout_pairs {
                    eprintln!("[layout-pair] {pair:?}");
                }
            }

            let mut layout_specs = HashMap::new();
            let mut layout_fresh = Vec::new();
            for (function, dict_types) in layout_pairs {
                let clone_qn = QualifiedName::new(
                    function.module().clone(),
                    &format!(
                        "{}{LAYOUT_SPEC_MARK}{:016x}",
                        function.member().as_str(),
                        stable_hash(&dict_types)
                    ),
                );
                if !self
                    .symbols
                    .contains_key(&SymbolName::Term(clone_qn.clone()))
                    && let Some(Symbol::Term(term)) =
                        self.symbols.get(&SymbolName::Term(function.clone()))
                {
                    let substitutions = layout_substitutions(&layout_slots[&function], &dict_types)
                        .unwrap_or_default();
                    let body = term.body.apply(&substitutions);
                    layout_fresh.push((clone_qn.clone(), term.type_signature.clone(), body));
                }
                layout_specs.insert((function, dict_types), clone_qn);
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
                            body: rewrite_layout_calls(t.body, &layout_specs, &layout_slots),
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

fn layout_substitutions(slots: &[LayoutSlot], concrete: &[Type]) -> Option<Substitutions> {
    (slots.len() == concrete.len()).then_some(())?;
    let mut bindings = HashMap::new();
    for (slot, concrete) in slots.iter().zip(concrete) {
        match_type_pattern(&slot.template, concrete, &mut bindings)?;
    }
    Some(bindings.into_iter().collect::<Vec<_>>().into())
}

fn applied_constructor(ty: &Type) -> Option<&QualifiedName> {
    match ty {
        Type::Apply { constructor, .. } => applied_constructor(constructor),
        Type::Constructor(name) => Some(name),
        _ => None,
    }
}

/// Locate every Memory_Layout dictionary in a term's leading constraint-argument
/// prefix. Constraint parameters precede source parameters and may contain other
/// classes, so keep their true application index and bound level rather than
/// assuming the first parameter is the layout.
fn leading_layout_slots(
    mut body: &phase::Expr<Types>,
    signatures: &HashSet<QualifiedName>,
) -> Vec<LayoutSlot> {
    let saturation = lambda_arity(body);
    while let Expr::Ascription(_, ascription) = body {
        body = &ascription.ascribed_tree;
    }

    let Expr::RecursiveLambda(annotation, recursive) = body else {
        return Vec::new();
    };
    let mut annotation = annotation;
    let mut parameter = &recursive.lambda.parameter;
    let mut next = recursive.lambda.body.as_ref();
    let mut argument = 0;
    let mut slots = Vec::new();

    loop {
        let Type::Arrow { domain, .. } = &annotation.inferred_type else {
            break;
        };
        let Some(class) = applied_constructor(domain) else {
            break;
        };
        if !signatures.contains(class) {
            break;
        }
        if *class == memory_layout_class() && matches!(parameter, Identifier::Bound(_)) {
            slots.push(LayoutSlot {
                argument,
                template: domain.as_ref().clone(),
                saturation,
            });
        }

        argument += 1;
        while let Expr::Ascription(_, ascription) = next {
            next = &ascription.ascribed_tree;
        }
        let Expr::Lambda(next_annotation, lambda) = next else {
            break;
        };
        annotation = next_annotation;
        parameter = &lambda.parameter;
        next = lambda.body.as_ref();
    }
    slots
}

fn lambda_arity(mut body: &phase::Expr<Types>) -> usize {
    let mut arity = 0;
    loop {
        while let Expr::Ascription(_, ascription) = body {
            body = &ascription.ascribed_tree;
        }
        match body {
            Expr::RecursiveLambda(_, recursive) => {
                arity += 1;
                body = &recursive.lambda.body;
            }
            Expr::Lambda(_, lambda) => {
                arity += 1;
                body = &lambda.body;
            }
            _ => return arity,
        }
    }
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
                ..
            },
            Type::Apply {
                constructor: cc,
                argument: ca,
                ..
            },
        ) => {
            match_type_pattern(tc, cc, bindings)?;
            match_type_pattern(ta, ca, bindings)
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
            if dict_levels.contains_key(f.as_ref())
                && witnesses.contains(w.as_ref())
                && std::env::var_os("MARM_NO_SELECTOR_SPEC")
                    .map_or(true, |_| !f.member().as_str().contains('$'))
            {
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
    layout_slots: &HashMap<QualifiedName, Vec<LayoutSlot>>,
    out: &mut Vec<(QualifiedName, Vec<Type>)>,
) {
    if let Some((function, arguments)) = application_spine(body)
        && let Some(slots) = layout_slots.get(function)
    {
        let types = slots
            .iter()
            .map(|slot| {
                arguments
                    .get(slot.argument)
                    .and_then(|argument| concrete_layout_type(argument))
            })
            .collect::<Option<Vec<_>>>();
        if let Some(types) = types {
            out.push((function.clone(), types));
        }
    }
    for child in crate::simplify::children(body) {
        collect_layout_pairs(&**child, layout_slots, out);
    }
}

fn application_spine<A>(
    body: &Expr<A, Identifier>,
) -> Option<(&QualifiedName, Vec<&Expr<A, Identifier>>)> {
    let mut arguments = Vec::new();
    let mut head = body;
    while let Expr::Apply(_, application) = head {
        arguments.push(application.argument.as_ref());
        head = application.function.as_ref();
    }
    arguments.reverse();
    match head {
        Expr::Variable(_, Identifier::Free(function)) => Some((function, arguments)),
        _ => None,
    }
}

fn application_head_type(body: &phase::Expr<Types>) -> Option<&Type> {
    let mut head = body;
    while let Expr::Apply(_, application) = head {
        head = application.function.as_ref();
    }
    match head {
        Expr::Variable(annotation, Identifier::Free(_)) => Some(&annotation.inferred_type),
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

/// Recover the call site's own metavariables from the ground layout argument.
/// Those variables are fresh instantiations of the callee's scheme and therefore
/// differ from the variables substituted into the specialized definition.
fn layout_call_substitutions(
    body: &phase::Expr<Types>,
    slots: &[LayoutSlot],
    arguments: &[&phase::Expr<Types>],
) -> Option<Substitutions> {
    let mut function_type = application_head_type(body)?;
    let source_arity = arrow_arity(function_type);
    let saturation = slots.first()?.saturation;
    let constraint_arity = saturation.checked_sub(source_arity)?;
    let source_arguments = arguments.get(constraint_arity..)?;
    (source_arguments.len() == source_arity).then_some(())?;

    let mut bindings = HashMap::new();
    for argument in source_arguments {
        let Type::Arrow {
            domain, codomain, ..
        } = function_type
        else {
            return None;
        };
        match_type_pattern(&argument.annotation().inferred_type, domain, &mut bindings)?;
        function_type = codomain;
    }
    match_type_pattern(
        &body.annotation().inferred_type,
        function_type,
        &mut bindings,
    )?;
    Some(bindings.into_iter().collect::<Vec<_>>().into())
}

fn replace_application_head(node: phase::Expr<Types>, clone: &QualifiedName) -> phase::Expr<Types> {
    match node {
        Expr::Apply(annotation, mut application) => {
            application.function = Rc::new(replace_application_head(
                Rc::unwrap_or_clone(application.function),
                clone,
            ));
            Expr::Apply(annotation, application)
        }
        Expr::Variable(annotation, Identifier::Free(_)) => {
            Expr::Variable(annotation, Identifier::Free(Box::new(clone.clone())))
        }
        other => other,
    }
}

fn rewrite_layout_calls(
    body: phase::Expr<Types>,
    specs: &HashMap<(QualifiedName, Vec<Type>), QualifiedName>,
    slots: &HashMap<QualifiedName, Vec<LayoutSlot>>,
) -> phase::Expr<Types> {
    body.map(&mut |node| {
        // Wait for a saturated call. `Expr::map` is bottom-up, so rewriting the
        // first prefix that merely reaches the layout argument would hide the
        // original callee from the outer applications and leave their result
        // annotations polymorphic.
        let target = application_spine(&node).and_then(|(function, arguments)| {
            let function_slots = slots.get(function)?;
            (arguments.len() == function_slots[0].saturation).then_some(())?;
            let types = function_slots
                .iter()
                .map(|slot| {
                    arguments
                        .get(slot.argument)
                        .and_then(|argument| concrete_layout_type(argument))
                })
                .collect::<Option<Vec<_>>>()?;
            let clone = specs.get(&(function.clone(), types.clone()))?.clone();
            let Some(substitutions) = layout_call_substitutions(&node, function_slots, &arguments)
            else {
                return None;
            };
            Some((clone, substitutions))
        });
        target.map_or(node.clone(), |(clone, substitutions)| {
            replace_application_head(node, &clone).apply(&substitutions)
        })
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
                        function: Rc::new(Expr::Variable(
                            fa,
                            Identifier::Free(Box::new({
                                if std::env::var_os("DUMP_SPECIALIZE").is_some() {
                                    eprintln!("[spec-redirect] -> {clone}");
                                }
                                clone
                            })),
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
