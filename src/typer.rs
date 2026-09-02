use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem,
    ops::Deref,
    rc::Rc,
    slice::Iter,
    sync::atomic::{AtomicU32, Ordering},
    vec,
};

use thiserror::Error;
use tracing::instrument;

use crate::{
    ast::{
        self, Apply, Array, ArrowTypeExpr, Binding, Confinement, ConstraintExpression, Deconstruct,
        IfThenElse, Injection, Kind, Lambda, Literal, ProductElement, Projection, Record, Segment,
        SelfReferential, Sequence, Tree, Tuple, TupleTypeExpr, TypeAscription, TypeExpression,
        annotation::Annotated,
        constraints::{Witness, WitnessEnvironment},
        namer::{
            self, CoproductSymbol, DependencyMatrix, FieldSymbol, Identifier, Named, QualifiedName,
            RecordSymbol, Symbol, SymbolName, TermSymbol, TypeDefinition, TypeSymbol,
        },
        pattern::{
            ConstructorPattern, Denotation, MatchClause, Pattern, Shape, StructPattern,
            TuplePattern,
        },
    },
    compiler::{Located, LocatedError},
    parser::{self, ParseInfo},
    phase::{self, Phase},
};

pub struct Types;

impl phase::Phase for Types {
    type Annotation = TypeInfo;
    type TermId = Identifier;
    type TypeId = QualifiedName;
}

pub type SymbolTable = namer::SymbolTable<TypeInfo, QualifiedName, Identifier>;
type UntypedExpr = phase::Expr<Named>;
pub type Expr = phase::Expr<Types>;

pub fn display_list<A>(sep: &str, xs: &[A]) -> String
where
    A: fmt::Display,
{
    xs.iter()
        .map(|x| x.to_string())
        .collect::<Vec<_>>()
        .join(sep)
}

/// A non-expansive local binding can be generalized without changing when its
/// computation happens. Constrained expansive bindings stay monomorphic until
/// local dictionary abstraction is implemented.
fn is_generalizable_value<A, Id>(expr: &ast::Expr<A, Id>) -> bool {
    match expr {
        ast::Expr::Variable(..)
        | ast::Expr::Constant(..)
        | ast::Expr::Lambda(..)
        | ast::Expr::RecursiveLambda(..)
        | ast::Expr::InvokeBridge(..) => true,
        ast::Expr::Tuple(_, Tuple { elements }) => elements
            .iter()
            .all(|element| is_generalizable_value(element)),
        ast::Expr::Record(_, Record { fields }) => fields
            .iter()
            .all(|(_, value)| is_generalizable_value(value)),
        ast::Expr::Inject(_, Injection { arguments, .. }) => arguments
            .iter()
            .all(|argument| is_generalizable_value(argument)),
        ast::Expr::Let(_, Binding { bound, body, .. }) => {
            is_generalizable_value(bound) && is_generalizable_value(body)
        }
        ast::Expr::Project(_, Projection { base, .. })
        | ast::Expr::Ascription(
            _,
            TypeAscription {
                ascribed_tree: base,
                ..
            },
        ) => is_generalizable_value(base),
        _ => false,
    }
}

impl<A> namer::SymbolTable<A, namer::QualifiedName, namer::Identifier> {
    pub fn terms(
        &self,
        order: Iter<&SymbolName>,
    ) -> Vec<&TermSymbol<A, namer::QualifiedName, namer::Identifier>> {
        self.extract_symbols(order, |sym| {
            if let namer::Symbol::Term(sym) = sym {
                Some(sym)
            } else {
                None
            }
        })
    }

    pub fn type_symbols(
        &self,
        order: Iter<&SymbolName>,
    ) -> Vec<&namer::TypeSymbol<namer::QualifiedName>> {
        self.extract_symbols(order, |sym| {
            if let namer::Symbol::Type(sym) = sym {
                Some(sym)
            } else {
                None
            }
        })
    }

    fn extract_symbols<F, Sym>(&self, terms: Iter<&SymbolName>, select: F) -> Vec<&Sym>
    where
        F: Fn(&namer::Symbol<A, namer::QualifiedName, namer::Identifier>) -> Option<&Sym>,
    {
        terms
            .filter_map(|&id| self.symbols.get(id))
            .filter_map(select)
            .collect()
    }

    pub fn dependency_matrix(&self) -> DependencyMatrix<SymbolName> {
        let mut matrix = DependencyMatrix::default();

        // This function is incredibly inefficient.
        for (id, symbol) in &self.symbols {
            matrix.add_edge(id.clone(), symbol.dependencies().into_iter().collect());
            if self.witnesses.contains(id.name()) {
                matrix.add_witness(id.clone());
            }
        }

        // Also add constraint methods
        for constraint_name in &self.signatures {
            let constraint = self
                .symbols
                .get(&SymbolName::Type(constraint_name.clone()))
                .and_then(|symbol| {
                    if let Symbol::Type(symbol) = symbol
                        && let TypeDefinition::Signature(symbol) = &symbol.definition
                    {
                        Some(symbol)
                    } else {
                        None
                    }
                })
                .expect("Internal error");
            let semantic_context = constraint_name.module();

            for method in constraint
                .vtable
                .fields
                .iter()
                .filter(|f| !is_super_field(&f.name))
            {
                let name = QualifiedName::new(semantic_context.clone(), method.name.as_str());
                matrix.add_edge(SymbolName::Term(name), vec![]);
            }
        }

        for foreign in &self.foreign_terms {
            matrix.add_edge(SymbolName::Term(foreign.name.clone()), vec![]);
        }

        matrix
    }
}

impl phase::SymbolTable<Types> {
    /// Preserve the source-level owner of every expression for runtime diagnostics.
    pub fn stamp_enclosing_terms(mut self) -> Self {
        for symbol in self.symbols.values_mut() {
            if let namer::Symbol::Term(term) = symbol {
                let owner = term.name.clone();
                term.body = term.body.map_annotation(&|info| {
                    let mut info = info.clone();
                    info.enclosing_term = Some(owner.clone());
                    info
                });
            }
        }
        self
    }
}

impl phase::TypeSignature<Named> {
    fn desugar_constraints(&mut self) {
        for c in mem::take(&mut self.constraints).into_iter().rev() {
            self.prepend_argument(c.annotation, c.into_type_expression());
        }
    }

    fn prepend_argument(
        &mut self,
        annotation: <Named as Phase>::Annotation,
        argument: phase::TypeExpression<Named>,
    ) {
        self.body = TypeExpression::Arrow(
            annotation,
            ArrowTypeExpr {
                capture: ast::Confinement::fresh(),
                domain: argument.into(),
                codomain: mem::take(&mut self.body).into(),
            },
        );
    }

    pub fn map_body<F>(self, f: F) -> Self
    where
        F: FnOnce(phase::TypeExpression<Named>) -> phase::TypeExpression<Named>,
    {
        Self {
            universal_quantifiers: self.universal_quantifiers,
            constraints: self.constraints,
            body: f(self.body),
            phase: PhantomData,
        }
    }

    pub fn type_scheme(
        &self,
        context_type_param_map: &HashMap<parser::Identifier, MetaVariable>,
        ctx: &TypingContext,
    ) -> Typing<TypeScheme> {
        let type_params = self
            .universal_quantifiers
            .iter()
            .map(|id| {
                (
                    id.name.clone(),
                    MetaVariable::fresh_with_kind(id.kind.clone()),
                )
            })
            .collect::<Vec<_>>();

        let type_param_map = context_type_param_map
            .iter()
            .map(|(p, q)| (p.clone(), q.clone()))
            .chain(type_params.iter().cloned())
            .collect::<HashMap<_, _>>();

        let constraints = self
            .constraints
            .iter()
            .map(|c| Constraint::from_constraint_expr(&type_param_map, c, ctx))
            .collect::<Typing<Vec<_>>>()?;

        let underlying = self.body.synthesize_type(&type_param_map, ctx)?;
        // Capability ascriptions can refine the indexed kind of a quantified
        // variable. Keep the scheme's binder in lockstep with the occurrence in
        // the synthesized body; metavariable identity itself remains unchanged.
        let underlying_variables = underlying.variables();
        let quantifiers = type_params
            .iter()
            .map(|(_, parameter)| {
                underlying_variables
                    .iter()
                    .find(|variable| *variable == parameter)
                    .cloned()
                    .unwrap_or_else(|| parameter.clone())
            })
            .collect();
        let context_confinements = context_type_param_map
            .values()
            .flat_map(|parameter| parameter.kind().confinement_variables())
            .collect::<BTreeSet<_>>();
        let confinement_quantifiers = underlying
            .confinement_variables()
            .difference(&context_confinements)
            .copied()
            .collect();

        Ok(TypeScheme {
            quantifiers,
            confinement_quantifiers,
            underlying,
            constraints: ConstraintSet::from(constraints.as_slice()),
        })
    }
}

impl phase::ConstraintExpression<Named> {
    fn from_signature_type_constructor(
        annotation: <Named as Phase>::Annotation,
        type_constructor: &TypeConstructor,
    ) -> ConstraintExpression<<Named as Phase>::Annotation, QualifiedName> {
        ConstraintExpression {
            annotation,
            class: type_constructor.definition().name.clone(),
            parameters: type_constructor
                .definition()
                .defining_symbol
                .type_parameters()
                .iter()
                .map(|tv| TypeExpression::Parameter(annotation, tv.name.clone()))
                .collect(),
        }
    }
}

/// How a term's body refers to its own (global) name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SelfReference {
    /// The body never names itself.
    None,
    /// Every self-reference sits under a lambda, so the value's own global slot
    /// is only read once that lambda is later invoked -- by which time `startup`
    /// has filled it. Sound value recursion with no backend support required.
    Guarded,
    /// At least one self-reference is evaluated while the binding's own value is
    /// still being computed (e.g. `x := x`, `ones := Cons 1 ones`). A strict
    /// backend would read the still-empty slot, so this must be rejected.
    Unguarded,
}

impl SelfReference {
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Unguarded, _) | (_, Self::Unguarded) => Self::Unguarded,
            (Self::Guarded, _) | (_, Self::Guarded) => Self::Guarded,
            _ => Self::None,
        }
    }
}

/// Classify how `body` refers to its own name `own`. A self-reference under a
/// lambda is *guarded* (its evaluation is deferred to call time, when the global
/// slot is populated); one evaluated eagerly during the binding's own init is
/// *unguarded*. Self-references carried as a bound De Bruijn (the `RecursiveLambda`
/// path for lambda-valued bindings) are handled elsewhere and never appear as a
/// `Free(own)` here.
fn classify_self_reference(body: &UntypedExpr, own: &QualifiedName) -> SelfReference {
    fn walk(expr: &UntypedExpr, own: &QualifiedName, under_lambda: bool) -> SelfReference {
        match expr {
            UntypedExpr::Variable(_, Identifier::Free(name)) if name.as_ref() == own => {
                if under_lambda {
                    SelfReference::Guarded
                } else {
                    SelfReference::Unguarded
                }
            }
            UntypedExpr::Lambda(_, Lambda { body, .. }) => walk(body, own, true),
            UntypedExpr::RecursiveLambda(_, SelfReferential { lambda, .. }) => {
                walk(&lambda.body, own, true)
            }
            other => crate::simplify::children(other)
                .into_iter()
                .fold(SelfReference::None, |acc, child| {
                    acc.join(walk(&**child, own, under_lambda))
                }),
        }
    }
    walk(body, own, false)
}

impl phase::SymbolTable<Named> {
    pub fn elaborate_compilation_unit(mut self) -> Typing<phase::SymbolTable<Types>> {
        crate::profile::time("type checker: check signature cycles", || {
            self.check_supersignature_acyclicity()
        })?;
        crate::profile::time("type checker: check alias cycles", || {
            self.check_type_alias_acyclicity()
        })?;

        let mut ctx =
            crate::profile::time("type checker: elaborate types", || self.elaborate_types())?;

        crate::profile::time("type checker: elaborate foreign terms", || {
            self.elaborate_foreign_terms(&mut ctx)
        })?;

        // Gives rise to signature method placeholders -- term typer needs this
        let selectors_names = crate::profile::time("type checker: elaborate constraints", || {
            self.elaborate_constraints(&mut ctx)
        })?;

        // This runs the term typer core
        let symbols = crate::profile::time("type checker: elaborate terms", || {
            self.elaborate_terms(&selectors_names.iter().collect::<Vec<_>>(), &mut ctx)
        })?;

        Ok(SymbolTable {
            module_members: self.module_members,
            member_modules: self.member_modules,
            symbols,
            base_imports: self.base_imports,
            module_imports: self.module_imports,
            scope_roots: self.scope_roots,
            foreign_terms: self.foreign_terms,
            signatures: self.signatures,
            witnesses: self.witnesses,
            constructor_opacity: self.constructor_opacity,
            member_visibility: self.member_visibility,
        })
    }

    /// The direct supersignatures of `sig` — the class names of its `|-` context,
    /// read off the signature's vtable record symbol. Empty for non-signatures.
    fn direct_supersignatures(&self, sig: &QualifiedName) -> Vec<QualifiedName> {
        if let Some(Symbol::Type(TypeSymbol {
            definition: TypeDefinition::Signature(signature),
            ..
        })) = self.symbols.get(&SymbolName::Type(sig.clone()))
        {
            signature
                .supersignatures
                .iter()
                .map(|c| c.class.clone())
                .collect()
        } else {
            Vec::new()
        }
    }

    /// Reject cyclic supersignature declarations (`A requires B`, `B requires A`)
    /// before any elaboration walks the super-edges.
    fn check_supersignature_acyclicity(&self) -> Typing<()> {
        let mut done: HashSet<QualifiedName> = HashSet::new();
        let mut signatures = self.signatures.iter().cloned().collect::<Vec<_>>();
        signatures.sort();
        for sig in &signatures {
            self.detect_super_cycle(sig, &mut Vec::new(), &mut done)?;
        }
        Ok(())
    }

    fn check_type_alias_acyclicity(&self) -> Typing<()> {
        fn visit(
            table: &phase::SymbolTable<Named>,
            name: &QualifiedName,
            path: &mut Vec<QualifiedName>,
            done: &mut HashSet<QualifiedName>,
        ) -> Typing<()> {
            if done.contains(name) {
                return Ok(());
            }
            if let Some(start) = path.iter().position(|candidate| candidate == name) {
                let mut cycle = path[start..].to_vec();
                cycle.push(name.clone());
                return Err(TypeError::CyclicTypeAlias { cycle }.at(ParseInfo::default()));
            }
            let Some(Symbol::Type(TypeSymbol {
                definition: TypeDefinition::Alias(alias),
                ..
            })) = table.symbols.get(&SymbolName::Type(name.clone()))
            else {
                return Ok(());
            };

            path.push(name.clone());
            let mut dependencies = alias
                .body
                .free_variables()
                .into_iter()
                .cloned()
                .collect::<Vec<_>>();
            dependencies.sort();
            for dependency in dependencies {
                visit(table, &dependency, path, done)?;
            }
            path.pop();
            done.insert(name.clone());
            Ok(())
        }

        let mut aliases = self
            .symbols
            .iter()
            .filter_map(|(name, symbol)| {
                matches!(
                    symbol,
                    Symbol::Type(TypeSymbol {
                        definition: TypeDefinition::Alias(_),
                        ..
                    })
                )
                .then(|| name.name().clone())
            })
            .collect::<Vec<_>>();
        aliases.sort();
        let mut done = HashSet::new();
        for alias in aliases {
            visit(self, &alias, &mut Vec::new(), &mut done)?;
        }
        Ok(())
    }

    fn detect_super_cycle(
        &self,
        node: &QualifiedName,
        path: &mut Vec<QualifiedName>,
        done: &mut HashSet<QualifiedName>,
    ) -> Typing<()> {
        if done.contains(node) {
            return Ok(());
        }
        if let Some(start) = path.iter().position(|n| n == node) {
            let mut cycle = path[start..].to_vec();
            cycle.push(node.clone());
            return Err(TypeError::CyclicSupersignature { cycle }.at(ParseInfo::default()));
        }

        path.push(node.clone());
        for sup in self.direct_supersignatures(node) {
            self.detect_super_cycle(&sup, path, done)?;
        }
        path.pop();
        done.insert(node.clone());
        Ok(())
    }

    #[instrument(skip_all)]
    fn elaborate_terms(
        &self,
        selector_names: &[&SymbolName],
        ctx: &mut TypingContext,
    ) -> Typing<HashMap<SymbolName, Symbol<TypeInfo, QualifiedName, Identifier>>> {
        let mut typed_symbols = HashMap::with_capacity(self.symbols.len());

        let witnesses = self.elaborate_witnesses(&ctx)?;
        let witness_deps = witnesses
            .dependency_matrix(&ctx.types)
            .map_err(|e| e.at(ParseInfo::default()))?;

        let mut deps = self.dependency_matrix();
        deps.merge(witness_deps.map(SymbolName::Term));

        let selector_names = selector_names.into_iter().copied().collect::<HashSet<_>>();

        // This types and binds all terms in ctx.terms
        let mut typed_terms = self.type_terms(
            &mut typed_symbols,
            deps.in_resolvable_order()
                .iter()
                .copied()
                .filter(|t| !selector_names.contains(t)),
            ctx,
        )?;

        self.elaborate_signature_type_constructors(ctx)?;

        let typed_selectors =
            self.type_terms(&mut typed_symbols, selector_names.iter().copied(), ctx)?;

        for (term_symbol, typed) in &typed_selectors {
            tracing::trace!("typed selector {} : {}", term_symbol.name, typed.tree);
        }

        typed_terms.extend(typed_selectors);

        for (symbol, term) in typed_terms {
            let pi = term.tree.annotation().parse_info;

            // The `given` constraints are the ones this term *declares* (its
            // signature's `|-` context), reconciled to the body's metavariables.
            // They become the dictionary parameters. The body's *inferred*
            // constraints (`term.constraints`) are the `wanted` set, discharged
            // against the givens -- including via supersignature projection. With
            // no signature, declared == inferred (current behaviour).
            let given = given_constraints(symbol, &term, ctx)?;

            // Zonk the wanted constraints through the term's own substitution before
            // discharge. A constraint collected inside a nested recursive lambda can
            // still carry a metavariable (`Sink $meta`) that later unification bound
            // to a concrete head (`$meta := Box`); without re-applying the substitution
            // the stale copy survives *alongside* its ground form and, being
            // variable-headed, is misclassified as parametric -> a spurious leading
            // dictionary parameter. For a witness that turns the produced record into a
            // `λself. record` function that callers project unforced (a null deref). The
            // set re-collects, so the stale copy collapses onto its ground twin.
            let wanted = term.constraints.apply(&term.substitutions);

            // this has to bind every term in TypingContext so that later elaborations
            // can discover constraints (type and order)
            // So it needs the name!
            let expr =
                elaborate_term_constraints(&symbol.name, &witnesses, given, wanted, term.tree, ctx)
                    .map_err(|e| e.at(pi))?;

            tracing::trace!("insert {} := {}", symbol.name, expr);
            typed_symbols.insert(
                SymbolName::Term(symbol.name.clone()),
                Symbol::Term(TermSymbol {
                    name: symbol.name.clone(),
                    type_signature: symbol.type_signature.clone(),
                    body: expr.into(),
                }),
            );
        }

        Ok(typed_symbols)
    }

    fn type_terms<'a>(
        &self,
        symbols: &mut HashMap<SymbolName, Symbol<TypeInfo, QualifiedName, Identifier>>,
        evaluation_order: impl Iterator<Item = &'a SymbolName>,
        ctx: &mut TypingContext,
    ) -> Typing<Vec<(&TermSymbol<ParseInfo, QualifiedName, Identifier>, Typed)>> {
        let mut typed_terms = Vec::default();

        for name in evaluation_order {
            // Rewrite in terms of a match instead?
            if let SymbolName::Term(term_name) = &name
                // signature method placeholders are already typed
                && !ctx.terms.free.contains_key(&term_name)
                && let Symbol::Term(symbol) = &self.symbols[&name]
            {
                //                tracing::trace!("@@@ {} := {:?}", symbol.name, symbol.body);
                let label = format!("type term: {}", symbol.name);
                typed_terms.push((
                    symbol,
                    crate::profile::time_if_slow(label, 10.0, || self.type_term(symbol, ctx))?,
                ))
            }

            if let SymbolName::Type(..) = name
                && let Symbol::Type(symbol) = &self.symbols[&name]
            {
                symbols.insert(name.clone(), Symbol::Type(symbol.clone()));
            }
        }
        Ok(typed_terms)
    }

    fn elaborate_witnesses(&self, ctx: &TypingContext) -> Typing<WitnessEnvironment> {
        let mut witnesses = WitnessEnvironment::default();

        // Deterministic order: witnesses are registered (and instantiated with
        // fresh variables) here; HashSet order would make resolution flaky.
        let mut witness_names = self.witnesses.iter().collect::<Vec<_>>();
        witness_names.sort();
        for witness_name in witness_names {
            let Symbol::Term(symbol) = &self.symbols[&SymbolName::Term(witness_name.clone())]
            else {
                panic!("non-term witness")
            };

            witnesses.register(Witness::from_type_signature(
                witness_name.clone(),
                symbol
                    .type_signature
                    .clone()
                    .expect("all witnesses have type signatures"),
                ctx,
            )?);
        }

        Ok(witnesses)
    }

    fn infer_type_kinds(&self) -> Typing<HashMap<QualifiedName, Kind>> {
        fn expression_kind(
            table: &phase::SymbolTable<Named>,
            expression: &phase::TypeExpression<Named>,
            parameters: &HashMap<parser::Identifier, Kind>,
            kinds: &HashMap<QualifiedName, Kind>,
        ) -> Typing<Kind> {
            match expression {
                TypeExpression::Constructor(pi, name) => {
                    let Some(Symbol::Type(_)) = table.symbols.get(&SymbolName::Type(name.clone()))
                    else {
                        return Err(TypeError::UndefinedType(name.clone()).at(*pi));
                    };
                    kinds
                        .get(name)
                        .cloned()
                        .ok_or_else(|| TypeError::UndefinedType(name.clone()).at(*pi))
                }
                TypeExpression::Parameter(pi, parameter) => parameters
                    .get(parameter)
                    .cloned()
                    .ok_or_else(|| TypeError::UnquantifiedTypeParameter(parameter.clone()).at(*pi)),
                TypeExpression::Apply(pi, application) => {
                    expression_kind(table, &application.function, parameters, kinds)?
                        .apply(expression_kind(
                            table,
                            &application.argument,
                            parameters,
                            kinds,
                        )?)
                        .map_err(|error| error.at(*pi))
                }
                TypeExpression::ConfinementAscription(pi, body, required) => {
                    let kind = expression_kind(table, body, parameters, kinds)?;
                    let actual = kind.confinement().cloned().ok_or_else(|| {
                        TypeError::ExpectedMonotypeKind { kind: kind.clone() }.at(*pi)
                    })?;
                    let required = Confinement::from(*required);
                    let substitutions = actual.require(required.clone()).ok_or_else(|| {
                        TypeError::ConfinementMismatch {
                            lhs: actual,
                            rhs: required,
                        }
                        .at(*pi)
                    })?;
                    Ok(kind.apply_confinement_substitutions(&substitutions))
                }
                TypeExpression::Arrow(pi, arrow) => {
                    for component in [&arrow.domain, &arrow.codomain] {
                        let kind = expression_kind(table, component, parameters, kinds)?;
                        if !kind.is_star() {
                            return Err(TypeError::ExpectedMonotypeKind { kind }.at(*pi));
                        }
                    }
                    Ok(Kind::Star(arrow.capture.clone()))
                }
                TypeExpression::Tuple(pi, tuple) => Ok(Kind::Star(Confinement::join(
                    tuple
                        .0
                        .iter()
                        .map(|element| {
                            let kind = expression_kind(table, element, parameters, kinds)?;
                            kind.confinement()
                                .cloned()
                                .ok_or_else(|| TypeError::ExpectedMonotypeKind { kind }.at(*pi))
                        })
                        .collect::<Typing<Vec<_>>>()?,
                ))),
            }
        }

        fn signature_confinement(
            table: &phase::SymbolTable<Named>,
            signature: &phase::TypeSignature<Named>,
            enclosing_parameters: &HashMap<parser::Identifier, Kind>,
            kinds: &HashMap<QualifiedName, Kind>,
        ) -> Typing<Confinement> {
            let mut parameters = enclosing_parameters.clone();
            parameters.extend(
                signature
                    .universal_quantifiers
                    .iter()
                    .map(|parameter| (parameter.name.clone(), parameter.kind.clone())),
            );
            let kind = expression_kind(table, &signature.body, &parameters, kinds)?;
            kind.confinement().cloned().ok_or_else(|| {
                TypeError::ExpectedMonotypeKind { kind }.at(*signature.body.annotation())
            })
        }

        fn is_fixed(symbol: &TypeSymbol<QualifiedName>) -> bool {
            matches!(
                symbol.origin,
                namer::TypeOrigin::Builtin | namer::TypeOrigin::Foreign
            ) || matches!(symbol.opacity, namer::Access::Within(_))
                && matches!(
                    symbol.kind.result_confinement(),
                    Some(Confinement::Confined | Confinement::Unconfined)
                )
        }

        let mut symbols = self
            .symbols
            .values()
            .filter_map(|symbol| match symbol {
                Symbol::Type(symbol) => Some((symbol.qualified_name(), symbol)),
                _ => None,
            })
            .collect::<Vec<_>>();
        symbols.sort_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));

        let mut kinds = symbols
            .iter()
            .map(|(name, symbol)| {
                let kind = if is_fixed(symbol) {
                    symbol.kind.clone()
                } else {
                    symbol.kind.with_result_confinement(Confinement::Unconfined)
                };
                (name.clone(), kind)
            })
            .collect::<HashMap<_, _>>();

        // Equations are monotone joins over a finite lattice. Starting every
        // inferred result at unconfined computes the least fixed point, including
        // mutually recursive declarations.
        for iteration in 0..=symbols.len() + 1 {
            let mut changed = false;
            let previous = kinds.clone();

            for (name, symbol) in &symbols {
                if is_fixed(symbol) {
                    continue;
                }

                let parameters = symbol
                    .type_parameters()
                    .iter()
                    .map(|parameter| (parameter.name.clone(), parameter.kind.clone()))
                    .collect::<HashMap<_, _>>();

                let next = match &symbol.definition {
                    TypeDefinition::Record(record) => {
                        symbol.kind.with_result_confinement(Confinement::join(
                            record
                                .fields
                                .iter()
                                .map(|field| {
                                    signature_confinement(
                                        self,
                                        &field.type_signature,
                                        &parameters,
                                        &previous,
                                    )
                                })
                                .collect::<Typing<Vec<_>>>()?,
                        ))
                    }
                    TypeDefinition::Signature(signature) => {
                        symbol.kind.with_result_confinement(Confinement::join(
                            signature
                                .vtable
                                .fields
                                .iter()
                                .map(|field| {
                                    signature_confinement(
                                        self,
                                        &field.type_signature,
                                        &parameters,
                                        &previous,
                                    )
                                })
                                .collect::<Typing<Vec<_>>>()?,
                        ))
                    }
                    TypeDefinition::Coproduct(coproduct) => {
                        symbol.kind.with_result_confinement(Confinement::join(
                            coproduct
                                .constructors
                                .iter()
                                .flat_map(|constructor| constructor.signature.iter())
                                .map(|field| {
                                    let kind =
                                        expression_kind(self, field, &parameters, &previous)?;
                                    kind.confinement().cloned().ok_or_else(|| {
                                        TypeError::ExpectedMonotypeKind { kind }
                                            .at(*field.annotation())
                                    })
                                })
                                .collect::<Typing<Vec<_>>>()?,
                        ))
                    }
                    TypeDefinition::Alias(alias) => {
                        let body_kind = expression_kind(self, &alias.body, &parameters, &previous)?;
                        symbol.type_parameters().iter().rev().fold(
                            body_kind,
                            |codomain, parameter| {
                                Kind::Arrow(parameter.kind.clone().into(), codomain.into())
                            },
                        )
                    }
                    TypeDefinition::BaseType(_) => continue,
                };

                if previous.get(name) != Some(&next) {
                    kinds.insert(name.clone(), next);
                    changed = true;
                }
            }

            if !changed {
                return Ok(kinds);
            }
            assert!(
                iteration <= symbols.len(),
                "confinement kind inference did not converge"
            );
        }

        unreachable!("finite confinement inference loop must converge")
    }

    fn elaborate_types(&self) -> Typing<TypingContext> {
        let mut ctx = TypingContext::default();
        let inferred_kinds = self.infer_type_kinds()?;

        for symbol in self.symbols.iter().filter_map(|(_, sym)| match sym {
            Symbol::Type(symbol) => Some(symbol),
            _ => None,
        }) {
            let mut symbol = symbol.clone();
            if let Some(kind) = inferred_kinds.get(&symbol.qualified_name()) {
                symbol.kind = kind.clone();
            }
            ctx.bind_type(
                symbol.qualified_name().clone(),
                TypeConstructor::from_symbol(&symbol),
            );
        }

        ctx.elaborate_type_constructors()?;

        Ok(ctx)
    }

    fn elaborate_constraints(&mut self, ctx: &mut TypingContext) -> Typing<Vec<SymbolName>> {
        self.insert_signature_method_placeholders(ctx)?;
        let selector_terms = self.elaborate_signature_method_selectors(ctx)?;
        self.symbols.extend(
            selector_terms
                .iter()
                .map(|t| (SymbolName::Term(t.name.clone()), Symbol::Term(t.clone()))),
        );

        self.lift_constrained_witness_methods(ctx);

        Ok(selector_terms
            .into_iter()
            .map(|term| SymbolName::Term(term.name))
            .collect())
    }

    /// A signature method that carries its own constraint (e.g.
    /// `mconcat :: ∀α. Monoid α |- m α -> α`) is a rank-2 field: its value must be
    /// a polymorphic, dictionary-taking function. That cannot be discharged at the
    /// witness/builder level, so -- mirroring how accessor selectors are emitted as
    /// top-level symbols -- we lift each such witness method body to its own
    /// top-level term `<witness>$<method>` and replace the record field with a
    /// reference to it. The lifted term then rides the ordinary type + discharge
    /// path, so its constraint becomes a leading dictionary parameter of the field.
    fn lift_constrained_witness_methods(&mut self, ctx: &TypingContext) {
        // Method names whose signature type carries a constraint. Ordinary methods
        // (e.g. `eq`) stay inline so the witness can discharge its own premises.
        let mut constrained_methods: HashSet<parser::Identifier> = HashSet::new();
        for signature in &self.signatures {
            if let Some(tc) = ctx.types.lookup(signature)
                && let TypeDefinition::Signature(sig) = &tc.definition().defining_symbol.definition
            {
                for field in &sig.vtable.fields {
                    if !field.type_signature.constraints.is_empty() {
                        constrained_methods.insert(field.name.clone());
                    }
                }
            }
        }
        if constrained_methods.is_empty() {
            return;
        }

        // Collect the fields to lift (borrow self.symbols immutably first).
        type NamedExpr = ast::Expr<ParseInfo, Identifier>;
        let mut lifts: Vec<(
            QualifiedName,
            parser::Identifier,
            QualifiedName,
            Rc<NamedExpr>,
        )> = Vec::new();
        let mut witness_names = self.witnesses.iter().cloned().collect::<Vec<_>>();
        witness_names.sort();
        for witness in witness_names {
            let Some(Symbol::Term(symbol)) = self.symbols.get(&SymbolName::Term(witness.clone()))
            else {
                continue;
            };
            // The witness body is a record, wrapped in an ascription to the
            // instance's dictionary type.
            let record = match &symbol.body {
                ast::Expr::Record(_, record) => record,
                ast::Expr::Ascription(_, ascription) => match ascription.ascribed_tree.as_ref() {
                    ast::Expr::Record(_, record) => record,
                    _ => continue,
                },
                _ => continue,
            };
            for (field_name, field_body) in &record.fields {
                if constrained_methods.contains(field_name) {
                    let lifted_name = QualifiedName::new(
                        witness.module().clone(),
                        &format!("{}${}", witness.member().as_str(), field_name.as_str()),
                    );
                    lifts.push((
                        witness.clone(),
                        field_name.clone(),
                        lifted_name,
                        field_body.clone(),
                    ));
                }
            }
        }

        for (witness, field_name, lifted_name, field_body) in lifts {
            let pi = *field_body.annotation();

            self.symbols.insert(
                SymbolName::Term(lifted_name.clone()),
                Symbol::Term(TermSymbol {
                    name: lifted_name.clone(),
                    type_signature: None,
                    body: Rc::unwrap_or_clone(field_body),
                }),
            );

            let Some(Symbol::Term(symbol)) =
                self.symbols.get_mut(&SymbolName::Term(witness.clone()))
            else {
                continue;
            };
            let record = match &mut symbol.body {
                ast::Expr::Record(_, record) => Some(record),
                ast::Expr::Ascription(_, ascription) => {
                    match Rc::make_mut(&mut ascription.ascribed_tree) {
                        ast::Expr::Record(_, record) => Some(record),
                        _ => None,
                    }
                }
                _ => None,
            };
            if let Some(record) = record {
                let reference = Rc::new(ast::Expr::Variable(
                    pi,
                    Identifier::Free(lifted_name.clone().into()),
                ));
                for (name, value) in &mut record.fields {
                    if *name == field_name {
                        *value = reference.clone();
                    }
                }
            }
        }
    }

    fn elaborate_signature_type_constructors(&self, ctx: &mut TypingContext) -> Typing<()> {
        for signature in &self.signatures {
            let mut type_constructor = ctx
                .types
                .bindings
                .remove(signature)
                .expect("internal error: constraint name does not match type constructor.");

            let signature_constraint = ConstraintExpression::from_signature_type_constructor(
                ParseInfo::default(),
                &type_constructor,
            );

            if let TypeDefinition::Signature(sig) =
                &mut type_constructor.definition_mut().defining_symbol.definition
            {
                for field in &mut sig.vtable.fields {
                    let pi = *field.type_signature.body.annotation();
                    let mut c = signature_constraint.clone();
                    c.annotation = pi;

                    field.type_signature.desugar_constraints();
                }

                // Phase 2 (supersignatures): encode each supersignature as a
                // hidden `$super$<Class>` field of the vtable holding that super's
                // dictionary. `$` can't start a surface identifier, so it can't
                // collide with a method; the `$super$` fields are filtered out of
                // the method-facing loops (selectors/placeholders/deps) so they
                // stay pure data. See notes/supersignatures.md.
                let super_fields = sig
                    .supersignatures
                    .iter()
                    .map(|c| FieldSymbol {
                        name: super_field_name(&c.class),
                        type_signature: ast::TypeSignature {
                            universal_quantifiers: Vec::new(),
                            constraints: Vec::new(),
                            body: c.clone().into_type_expression(),
                            phase: PhantomData,
                        },
                    })
                    .collect::<Vec<_>>();
                sig.vtable.fields.extend(super_fields);
            }

            type_constructor = type_constructor.reelaborate(ctx)?;

            ctx.types
                .bindings
                .insert(signature.clone(), type_constructor);
        }

        Ok(())
    }

    // This has to leave the constaints in the signature
    fn elaborate_signature_method_selectors(
        &self,
        ctx: &TypingContext,
    ) -> Typing<Vec<TermSymbol<ParseInfo, QualifiedName, Identifier>>> {
        let mut symbols = Vec::with_capacity(2 * self.signatures.len());
        let pi = ParseInfo::default();

        for c in &self.signatures {
            let type_constructor = ctx
                .types
                .lookup(c)
                .cloned()
                .expect("internal error: constraint name does not match type constructor.");

            let signature_constraint =
                ConstraintExpression::from_signature_type_constructor(pi, &type_constructor);

            if let TypeDefinition::Signature(sig) =
                &type_constructor.definition().defining_symbol.definition
            {
                for field in sig
                    .vtable
                    .fields
                    .iter()
                    .filter(|f| !is_super_field(&f.name))
                {
                    let method_arity = field.type_signature.body.arrow_arity();
                    tracing::trace!("{} {method_arity}", field.name);
                    let method_dictionary_count = field.type_signature.constraints.len();

                    let name = QualifiedName::new(
                        type_constructor.defining_context().clone(),
                        &format!(
                            "{}${}",
                            type_constructor.definition().name.member.as_str(),
                            field.name.as_str()
                        ),
                    );

                    // The selector's dictionaries are injected at call sites in
                    // ConstraintSet (BTreeSet) order, i.e. sorted by class name. Lay
                    // the body and the type out in that same order, otherwise the
                    // fixed slot the signature method is projected from disagrees with
                    // the injection whenever the signature class does not sort first
                    // (e.g. `Traversable` after `Applicative`). `None` marks the
                    // signature dictionary; `Some(j)` the method's j-th own dictionary.
                    let mut constraints: Vec<(Option<usize>, phase::ConstraintExpression<Named>)> =
                        vec![(None, signature_constraint.clone())];
                    for (j, c) in field.type_signature.constraints.iter().enumerate() {
                        constraints.push((Some(j), c.clone()));
                    }
                    constraints.sort_by(|(_, a), (_, b)| a.class.cmp(&b.class));

                    let num_constraints = constraints.len();
                    let slot = |origin: Option<usize>| {
                        1 + constraints.iter().position(|(o, _)| *o == origin).unwrap()
                    };

                    // Project the signature method from the signature dictionary, then
                    // apply the method's own dictionaries (in method order) and finally
                    // the value arguments (which follow all dictionaries).
                    let mut spine = ast::Expr::Project(
                        pi,
                        Projection {
                            base: ast::Expr::Variable(pi, Identifier::Bound(slot(None))).into(),
                            select: ProductElement::Name(field.name.clone()),
                        },
                    );
                    for j in 0..method_dictionary_count {
                        spine = ast::Expr::Apply(
                            pi,
                            Apply {
                                function: spine.into(),
                                argument: ast::Expr::Variable(pi, Identifier::Bound(slot(Some(j))))
                                    .into(),
                            },
                        );
                    }
                    let total_params = num_constraints + method_arity;
                    for arg in (num_constraints + 1)..=total_params {
                        spine = ast::Expr::Apply(
                            pi,
                            Apply {
                                function: spine.into(),
                                argument: ast::Expr::Variable(pi, Identifier::Bound(arg)).into(),
                            },
                        );
                    }

                    let body = (2..=total_params).rev().fold(spine, |body, x| {
                        ast::Expr::Lambda(
                            pi,
                            Lambda {
                                parameter: Identifier::Bound(x),
                                body: body.into(),
                            },
                        )
                    });
                    let lambda = Lambda {
                        parameter: Identifier::Bound(1),
                        body: body.into(),
                    };

                    let mut type_signature = field.type_signature.clone();

                    type_signature.universal_quantifiers = {
                        let mut signature_parameters = type_constructor
                            .definition()
                            .defining_symbol
                            .type_parameters()
                            .to_vec();
                        signature_parameters
                            .extend_from_slice(&type_signature.universal_quantifiers);
                        signature_parameters
                    };

                    // Constraints in the same sorted order the body expects.
                    type_signature.constraints =
                        constraints.iter().map(|(_, c)| c.clone()).collect();

                    // Put the constraints back on the selector so that solve_constraints
                    // in discharge_ground_constraints can understand what to do. Normal
                    // functions will desuguar completely.
                    let saved = type_signature.constraints.clone();
                    type_signature.desugar_constraints();
                    type_signature.constraints = saved;

                    let tree = ast::Expr::Ascription(
                        pi,
                        TypeAscription {
                            ascribed_tree: ast::Expr::RecursiveLambda(
                                pi,
                                SelfReferential {
                                    own_name: Identifier::Bound(0),
                                    lambda,
                                },
                            )
                            .into(),
                            type_signature: type_signature.clone(),
                        },
                    );

                    tracing::trace!("{name} is {}", tree);

                    symbols.push(TermSymbol {
                        name,
                        type_signature: Some(type_signature),
                        body: tree.into(),
                    });
                }
            }
        }

        Ok(symbols)
    }

    fn insert_signature_method_placeholders(&self, ctx: &mut TypingContext) -> Typing<()> {
        // Iterate signatures in a deterministic order. A method name shared by two
        // signatures (e.g. `pure` in both Applicative and Monad) overwrites the
        // placeholder, so a HashSet's iteration order would make resolution -- and
        // thus the whole program -- nondeterministic.
        let mut signatures = self.signatures.iter().collect::<Vec<_>>();
        signatures.sort();
        for c in signatures {
            let type_constructor = ctx
                .types
                .lookup(c)
                .cloned()
                .expect("internal error: constraint name does not match type constructor.");

            let type_constructor = type_constructor.instantiate(ctx)?;
            let constraints = ConstraintSet::from(
                [Constraint::from_type_constructor(&type_constructor)].as_slice(),
            );

            if let TypeStructure::PolyRecord(record_type) = type_constructor.structure()? {
                for (method_id, scheme) in
                    record_type.fields().filter(|(id, _)| !is_super_field(id))
                {
                    let scheme = scheme.clone();
                    let name = QualifiedName::new(
                        type_constructor.defining_context().clone(),
                        method_id.as_str(),
                    );

                    let constrained = Constrained {
                        constraints: scheme.constraints.union(constraints.clone()),
                        underlying: scheme.underlying,
                    };
                    let scheme = constrained.generalize(ctx);

                    tracing::trace!(">>> placeholder {name} :: {scheme}");
                    ctx.bind_free_term(name, scheme.underlying);
                }
            }
        }

        Ok(())
    }

    #[instrument(skip_all)]
    fn type_term(
        &self,
        symbol: &TermSymbol<ParseInfo, namer::QualifiedName, Identifier>,
        ctx: &mut TypingContext,
    ) -> Typing<Typed> {
        tracing::debug!("{}, {}", symbol.name, symbol.body);

        let qualified_name = symbol.name.clone();

        // Guarded value recursion: a non-lambda binding may name itself as long as
        // the self-reference is deferred behind a lambda. Bind the name *before*
        // inferring the body so the self-reference resolves. Witnesses keep their
        // existing (lazy-dictionary) path untouched. A `RecursiveLambda`-valued
        // binding carries its own name as a bound De Bruijn, so it classifies as
        // `None` here and stays on the plain path below.
        let expr = match (
            self.witnesses.contains(&qualified_name),
            classify_self_reference(&symbol.body, &qualified_name),
        ) {
            (false, SelfReference::Unguarded) => {
                let pi = *symbol.body.annotation();
                return Err(TypeError::UnguardedValueRecursion {
                    name: qualified_name,
                }
                .at(pi));
            }

            (false, SelfReference::Guarded) if symbol.type_signature.is_some() => {
                // With a signature, self-calls may use the declared scheme
                // (polymorphic recursion is sound because the user annotated it).
                let signature = symbol.type_signature.as_ref().unwrap();
                let scheme = signature.type_scheme(&HashMap::default(), ctx)?;
                ctx.bind_free_term(qualified_name.clone(), scheme);
                ctx.infer_expr(&symbol.body)?
            }

            (false, SelfReference::Guarded) => {
                // No signature: monomorphic recursion. Bind a fresh metavariable
                // for the self-reference, then reconcile it with the inferred type.
                let pi = *symbol.body.annotation();
                let own = Type::fresh();
                ctx.bind_free_term(
                    qualified_name.clone(),
                    TypeScheme::from_constant(own.clone()),
                );
                let expr = ctx.infer_expr(&symbol.body)?;
                let unification = expr
                    .tree
                    .type_info()
                    .inferred_type
                    .unified_with(&own.apply(&expr.substitutions), &ctx.types)
                    .map_err(|e| e.at(pi))?;
                expr.apply(&unification)
            }

            _ => ctx.infer_expr(&symbol.body)?,
        };

        let scheme = if let Some(signature) = &symbol.type_signature {
            let mut declared = signature.type_scheme(&HashMap::default(), ctx)?;
            // Witnesses are verified on the separate dictionary-elaboration path.
            if !self.witnesses.contains(&qualified_name) {
                let inferred = expr
                    .tree
                    .type_info()
                    .inferred_type
                    .apply(&expr.substitutions);
                let pi = *symbol.body.annotation();
                declared.reject_if_more_general_than(&inferred, &qualified_name, pi, ctx)?;

                // Surface signatures elide arrow capture indices. Checking the
                // body solves those indices; retain that solution in the scheme
                // registered for subsequent users instead of re-generalizing the
                // unsolved placeholders from the parsed annotation.
                let capture_solution = declared
                    .underlying
                    .unified_with(&inferred, &ctx.types)
                    .map_err(|e| e.at(pi))?;
                declared.underlying = declared.underlying.apply(&Substitutions::with_confinements(
                    capture_solution.confinements.clone(),
                ));
                let declared_variables = declared.underlying.variables();
                declared.quantifiers = declared
                    .quantifiers
                    .iter()
                    .map(|quantifier| {
                        declared_variables
                            .iter()
                            .find(|variable| *variable == quantifier)
                            .cloned()
                            .unwrap_or_else(|| quantifier.clone())
                    })
                    .collect();
                declared.confinement_quantifiers = declared.underlying.confinement_variables();

                // `Memory_Layout` evidence is compiler-derived, so a surface
                // signature need not repeat layout obligations introduced by an
                // implementation detail such as calling `Hash_Table.lookup`.
                // Nevertheless, an abstract layout cannot be manufactured inside
                // the generic worker: it must become part of that worker's hidden
                // dictionary ABI so concrete callers can supply and specialize it.
                // Re-express the inferred constraints in the declared scheme's
                // quantified variables before registering the enriched scheme.
                let inferred_to_declared = inferred
                    .unified_with(&declared.underlying, &ctx.types)
                    .map_err(|e| e.at(pi))?;
                let inferred_layouts = expr
                    .constraints
                    .apply(&expr.substitutions)
                    .apply(&inferred_to_declared)
                    .into_iter()
                    .filter(|constraint| {
                        *constraint.name() == memory_layout_class()
                            && !constraint.variables().is_empty()
                            && memory_layout_requires_parameter(constraint, &ctx.types)
                    })
                    .collect::<Vec<_>>();
                declared.constraints = declared
                    .constraints
                    .union(ConstraintSet::from(inferred_layouts.as_slice()));

                // Ambiguity: a quantified variable that occurs in the constraint
                // context but nowhere in the declared type is fixed by nothing at a
                // call site (there are no functional dependencies), so instance
                // resolution leaves it -- and the dictionary it selects -- undetermined.
                // Reject with a clear message rather than leaking a phantom dictionary
                // parameter or wiring an arbitrary instance. E.g. `hash_with : ∀α
                // factory h. … Hash_Stream_Factory factory h |- factory -> α -> Int`,
                // where `h` appears only in the constraint.
                let type_vars = declared.underlying.variables();
                for constraint in declared.constraints.iter() {
                    if constraint
                        .constraint_type
                        .variables()
                        .iter()
                        .any(|v| declared.quantifiers.contains(v) && !type_vars.contains(v))
                    {
                        return Err(TypeError::AmbiguousConstraint {
                            name: qualified_name.clone(),
                            constraint: constraint.clone(),
                            underlying: declared.underlying.clone(),
                        }
                        .at(pi));
                    }
                }
            }
            declared
        } else {
            let inferred_type = &expr.as_constrained_type();
            inferred_type.generalize(ctx).underlying
        };

        tracing::trace!(">>> {} :: {}", qualified_name, scheme);
        ctx.bind_free_term(qualified_name.clone(), scheme.clone());

        Ok(expr)
    }

    pub fn elaborate_foreign_terms(&self, ctx: &mut TypingContext) -> Typing<()> {
        for ext in &self.foreign_terms {
            let mut type_scheme = ext.type_signature.type_scheme(&HashMap::default(), ctx)?;
            // A foreign symbol itself is a global code pointer, not a closure.
            // Partial applications may still capture arguments; only the outer
            // arrow receives this unconditional bottom capability.
            if let Type::Arrow { capture, .. } = &mut type_scheme.underlying {
                *capture = Confinement::Unconfined;
            }
            type_scheme.confinement_quantifiers = type_scheme.underlying.confinement_variables();
            ctx.bind_free_term(ext.name.clone(), type_scheme);
        }
        Ok(())
    }
}

/// Prefix for the hidden supersignature dictionary fields injected into a
/// signature's vtable. `$` cannot begin a surface identifier, so these never
/// collide with user method names.
const SUPER_FIELD_PREFIX: &str = "$super$";

fn super_field_name(class: &QualifiedName) -> parser::Identifier {
    parser::Identifier::from_str(&format!("{SUPER_FIELD_PREFIX}{}", class.member.as_str()))
}

fn is_super_field(name: &parser::Identifier) -> bool {
    name.as_str().starts_with(SUPER_FIELD_PREFIX)
}

/// The supersignature obligations of a witness whose produced dictionary has type
/// `head` (e.g. `Ord Int`, `Monad (ExceptT m e)`): each hidden `$super$<Class>`
/// field to fill, paired with the instantiated super constraint whose dictionary
/// fills it. Returns empty for any type that is not a signature dictionary, so it
/// is safe to call on every term.
fn super_obligations(
    head: &Type,
    ctx: &TypingContext,
) -> Result<Vec<(parser::Identifier, Constraint)>, TypeError> {
    let class = match head {
        Type::Apply { .. } | Type::Constructor(..) => head.applied_name(),
        _ => return Ok(Vec::new()),
    };
    let Some(tc) = ctx.types.lookup(class) else {
        return Ok(Vec::new());
    };
    if !matches!(
        &tc.definition().defining_symbol.definition,
        TypeDefinition::Signature(sig) if !sig.supersignatures.is_empty()
    ) {
        return Ok(Vec::new());
    }

    // Instantiate the signature with fresh parameters, unify its spine with the
    // head to learn the head's type arguments, then apply that to each super.
    let inst = tc.instantiate(ctx).map_err(|e| *e.error)?;
    let subst = inst.make_spine().unified_with(head, &ctx.types)?;
    let params = inst.definition().instantiated_params.clone();
    let TypeDefinition::Signature(sig) = &inst.definition().defining_symbol.definition else {
        return Ok(Vec::new());
    };

    sig.supersignatures
        .iter()
        .map(|super_ce| {
            let c =
                Constraint::from_constraint_expr(&params, super_ce, ctx).map_err(|e| *e.error)?;
            Ok((super_field_name(&super_ce.class), c.apply(&subst)))
        })
        .collect()
}

/// The ordinal of a `$super$…` field within `dict`'s vtable record. Projections
/// built here run *after* type inference, so they must carry the resolved
/// ordinal directly (the interpreter/codegen only understand `Ordinal`).
fn super_field_ordinal(
    dict: &Constraint,
    field: &parser::Identifier,
    ctx: &TypingContext,
) -> Option<usize> {
    let tc = ctx
        .types
        .lookup(dict.constraint_type.applied_name())?
        .instantiate(ctx)
        .ok()?;
    match tc.structure().ok()? {
        TypeStructure::PolyRecord(record_type) => record_type.field_info(field).map(|(i, _)| i),
        _ => None,
    }
}

/// If the given constraint `g` entails the wanted constraint `w` through a chain
/// of supersignatures, the projection path (field ordinal + resulting dictionary
/// type at each hop) from `g`'s dictionary to `w`'s. Both are expected to share
/// the enclosing term's metavariables, so the supers instantiated at `g`'s
/// arguments match `w` by equality.
fn super_projection_path(
    g: &Constraint,
    w: &Constraint,
    ctx: &TypingContext,
) -> Option<Vec<(usize, Type)>> {
    for (field, super_c) in super_obligations(&g.constraint_type, ctx).ok()? {
        let ordinal = super_field_ordinal(g, &field, ctx)?;
        if &super_c == w {
            return Some(vec![(ordinal, super_c.constraint_type)]);
        }
        if let Some(mut rest) = super_projection_path(&super_c, w, ctx) {
            rest.insert(0, (ordinal, super_c.constraint_type));
            return Some(rest);
        }
    }
    None
}

/// Build the evidence for a supersignature-entailed constraint: project the
/// `$super$…` chain (by ordinal) out of the entailing dictionary `base`.
fn project_super_evidence(base: Expr, path: &[(usize, Type)]) -> Expr {
    let pi = base.annotation().parse_info;
    path.iter().fold(base, |base, (ordinal, ty)| {
        Expr::Project(
            pi.with_inferred_type(ty.clone()),
            Projection {
                base: std::rc::Rc::new(base),
                select: ProductElement::Ordinal(*ordinal),
            },
        )
    })
}

/// Descend through a witness's dictionary-parameter lambdas / ascription to the
/// record it ultimately builds, returning its fields for mutation.
fn witness_record_fields_mut(
    tree: &mut Expr,
) -> Option<&mut Vec<(parser::Identifier, std::rc::Rc<Expr>)>> {
    match tree {
        Expr::Record(_, record) => Some(&mut record.fields),
        Expr::Ascription(_, a) => {
            witness_record_fields_mut(std::rc::Rc::make_mut(&mut a.ascribed_tree))
        }
        Expr::RecursiveLambda(_, rec) => {
            witness_record_fields_mut(std::rc::Rc::make_mut(&mut rec.lambda.body))
        }
        Expr::Lambda(_, l) => witness_record_fields_mut(std::rc::Rc::make_mut(&mut l.body)),
        _ => None,
    }
}

/// The constraints a term *declares* (its signature's `|-` context), instantiated
/// and reconciled to the body's metavariables so supersignature entailment can
/// match them against the body's inferred (wanted) constraints. With no
/// signature, the declared set is exactly the inferred set.
fn given_constraints(
    symbol: &TermSymbol<ParseInfo, QualifiedName, Identifier>,
    term: &Typed,
    ctx: &TypingContext,
) -> Typing<ConstraintSet> {
    match &symbol.type_signature {
        Some(signature) => {
            let instantiated = signature
                .type_scheme(&HashMap::default(), ctx)?
                .instantiate();
            let subst = instantiated
                .underlying
                .unified_with(&term.tree.type_info().inferred_type, &ctx.types)
                .map_err(|e| e.at(ParseInfo::default()))?;
            Ok(instantiated.constraints.apply(&subst))
        }
        None => Ok(term.constraints.clone()),
    }
}

#[instrument(skip_all)]
fn elaborate_term_constraints(
    symbol_name: &QualifiedName,
    witnesses: &WitnessEnvironment,
    given: ConstraintSet,
    constraints: ConstraintSet,
    tree: ast::Expr<TypeInfo, Identifier>,
    ctx: &mut TypingContext,
) -> Result<ast::Expr<TypeInfo, Identifier>, TypeError> {
    tracing::trace!("{symbol_name} given {given} wanted {constraints} tree {tree}");

    if std::env::var_os("DUMP_WANTED").is_some_and(|f| {
        symbol_name
            .to_string()
            .contains(&f.to_string_lossy().to_string())
    }) {
        eprintln!(
            "[wanted] {symbol_name}  body type {}",
            tree.type_info().inferred_type
        );
        for c in given.iter() {
            eprintln!(
                "    given  {c}  ground={}",
                c.constraint_type.variables().is_empty()
            );
        }
        for c in constraints.iter() {
            eprintln!(
                "    wanted {c}  ground={} parametric={}",
                c.constraint_type.variables().is_empty(),
                c.is_parametric()
            );
        }
    }

    Ok(resolve_constraints(
        symbol_name,
        tree,
        given,
        constraints,
        witnesses,
        ctx,
    )?)
}

#[instrument(skip_all)]
fn resolve_constraints(
    symbol_name: &QualifiedName,
    tree: Expr,
    given: ConstraintSet,
    constraints: ConstraintSet,
    witnesses: &WitnessEnvironment,
    ctx: &mut TypingContext,
) -> Result<Expr, TypeError> {
    let is_constrained = !given.is_empty() || !constraints.is_empty();

    // A witness body can leave its class parameter as a free metavariable: when a
    // method threads state through a nested recursive lambda, the recursion's fresh
    // codomain never ties back to the instance head, so a sibling-method use yields
    // `Sink $a` with `$a` unbound. The produced dictionary's own type is already the
    // ground head (`Sink Box`), so pin the parameter by unifying every wanted
    // constraint of the witness's class against that head; the resulting
    // substitution then also grounds the transitively-affected constraints
    // (`Monad (State $a)` -> `Monad (State Box)`). Constraints of other classes fail
    // to unify with the head and are left untouched. Without this the stale
    // variable-headed constraint is misread as a leading dictionary parameter,
    // turning the record into a `λself. record` that callers project unforced (a
    // null dereference).
    let (mut tree, constraints) = match witnesses.witness_named(symbol_name) {
        // Only a fully CONCRETE head (`Sink Box`) may pin metavariables this way. A
        // polymorphic head (`Display (List a)`) legitimately carries same-class
        // premises (`Display a`, the recursive element instance) that must stay
        // parametric; unifying those against the head would collapse the recursion.
        Some(witness) if witness.head.constraint_type.variables().is_empty() => {
            let head = witness.head.constraint_type.clone();
            let mut ground = Substitutions::default();
            for c in constraints.iter() {
                if let Ok(s) = c
                    .constraint_type
                    .apply(&ground)
                    .unified_with(&head, &ctx.types)
                {
                    ground = ground.compose(&s);
                }
            }
            (tree.apply(&ground), constraints.apply(&ground))
        }
        _ => (tree, constraints),
    };

    // Supersignatures: if this term builds a signature dictionary (a witness),
    // capture the hidden `$super$` fields it must fill *before* the tree is
    // wrapped in dictionary-parameter lambdas below (which would change its type
    // to an arrow). Populated after discharge, using the same evidence.
    let super_obligations = super_obligations(&tree.type_info().inferred_type, ctx)?;

    // The wanted (inferred) constraints split into variable-headed (`Eq α`, which
    // no instance can match) and instance-resolvable (`Eq Int`, `Eq (List α)`).
    let is_wanted_parameter = |constraint: &Constraint| {
        constraint.is_parametric()
            || (*constraint.name() == memory_layout_class()
                && !constraint.variables().is_empty()
                && memory_layout_requires_parameter(constraint, &ctx.types))
    };
    let (mut wanted_parametric, resolvable) = constraints
        .clone()
        .into_iter()
        .partition::<Vec<_>, _>(is_wanted_parameter);

    // A resolvable constraint like `Functor (ExceptT m e)` is discharged through a
    // witness whose premises can themselves be parametric (`Functor m`, `m`
    // abstract). Such a premise is only satisfiable from a dictionary parameter
    // (projected from a given), yet it never appears among the *wanted* set, so the
    // param logic below would skip it and `resolve_witness` would ground it against
    // a concrete witness head -- a fabricated dictionary. Surface those parametric
    // premises (transitively) as wanted, so a given (`Monad m`) is bound as a
    // parameter and the premise is projected out of it.
    {
        // Seed from the resolvable constraints *and* the super-obligations (a
        // `Monoid (Perhaps α)` witness must fill a `$super$Semigroup` =
        // `Semigroup (Perhaps α)`, whose `Semigroup α` premise likewise projects
        // out of the `Monoid α` parameter).
        let mut worklist = resolvable.clone();
        worklist.extend(super_obligations.iter().map(|(_, c)| c.clone()));
        let mut seen: Vec<Constraint> = Vec::new();
        while let Some(c) = worklist.pop() {
            if seen.contains(&c) {
                continue;
            }
            seen.push(c.clone());
            for premise in witnesses.premises_of(&c, &ctx.types) {
                if premise.is_parametric() {
                    if !wanted_parametric.contains(&premise) {
                        wanted_parametric.push(premise);
                    }
                } else {
                    worklist.push(premise);
                }
            }
        }
    }

    // Parameters are driven by the *wanted* (inferred) constraints -- a term only
    // needs a dictionary parameter for a class its body actually uses. The given
    // (declared) constraints only redirect a wanted: if a *proper supersignature*
    // of a given covers the wanted, the given becomes the parameter and the wanted
    // is projected out of it (`Ord α` given covers a wanted `Eq α`). Otherwise the
    // wanted is its own parameter -- exactly the pre-supersignature behaviour, so
    // selectors (whose dictionary is an explicit argument, no inferred constraint)
    // and ordinary constrained functions are unaffected.
    let given_parametric: Vec<Constraint> = given
        .iter()
        // An explicit layout constraint is an intentional part of the source ABI,
        // even when element-zero discovery would also be safe for that particular
        // abstract product. Only inferred implementation-detail layouts use the
        // narrower `is_wanted_parameter` rule above.
        .filter(|c| {
            c.is_parametric() || (*c.name() == memory_layout_class() && !c.variables().is_empty())
        })
        .cloned()
        .collect();

    let mut params: Vec<Constraint> = Vec::new();
    let mut projections: Vec<(Constraint, Constraint, Vec<(usize, Type)>)> = Vec::new();
    for w in &wanted_parametric {
        if let Some((g, path)) = given_parametric.iter().find_map(|g| {
            (g != w)
                .then(|| super_projection_path(g, w, ctx).map(|path| (g.clone(), path)))
                .flatten()
        }) {
            if !params.contains(&g) {
                params.push(g.clone());
            }
            projections.push((w.clone(), g, path));
        } else if !params.contains(w) {
            params.push(w.clone());
        }
    }

    // An explicitly declared applied Memory_Layout constraint is also part of the
    // function's public dictionary ABI when the body does not inspect the dictionary
    // itself. Direct packed reads/writes consume its information later, after layout
    // specialization, so wanted-only parameter selection would omit the binder while
    // callers (following the registered source scheme) still supply it. Keep these
    // declared layout parameters even when they are operationally implicit here.
    for declared in &given_parametric {
        if *declared.name() == memory_layout_class()
            && !declared.variables().is_empty()
            && !params.contains(declared)
        {
            params.push(declared.clone());
        }
    }

    // Keep dictionary parameters in the registered type scheme's constraint
    // order. Registration and body elaboration use independently-freshened meta
    // variables, so BTree ordering is not stable when a function needs two
    // dictionaries from the same class (notably two different Memory_Layout
    // applications). The caller follows the registered scheme; translate that
    // order into the body's variables before adding parameter lambdas.
    if let Some(registered) = ctx.terms.lookup_free(symbol_name) {
        let registered = registered.instantiate();
        if let Ok(subst) = registered
            .underlying
            .unified_with(&tree.type_info().inferred_type, &ctx.types)
        {
            let mut ordered: Vec<Constraint> = registered
                .constraints
                .apply(&subst)
                .into_iter()
                .filter(|constraint| params.contains(constraint))
                .collect();
            for param in &params {
                if !ordered.contains(param) {
                    ordered.push(param.clone());
                }
            }
            params = ordered;
        }
    }

    // If this term *is* a witness, its dictionary parameters must be bound in the
    // exact order `resolve_witness` supplies the premise dictionaries at a use site
    // -- i.e. the registered witness's `premises` Vec order. The `params` order
    // above follows the *wanted* BTreeSet, which sorts by the class constructor
    // first and only falls through to the (metavariable) argument when two
    // constraints share a class. Those metavariables are numbered independently in
    // the registration pass and this body pass, so two same-class premises
    // (`Display α + Display e`) can come out reversed here relative to the caller,
    // landing the dictionaries in swapped slots. Reorder `params` to follow the
    // registered premises, translated into this body's metavariables by unifying
    // the registered head against the body's head type. For single premises and
    // for premises of distinct classes the two orders already agree, so this is a
    // no-op except for the same-class case it exists to fix.
    if let Some(witness) = witnesses.witness_named(symbol_name)
        && let Ok(subst) = witness
            .head
            .constraint_type
            .unified_with(&tree.type_info().inferred_type, &ctx.types)
    {
        // A witness's leading dictionary parameters *are* its premises, in premise
        // order: the caller supplies exactly those, so bind exactly those. Start
        // from the premises (fixing both order and, when the body only uses some of
        // them, count -- an unused premise still needs its slot, or the caller's
        // extra dictionary over-applies the witness), then append any wanted-derived
        // param not among them (defensive; shouldn't arise for a witness).
        let mut ordered: Vec<Constraint> =
            witness.premises.iter().map(|c| c.apply(&subst)).collect();
        for p in &params {
            if !ordered.contains(p) {
                ordered.push(p.clone());
            }
        }
        params = ordered;
    }

    tracing::trace!(
        "{symbol_name} params: {:?} projections {:?} resolvable {:?}",
        &params,
        &projections,
        &resolvable
    );

    // Self referential trees have own_name at #0, first parameter is
    // therefore offset by 1.
    let is_self_referential = matches!(
        &tree,
        Expr::Ascription(
            _,
            the
        ) if matches!(*the.ascribed_tree, Expr::RecursiveLambda(..))
    ) || matches!(&tree, Expr::RecursiveLambda(..));

    // `bind_term(Bound(0))` pushes onto the shared `bound` stack, which is not
    // otherwise cleared between symbols in the discharge loop. Reset it so this
    // symbol's self-reference (#0) refers to *itself*, not to whichever
    // self-referential constrained symbol happened to be discharged first.
    ctx.reset_self_reference();
    if is_constrained && is_self_referential {
        // The self-reference must advertise only the *parametric* constraints --
        // the ones that actually became leading dictionary parameters (#1, #2,
        // ...) below. A recursive call has to re-pass exactly those dictionaries.
        // Resolvable constraints (ground- or constructor-headed, e.g.
        // `Functor (ExprF name a)`) are discharged inline in the body and take no
        // parameter, so listing them here would make the recursive call inject a
        // phantom dictionary argument and shift the real arguments.
        ctx.bind_term(
            Identifier::Bound(0),
            Constrained {
                constraints: ConstraintSet::from(params.as_slice()),
                underlying: tree.type_info().inferred_type.clone(),
            }
            .generalize(ctx)
            .underlying,
        );
    }

    let mut evidence = HashMap::new();

    // `add_dictionary_parameter_slot` truly prepends: the last constraint added
    // becomes argument #1. Add in reverse scheme order so the finished lambda and
    // its callers both see params[0], params[1], ... at Bound(1), Bound(2), ... .
    // This matters once a generic worker carries three dictionaries (for example
    // Eq plus two inferred Memory_Layouts); layout markers previously made the
    // accidental swap hard to observe at runtime, but their annotations no longer
    // matched the actual slots and specialization could not follow them.
    for c in params.iter().rev() {
        tree = add_dictionary_parameter_slot(&tree, &c.constraint_type);
    }

    // Bind evidence to the now-stable parameter levels.
    for (i, c) in params.iter().enumerate() {
        let name = Identifier::Bound(1 + i);
        tracing::trace!("binding {name} to {}", c.constraint_type);

        evidence.insert(
            c.clone(),
            Expr::Variable(
                tree.annotation()
                    .parse_info
                    .with_inferred_type(c.constraint_type.clone()),
                name,
            ),
        );
    }

    // Supersignature entailment: a wanted constraint that is a supersignature of a
    // given is discharged by projecting the `$super$…` chain out of that given's
    // dictionary parameter -- so it needs no parameter of its own.
    for (w, param_given, path) in projections {
        let base = evidence[&param_given].clone();
        evidence.insert(w, project_super_evidence(base, &path));
    }

    // Discharge the remaining constraints through their instances, using the
    // parameter dictionaries just bound as assumptions for the instances'
    // premises. A recursive derived instance resolves its own head this way,
    // reconstructing the recursive dictionary from the parameters.
    for c in resolvable {
        let w = witnesses.resolve_witness(&c, &ctx.types, &evidence)?;

        // If a constraint resolves to the witness we are *currently* elaborating,
        // that is a recursive dictionary. When this tree has a self-reference slot
        // (#0) -- i.e. it is a self-referential lambda, as constrained/derived
        // witnesses and functions are -- route the recursion through #0, exactly as
        // ordinary recursion does.
        //
        // A *ground* witness (e.g. `Foldable List`) has no such slot: its body is a
        // plain record, so #0 would collide with a field lambda's own parameter and
        // mis-project at run time (a `BadProjection`). Leave those as the global
        // self-reference, which resolves through the shared, live globals.
        let w = if is_self_referential {
            w.map(&mut |e| match e {
                Expr::Variable(ti, Identifier::Free(name)) if name.as_ref() == symbol_name => {
                    Expr::Variable(ti, Identifier::Bound(0))
                }
                other => other,
            })
        } else {
            w
        };

        evidence.insert(c, w);
    }

    //    tracing::trace!("{evidence}");

    if !evidence.is_empty() {
        tracing::trace!("Sixten!");
        tree = discharge_constraints(tree, &evidence, witnesses, ctx);
    }
    tree = elaborate_constraint_method_placeholders(tree, &constraints, ctx);

    // Supersignatures: fill each `$super$<Class>` field with the resolved super
    // dictionary. A ground super (`Eq Int`) resolves to that ground witness; a
    // parametric super (`Applicative (ExceptT m e)`) resolves against the
    // dictionary parameters just bound (the same `evidence`). The value is
    // already fully discharged, so it is spliced in *after* `discharge_constraints`.
    if !super_obligations.is_empty() {
        let mut super_fields = Vec::with_capacity(super_obligations.len());
        for (field, constraint) in &super_obligations {
            let dictionary = witnesses.resolve_witness(constraint, &ctx.types, &evidence)?;
            super_fields.push((field.clone(), std::rc::Rc::new(dictionary)));
        }
        if let Some(fields) = witness_record_fields_mut(&mut tree) {
            fields.extend(super_fields);
            // The dictionary record's runtime layout must match the vtable record
            // TYPE, which sorts fields by name (`RecordType::from_fields`). Project
            // selectors read by that sorted ordinal, so keep the value in the same
            // order.
            fields.sort_by(|(a, _), (b, _)| a.cmp(b));
        }
    }

    Ok(tree)
}

// witness C2 Int := ...
//
// f :: forall a b. C1 a + C2 b + C3 a |- a -> b -> Text := lambda a b.
//   c1 a; c2 b; c3 a
//
// g :: forall a. C1 a + C3 a |- a -> Unit := lambda a.
//   f a 10
//
// a := Text
// b := Int
//
// ground: C 2 Int
// non-ground: C1 a, C3 a
//
// Expects tree to be post insert_selectors_at_placeholders
//
// This function can carry a list of type errors.
#[instrument(skip_all)]
fn discharge_constraints(
    tree: Expr,
    evidence: &HashMap<Constraint, Expr>,
    witnesses: &WitnessEnvironment,
    ctx: &TypingContext,
) -> Expr {
    tracing::trace!("tree {tree} evidence {evidence:?}");

    // It crashes on access to parameter 0 in a witness
    // function. It is not recursive so it is bound at #0.
    // There is also the question of whether or not I should even be
    // inspecting Identifier::Bound(..) and not just Identifier::Free(..)

    tree.map(&mut |e| match e {
        Expr::Variable(type_info, ref term_id @ (Identifier::Free(..) | Identifier::Bound(0))) => {
            // It is just not as easy as picking #0 too. It could be a plain variable
            tracing::trace!("name {term_id}");

            // A witness global reached here inside an evidence term is ALREADY
            // saturated: `resolve_witness` built the spine with its premise
            // dictionaries applied. Re-injecting here would double-apply them. This
            // used to be masked -- the spine carried `Type::fresh()` annotations, so
            // the unification below bound a free variable, no use-site constraint ever
            // matched the evidence map, and injection silently no-opped. Now that the
            // spine is honestly typed, the guard has to be explicit.
            let is_saturated_witness = matches!(term_id, Identifier::Free(q)
                if witnesses.witness_named(q.as_ref()).is_some());

            if let Some(type_scheme) = ctx.terms.lookup(&term_id)
                && !type_scheme.constraints.is_empty()
                && !is_saturated_witness
            {
                let use_site_type = type_scheme.instantiate();

                tracing::trace!("scheme {use_site_type} type {}", type_info.inferred_type);

                let use_site_subst = use_site_type
                    .underlying
                    .unified_with(&type_info.inferred_type, &ctx.types)
                    .expect("expr.typed");
                // Substitute each constraint but KEEP the scheme's own order. Going
                // through `ConstraintSet::apply` would re-collect into a `BTreeSet`,
                // re-sorting by the now-GROUND types -- and the fold below turns this
                // order into the dictionary ARGUMENT order, while the callee bound its
                // dictionary PARAMETERS against the un-grounded constraints. For two
                // premises of the same class (`Default a + Default b`) the class name
                // cannot break the tie, so grounding can reverse them and the two
                // dictionaries get swapped at the call site.
                let use_site_constraints = use_site_type
                    .constraints
                    .iter()
                    .map(|c| c.apply(&use_site_subst))
                    .collect::<Vec<_>>();

                let is_injection_site = use_site_constraints
                    .iter()
                    .any(|c| evidence.contains_key(c));

                if is_injection_site {
                    //tracing::trace!("{method_name} ")

                    use_site_constraints.iter().fold(
                        Expr::Variable(type_info.clone(), term_id.clone()),
                        |f, c| {
                            if !evidence.contains_key(c) {
                                println!("discharge_constrans: {c} not in {evidence:?}");
                            }
                            let mut w = evidence[c].clone();

                            // Do not try to insert dictionaries into variables, these
                            // are for non-ground constraints that have be deferred
                            // to dictionary paramters in the current top-level declaration
                            if !matches!(w, Expr::Variable(..)) {
                                w = discharge_constraints(
                                    evidence[c].clone(),
                                    evidence,
                                    witnesses,
                                    ctx,
                                );
                            }

                            Expr::Apply(
                                type_info.clone(),
                                Apply {
                                    function: f.into(),
                                    argument: w.into(),
                                },
                            )
                        },
                    )
                } else {
                    Expr::Variable(type_info, term_id.clone())
                }
            } else {
                Expr::Variable(type_info, term_id.clone())
            }
        }

        _otherwise => _otherwise,
    })
}

#[instrument(skip_all)]
fn elaborate_constraint_method_placeholders(
    tree: Expr,
    evidence: &ConstraintSet,
    ctx: &TypingContext,
) -> Expr {
    // Key by the method's *fully-qualified* name (its signature's module +
    // member), not the bare member. Otherwise an unrelated module function that
    // merely shares a method's name -- e.g. `State.bind` vs the `Monad` method
    // `bind` -- would be clobbered into the class selector.
    let mut constraint_signatures: HashMap<QualifiedName, &Constraint> = HashMap::new();

    for c in evidence.iter() {
        let signature = c.signature(&ctx.types).expect("expr.typed");
        for method in signature.vtable.into_vec() {
            if is_super_field(&method) {
                continue;
            }
            constraint_signatures.insert(
                QualifiedName::new(c.name().module.clone(), method.as_str()),
                c,
            );
        }
    }

    // What if this function resolves the type scheme of the selector method name
    // it names?

    tree.map(&mut |e| match e {
        Expr::Variable(type_info, ref term_id @ Identifier::Free(ref method_name))
            if constraint_signatures.contains_key(method_name.as_ref()) =>
        {
            let constraint = constraint_signatures[method_name.as_ref()];
            let QualifiedName { module, member } = constraint.name();
            let selector_name = QualifiedName::new(
                module.clone(),
                &format!("{member}${}", method_name.member()),
            );

            let ty = ctx.terms.lookup_free(&selector_name);
            tracing::trace!("{selector_name} :: {ty:?} ");

            Expr::Variable(
                TypeInfo {
                    parse_info: type_info.parse_info,
                    inferred_type: ty.unwrap().underlying.clone().into(),
                    enclosing_term: type_info.enclosing_term,
                },
                //TypeInfo {
                //    parse_info: type_info.parse_info,
                //    inferred_type: type_info.inferred_type.into(),
                //},
                //TypeInfo {
                //    parse_info: type_info.parse_info,
                //    inferred_type: Type::Arrow {
                //        domain: constraint.constraint_type.clone().into(),
                //        codomain: type_info.inferred_type.into(),
                //    },
                //},
                Identifier::Free(selector_name.into()),
            )
        }

        otherwise => otherwise,
    })
}

fn dictionary_arrow(annotation: &TypeInfo, dictionary_type: &Type) -> TypeInfo {
    TypeInfo {
        parse_info: annotation.parse_info,
        inferred_type: Type::Arrow {
            capture: Confinement::fresh(),
            domain: Box::new(dictionary_type.clone()),
            codomain: Box::new(annotation.inferred_type.clone()),
        },
        enclosing_term: annotation.enclosing_term.clone(),
    }
}

fn add_dictionary_parameter_slot(expr: &Expr, dictionary_type: &Type) -> Expr {
    if let Expr::Ascription(a0, ascription) = expr {
        match ascription.ascribed_tree.as_ref() {
            Expr::RecursiveLambda(a1, rec) => Expr::Ascription(
                a0.clone(),
                TypeAscription {
                    ascribed_tree: Expr::RecursiveLambda(
                        dictionary_arrow(a1, dictionary_type),
                        SelfReferential {
                            own_name: rec.own_name.clone(),
                            lambda: rec.lambda.clone().prepend_parameter(a1.clone()).clone(),
                        },
                    )
                    .into(),
                    type_signature: ascription.type_signature.clone(),
                },
            ),

            expr => Expr::Ascription(
                a0.clone(),
                TypeAscription {
                    ascribed_tree: Expr::RecursiveLambda(
                        dictionary_arrow(a0, dictionary_type),
                        SelfReferential {
                            own_name: Identifier::Bound(0),
                            lambda: Lambda {
                                parameter: Identifier::Bound(1),
                                body: expr
                                    .clone()
                                    .map(&mut |e| e.shift_de_bruijn_levels(0, 2))
                                    .into(),
                            },
                        },
                    )
                    .into(),
                    type_signature: ascription.type_signature.clone(),
                },
            ),
        }
    } else {
        // A non-ascribed tree, e.g. an inferred constrained function or a lifted
        // witness method body. Slot the dictionary parameter directly, with no
        // ascription to preserve. Same shape as above: `own_name` at #0, the new
        // parameter at #1.
        match expr {
            Expr::RecursiveLambda(a1, rec) => Expr::RecursiveLambda(
                dictionary_arrow(a1, dictionary_type),
                SelfReferential {
                    own_name: rec.own_name.clone(),
                    lambda: rec.lambda.clone().prepend_parameter(a1.clone()).clone(),
                },
            ),

            other => Expr::RecursiveLambda(
                dictionary_arrow(other.annotation(), dictionary_type),
                SelfReferential {
                    own_name: Identifier::Bound(0),
                    lambda: Lambda {
                        parameter: Identifier::Bound(1),
                        body: other
                            .clone()
                            .map(&mut |e| e.shift_de_bruijn_levels(0, 2))
                            .into(),
                    },
                },
            ),
        }
    }
}

impl phase::Lambda<Types> {
    fn prepend_parameter(self, previous_annotation: TypeInfo) -> Self {
        let Identifier::Bound(first_level) = self.parameter else {
            panic!("expected locally bound")
        };

        Lambda {
            parameter: Identifier::Bound(first_level),
            body: Expr::Lambda(
                previous_annotation,
                Lambda {
                    parameter: Identifier::Bound(1 + first_level),
                    body: Rc::unwrap_or_clone(self.body)
                        .map(&mut |e| e.shift_de_bruijn_levels(first_level, 1))
                        .into(),
                },
            )
            .into(),
        }
    }
}

impl Expr {
    pub fn type_info(&self) -> &TypeInfo {
        self.annotation()
    }

    pub fn shift_de_bruijn_levels(self, threshold: usize, delta: usize) -> Self {
        match self {
            Self::Variable(a, Identifier::Bound(l)) if l >= threshold => {
                Self::Variable(a.clone(), Identifier::Bound(delta + l))
            }

            Self::Lambda(
                a,
                Lambda {
                    parameter: Identifier::Bound(l),
                    body,
                },
            ) if l >= threshold => Self::Lambda(
                a.clone(),
                Lambda {
                    parameter: Identifier::Bound(delta + l),
                    body,
                },
            ),

            // A `RecursiveLambda` binds two levels at this node -- its `own_name`
            // (the self-reference slot) and the inner lambda's parameter -- neither
            // of which is an `Expr`, so `map`'s recursion never reaches them; only
            // this arm can shift them. Without it a nested recursive `let` lambda
            // keeps stale binder levels after a dictionary-parameter shift while the
            // variables referencing it move, desyncing the recursive frame's scope
            // in closure conversion (undeclared `l*` in the emitted C).
            Self::RecursiveLambda(
                a,
                SelfReferential {
                    own_name: Identifier::Bound(own),
                    lambda:
                        Lambda {
                            parameter: Identifier::Bound(p),
                            body,
                        },
                },
            ) if own >= threshold => Self::RecursiveLambda(
                a.clone(),
                SelfReferential {
                    own_name: Identifier::Bound(delta + own),
                    lambda: Lambda {
                        parameter: Identifier::Bound(delta + p),
                        body,
                    },
                },
            ),

            Self::Let(
                a,
                Binding {
                    binder: Identifier::Bound(l),
                    operator,
                    bound,
                    body,
                },
            ) if l >= threshold => Self::Let(
                a.clone(),
                Binding {
                    binder: Identifier::Bound(delta + l),
                    operator,
                    bound,
                    body,
                },
            ),

            Self::Deconstruct(
                a,
                Deconstruct {
                    scrutinee,
                    match_clauses,
                },
            ) => Self::Deconstruct(
                a,
                Deconstruct {
                    scrutinee,
                    match_clauses: match_clauses
                        .into_iter()
                        .map(|clause| MatchClause {
                            pattern: clause.pattern.map_binders(&|id| match id {
                                Identifier::Bound(l) => Identifier::Bound(delta + l),
                                id => id,
                            }),
                            consequent: clause.consequent,
                        })
                        .collect(),
                },
            ),

            e => e,
        }
    }
}

pub trait Substitutable {
    type Output;
    fn apply(&self, subs: &Substitutions) -> Self::Output;
}

impl<T> Substitutable for T
where
    T: Annotated<TypeInfo, TypeInfo, namer::Identifier, Output = T>,
{
    type Output = T::Output;
    fn apply(&self, subs: &Substitutions) -> Self::Output {
        self.map_annotation(&move |ti| ti.apply(subs))
    }
}

#[derive(Debug, Error)]
pub enum TypeError {
    #[error("cannot unify\n       left:  {lhs}\n       right: {rhs}")]
    UnificationImpossible { lhs: Type, rhs: Type },

    #[error("infinite type\ntype variable: {param}\noccurs in: {ty}")]
    InfiniteType { param: MetaVariable, ty: Type },

    #[error(
        "bad projection: type `{inferred_base_type}` has no member `{}`",
        projection.select
    )]
    BadProjection {
        projection: phase::Projection<Named>,
        inferred_base_type: Type,
    },

    #[error("Ambiguous base type projecting field {} from {} with choices {}",
        projection.select, projection.base, display_list(", ", choices))]
    AmbiguousRecordProjection {
        projection: phase::Projection<Named>,
        choices: Vec<Type>,
    },

    #[error("undefined name {name}\nat: {parse_info}")]
    UndefinedName {
        parse_info: ParseInfo,
        name: Identifier,
    },

    #[error(
        "unguarded recursive binding: `{name}` refers to itself while computing its own \
         value.\nGuard the self-reference behind a lambda (or give it a parameter), so it \
         is only read once the binding is initialised."
    )]
    UnguardedValueRecursion { name: namer::QualifiedName },

    #[error(
        "ambiguous constraint on `{name}`: the type variable in `{constraint}` is fixed by \
         no argument or result -- it appears only in the constraint context, never in the \
         declared type `{underlying}`. Nothing at a call site can determine it (this would \
         be a functional dependency, which is unsupported). Put the variable in the type: \
         e.g. take/return a value of that type, so a caller pins it."
    )]
    AmbiguousConstraint {
        name: namer::QualifiedName,
        constraint: Constraint,
        underlying: Type,
    },

    #[error("undefined type {0}")]
    UndefinedType(namer::QualifiedName),

    #[error("undefined symbol {0}")]
    UndefinedSymbol(SymbolName),

    #[error("{0} does not match a known record type")]
    NoSuchRecordType(RecordType),

    #[error("{0} does not match a known record type")]
    NoRecordTypWithShape(RecordShape),

    #[error("unknown type parameter {0} in type expression")]
    UnquantifiedTypeParameter(parser::Identifier),

    #[error("type constructor {constructor} expects {expected} arguments\nwas given: {was:?}")]
    WrongArity {
        constructor: namer::QualifiedName,
        was: Vec<Type>,
        expected: usize,
    },

    #[error("type constructor {0} accessed in non-elaborated state")]
    UnelaboratedConstructor(namer::QualifiedName),

    #[error("{0}")]
    InternalAssertion(String),

    #[error("{0} is not a known coproduct constructor")]
    NoSuchCoproductConstructor(namer::QualifiedName),

    #[error("constructor {constructor} takes {expected} argument(s), but this pattern binds {got}")]
    ConstructorPatternArity {
        constructor: namer::QualifiedName,
        expected: usize,
        got: usize,
    },

    #[error("tuple expression {base} does not have element {select}")]
    TupleOrdinalOutOfBounds {
        base: ast::Expr<ParseInfo, Identifier>,
        select: ProductElement,
    },

    #[error("no such field {field} in {record_type}")]
    BadRecordPatternField {
        record_type: Type,
        field: parser::Identifier,
    },

    #[error("pattern `{pattern}` cannot match a value of type `{scrutinee}`")]
    PatternTypeMismatch {
        pattern: String,
        scrutinee: TypeStructure,
    },

    #[error("{clause} is not useful")]
    UselessMatchClause { clause: phase::MatchClause<Types> },

    #[error("this deconstruction is not exhaustive; unmatched: {}", missing.join(", "))]
    MatchNotExhaustive { missing: Vec<String> },

    #[error(
        "the declared signature of `{name}` is more general than its definition\n       \
         declared: {declared}\n       inferred: {inferred}"
    )]
    SignatureTooGeneral {
        name: QualifiedName,
        declared: Type,
        inferred: Type,
    },

    #[error("Bad specialization: {0}")]
    BadSpecialization(Specialization),

    #[error("expected: {expected}; found: {found}")]
    ExpectedType { expected: Type, found: Type },

    #[error("{from} is not {expected}")]
    Disappointed { expected: Type, from: namer::Expr },

    #[error("undefined constraint signature {0}")]
    UndefinedSignature(QualifiedName),

    #[error("cyclic supersignatures: {}", display_list(" requires ", cycle))]
    CyclicSupersignature { cycle: Vec<QualifiedName> },

    #[error("cyclic type alias: {}", display_list(" expands to ", cycle))]
    CyclicTypeAlias { cycle: Vec<QualifiedName> },

    #[error("expected a monotype of kind *; found kind {kind}")]
    ExpectedMonotypeKind { kind: Kind },

    #[error("no witness found for {0}")]
    NoWitness(Constraint),

    #[error(
        "ambiguous coproduct constructor; {constructor} matches {}.",
        display_list(", ", candidates)
    )]
    AmbiguousCoproduct {
        constructor: QualifiedName,
        candidates: Vec<QualifiedName>,
    },

    #[error(
        "ambiguous record shape; {shape} matches {}.",
        display_list(", ", candidates)
    )]
    AmbiguousRecord {
        shape: RecordShape,
        candidates: Vec<QualifiedName>,
    },

    #[error("kind mismatch: cannot apply type of kind {function} at type of kind {argument}")]
    KindMismatchError { function: Kind, argument: Kind },

    #[error("confinement mismatch: cannot unify {lhs} with {rhs}")]
    ConfinementMismatch { lhs: Confinement, rhs: Confinement },

    #[error("type `{ty}` is {actual}{path}, but this context requires {required}")]
    ConfinementRequirement {
        ty: Type,
        actual: Confinement,
        required: Confinement,
        /// Filled in later by `attribute_confined_capture`; unification itself
        /// has no type environment to walk.
        path: ConfinementPath,
    },

    #[error(
        "this action captures `{ty}`, which is confined{path}, so the action cannot cross a thread boundary"
    )]
    ConfinedCapture { ty: Type, path: ConfinementPath },

    #[error(
        "unification error: kind mismatch: cannot unify {lhs}:{lhs_kind} with {rhs}:{rhs_kind}"
    )]
    KindMismatch {
        lhs: Type,
        lhs_kind: Kind,
        rhs: Type,
        rhs_kind: Kind,
    },

    // This could be improved!
    #[error(
        "record shape mismatch, missing: {} (and superfluous: {}).",
        display_list(", ", missing),
        display_list(", ", superfluous)
    )]
    BadRecordLiteral {
        missing: Vec<parser::Identifier>,
        superfluous: Vec<parser::Identifier>,
    },
}

#[derive(Debug)]
pub struct Specialization {
    map: Vec<(parser::Identifier, Type)>,
}

impl fmt::Display for Specialization {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (id, ty) in &self.map {
            writeln!(f, "{id} := {ty}")?;
        }
        Ok(())
    }
}

pub type Typing<A = Typed> = Result<A, Located<TypeError>>;

#[derive(Debug, Clone)]
pub struct TypeInfo {
    pub parse_info: ParseInfo,
    pub inferred_type: Type,
    /// Surface declaration containing this expression. Stamped after elaboration so
    /// diagnostics survive simplification, closure conversion, and lambda lifting.
    pub enclosing_term: Option<QualifiedName>,
}

impl TypeInfo {
    pub fn new(parse_info: ParseInfo, inferred_type: Type) -> Self {
        Self {
            parse_info,
            inferred_type,
            enclosing_term: None,
        }
    }

    pub fn apply(&self, subs: &Substitutions) -> Self {
        Self {
            parse_info: self.parse_info,
            inferred_type: self.inferred_type.apply(subs),
            enclosing_term: self.enclosing_term.clone(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Constrained<A> {
    pub constraints: ConstraintSet,
    pub underlying: A,
}

impl<A> Constrained<A> {
    pub fn unconstrained(underlying: A) -> Self {
        Self {
            constraints: ConstraintSet::default(),
            underlying,
        }
    }
}

impl Constrained<Type> {
    pub fn generalize(&self, ctx: &TypingContext) -> Constrained<TypeScheme> {
        let quantifiers = self.free_variables(ctx);
        let (quantified, _retained) = self
            .constraints
            .iter()
            .partition::<Vec<_>, _>(|c| c.variables().iter().all(|t| quantifiers.contains(t)));

        Constrained {
            constraints: ConstraintSet::default(),
            underlying: TypeScheme {
                quantifiers: quantifiers.iter().cloned().collect(),
                confinement_quantifiers: self
                    .underlying
                    .confinement_variables()
                    .difference(&ctx.free_confinement_variables())
                    .copied()
                    .collect(),
                underlying: self.underlying.clone(),
                constraints: ConstraintSet::from(quantified.as_slice()),
            },
        }
    }

    fn free_variables(&self, ctx: &TypingContext) -> HashSet<MetaVariable> {
        let mut ty_vars = self.underlying.variables();
        ty_vars.extend(self.constraints.variables());
        let ctx_bounds = ctx.free_variables();
        ty_vars.difference(&ctx_bounds).cloned().collect()
    }
}

#[derive(Debug, Clone)]
pub struct Typed {
    pub substitutions: Substitutions,
    pub constraints: ConstraintSet,
    pub tree: Expr,
}

impl Typed {
    fn constant(tree: Expr) -> Self {
        Self {
            substitutions: Substitutions::default(),
            constraints: ConstraintSet::default(),
            tree,
        }
    }

    fn computed(substitutions: Substitutions, constraints: ConstraintSet, tree: Expr) -> Self {
        Self {
            substitutions,
            constraints,
            tree,
        }
    }

    fn apply(&self, subst: &Substitutions) -> Self {
        let substitutions = self.substitutions.compose(subst);
        let constraints = self.constraints.apply(&substitutions);
        let tree = self.tree.apply(&substitutions);
        Self {
            substitutions,
            constraints,
            tree,
        }
    }

    fn as_constrained_type(&self) -> Constrained<Type> {
        Constrained {
            constraints: self.constraints.clone(),
            underlying: self.tree.type_info().inferred_type.clone(),
        }
    }

    fn _map_tree<F>(self, f: &mut F) -> Self
    where
        F: FnMut(Expr) -> Expr,
    {
        Self {
            substitutions: self.substitutions,
            constraints: self.constraints,
            tree: self.tree.map(f),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct ConstraintSet(BTreeSet<Constraint>);

impl ConstraintSet {
    fn _len(&self) -> usize {
        self.0.len()
    }

    /// The constraints of `self` that `other` does not already carry.
    fn difference(&self, other: &ConstraintSet) -> ConstraintSet {
        ConstraintSet(
            self.0
                .iter()
                .filter(|c| !other.0.contains(*c))
                .cloned()
                .collect(),
        )
    }

    fn _contains(&self, constraint: &Constraint) -> bool {
        self.0.contains(constraint)
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn apply(&self, subst: &Substitutions) -> Self {
        let Self(constraints) = self;
        Self(constraints.iter().map(|c| c.apply(subst)).collect())
    }

    fn union(&self, ConstraintSet(rhs): ConstraintSet) -> ConstraintSet {
        let Self(lhs) = self;

        Self(lhs.union(&rhs).cloned().collect())
    }

    pub fn iter(&self) -> impl Iterator<Item = &Constraint> {
        self.0.iter()
    }

    pub fn into_iter(self) -> impl Iterator<Item = Constraint> {
        self.0.into_iter()
    }

    pub fn variables(&self) -> HashSet<MetaVariable> {
        self.0.iter().flat_map(|tv| tv.variables()).collect()
    }

    pub fn without<P>(&mut self, mut p: P)
    where
        P: FnMut(&Constraint) -> bool,
    {
        let Self(constraints) = self;
        constraints.retain(|c| !p(c));
    }
}

impl From<&[Constraint]> for ConstraintSet {
    fn from(value: &[Constraint]) -> Self {
        Self(value.iter().cloned().collect())
    }
}
impl From<&[&Constraint]> for ConstraintSet {
    fn from(value: &[&Constraint]) -> Self {
        Self(value.iter().copied().cloned().collect())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Constraint {
    pub constraint_type: Type,
}

impl Type {
    fn applied_name(&self) -> &QualifiedName {
        match self {
            Type::Apply { constructor, .. } => constructor.applied_name(),
            Type::Constructor(name) => name,
            otherwise => panic!("{otherwise}"),
        }
    }
}

impl Constraint {
    pub fn from_constraint_expr(
        types: &HashMap<parser::Identifier, MetaVariable>,
        expr: &phase::ConstraintExpression<Named>,
        ctx: &TypingContext,
    ) -> Typing<Constraint> {
        let constructor = ctx.types.lookup(&expr.class).ok_or_else(|| {
            TypeError::UndefinedSignature(expr.class.clone()).at(ParseInfo::default())
        })?;
        let arguments = expr
            .parameters
            .iter()
            .map(|te| te.synthesize_type(types, ctx))
            .collect::<Typing<Vec<_>>>()?;

        let constraint_type = constructor.definition().apply_at(&arguments);
        Ok(Self { constraint_type })
    }

    pub fn from_type_constructor(constructor: &TypeConstructor) -> Self {
        Self::from_assumed_spine(constructor.make_spine())
    }

    pub fn from_assumed_spine(constraint_type: Type) -> Self {
        Self { constraint_type }
    }

    pub fn name(&self) -> &QualifiedName {
        self.constraint_type.applied_name()
    }

    pub fn apply(&self, subst: &Substitutions) -> Self {
        Self {
            constraint_type: self.constraint_type.apply(subst),
        }
    }

    pub fn variables(&self) -> HashSet<MetaVariable> {
        self.constraint_type.variables()
    }

    /// A constraint whose constrained type is a bare type variable (e.g. `Eq α`).
    /// Applied `Memory_Layout` givens receive additional handling while elaborating
    /// a declared constrained term; undeclared inferred constraints cannot become
    /// parameters because they are absent from its registered source signature.
    pub fn is_parametric(&self) -> bool {
        matches!(
            &self.constraint_type,
            Type::Apply { argument, .. } if matches!(argument.as_ref(), Type::Variable(..))
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RecordType(Vec<(parser::Identifier, Type)>);

impl RecordType {
    fn from_fields(fields: &[(parser::Identifier, Type)]) -> Self {
        let mut fields = fields.to_vec();
        fields.sort_by(|(t, _), (u, _)| t.cmp(u));

        Self(fields)
    }

    pub fn shape(&self) -> RecordShape {
        RecordShape(self.0.iter().map(|(l, _)| l.clone()).collect())
    }

    fn apply(&self, subs: &Substitutions) -> Self {
        Self(
            self.0
                .iter()
                .map(|(id, t)| (id.clone(), t.apply(subs)))
                .collect(),
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CoproductType(Vec<(QualifiedName, Vec<Type>)>);

impl CoproductType {
    /// The constructors (name + argument types) of this coproduct, in sorted order.
    pub fn constructors(&self) -> impl Iterator<Item = &(QualifiedName, Vec<Type>)> {
        self.0.iter()
    }

    fn from_constructors(constructors: &[(QualifiedName, Vec<Type>)]) -> Self {
        let mut constructors = constructors.to_vec();
        constructors.sort_by(|(t, _), (u, _)| t.cmp(u));

        Self(constructors)
    }

    fn apply(&self, subs: &Substitutions) -> Self {
        Self(
            self.0
                .iter()
                .map(|(id, signature)| {
                    (
                        id.clone(),
                        signature.iter().map(|ty| ty.apply(subs)).collect(),
                    )
                })
                .collect(),
        )
    }

    fn signature(&self, constructor: &namer::QualifiedName) -> Option<&[Type]> {
        self.0
            .iter()
            .find_map(|(id, signature)| (id == constructor).then_some(signature.as_slice()))
    }
}

impl Kind {
    pub fn apply(self, at: Kind) -> Result<Self, TypeError> {
        match self {
            Kind::Arrow(k1, k2) => {
                let mut substitutions = BTreeMap::new();
                if k1.match_argument(&at, &mut substitutions) {
                    Ok(k2.apply_confinement_substitutions(&substitutions))
                } else {
                    Err(TypeError::KindMismatchError {
                        function: Kind::Arrow(k1, k2),
                        argument: at,
                    })
                }
            }
            otherwise => Err(TypeError::KindMismatchError {
                function: otherwise,
                argument: at,
            }),
        }
    }
}

/// The field/constructor chain from a confined composite down to the leaf that
/// makes it confined, with that leaf's type. Absent when the type is confined in
/// itself, in which case naming the type is already the whole explanation.
#[derive(Debug, Clone, Default)]
pub struct ConfinementPath(Option<(Vec<String>, Type)>);

impl fmt::Display for ConfinementPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            None => Ok(()),
            Some((path, leaf)) => write!(f, " because `{}` is `{leaf}`", path.join(".")),
        }
    }
}

/// One lexically captured variable, retained with its source position and type so
/// a failed capability check can name the capture that caused it rather than
/// reporting only that the enclosing action failed a constraint.
#[derive(Debug, Clone)]
pub struct Capture {
    parse_info: ParseInfo,
    ty: Type,
    confinement: Confinement,
}

/// The capture index of a lambda, plus the captures it was joined from. Inference
/// uses `joined` alone; the captures exist only so diagnostics can attribute a
/// confined index to a specific variable.
#[derive(Debug, Clone)]
pub struct CaptureConfinement {
    joined: Confinement,
    captures: Vec<Capture>,
}

impl CaptureConfinement {
    /// The first capture that is confined, in source order -- the one to blame
    /// when an action is rejected at a thread boundary.
    fn confined(&self) -> Option<&Capture> {
        self.captures
            .iter()
            .find(|capture| capture.confinement == Confinement::Confined)
    }

    /// Explain a failed capture-index check. When a specific capture is confined,
    /// blame it at its own source position; otherwise fall back to the opaque
    /// index mismatch, which is all the inference actually knows.
    fn mismatch(&self, expected: Confinement, pi: ParseInfo) -> Located<TypeError> {
        match self.confined() {
            Some(capture) => TypeError::ConfinedCapture {
                ty: capture.ty.clone(),
                // No type environment here to walk; the type alone is the blame.
                path: ConfinementPath::default(),
            }
            .at(capture.parse_info),
            None => TypeError::ConfinementMismatch {
                lhs: expected,
                rhs: self.joined.clone(),
            }
            .at(pi),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Type {
    Variable(MetaVariable),
    Base(BaseType),
    Arrow {
        capture: Confinement,
        domain: Box<Type>,
        codomain: Box<Type>,
    },
    Tuple(TupleType),
    Record(RecordType),
    Coproduct(CoproductType),
    Array(Box<Type>),
    Constructor(namer::QualifiedName),
    Apply {
        constructor: Box<Type>,
        argument: Box<Type>,
        /// Occurrence-specific capture index for constructors with a hidden
        /// capability parameter. Currently used by `IO`; ordinary applications
        /// leave it absent.
        capture: Option<Confinement>,
    },
}

impl Type {
    pub(crate) fn application(constructor: Type, argument: Type) -> Self {
        let capture = matches!(
            &constructor,
            Type::Constructor(name) if *name == io_type_name()
        )
        .then(Confinement::fresh);
        Self::Apply {
            constructor: constructor.into(),
            argument: argument.into(),
            capture,
        }
    }

    pub fn kind(&self, ctx: &TypeEnvironment) -> Result<Kind, TypeError> {
        fn inhabited(kind: Kind) -> Result<Confinement, TypeError> {
            match kind {
                Kind::Star(confinement) => Ok(confinement),
                kind => Err(TypeError::ExpectedMonotypeKind { kind }),
            }
        }

        match self {
            Self::Variable(tp) => Ok(tp.kind().clone()),
            Self::Base(BaseType::Array) => {
                let element = Confinement::fresh();
                Ok(Kind::Arrow(
                    Kind::Star(element.clone()).into(),
                    Kind::Star(element).into(),
                ))
            }
            Self::Base(..) => Ok(Kind::unconfined()),
            Self::Arrow { capture, .. } => Ok(Kind::Star(capture.clone())),
            Self::Tuple(tuple) => Ok(Kind::Star(Confinement::join(
                tuple
                    .elements()
                    .iter()
                    .map(|element| element.kind(ctx).and_then(inhabited))
                    .collect::<Result<Vec<_>, _>>()?,
            ))),
            Self::Record(record) => Ok(Kind::Star(Confinement::join(
                record
                    .0
                    .iter()
                    .map(|(_, field)| field.kind(ctx).and_then(inhabited))
                    .collect::<Result<Vec<_>, _>>()?,
            ))),
            Self::Coproduct(coproduct) => Ok(Kind::Star(Confinement::join(
                coproduct
                    .0
                    .iter()
                    .flat_map(|(_, arguments)| arguments)
                    .map(|argument| argument.kind(ctx).and_then(inhabited))
                    .collect::<Result<Vec<_>, _>>()?,
            ))),
            Self::Array(element) => Ok(Kind::Star(inhabited(element.kind(ctx)?)?)),
            Self::Constructor(name) => ctx
                .lookup(name)
                .ok_or_else(|| TypeError::UndefinedType(name.clone()))
                .map(|tc| tc.kind())
                .cloned(),
            Self::Apply {
                constructor,
                argument,
                capture,
            } => {
                if let Some(capture) = capture {
                    let result = inhabited(argument.kind(ctx)?)?;
                    return Ok(Kind::Star(Confinement::join([capture.clone(), result])));
                }
                let k1 = constructor.kind(ctx)?;
                let k2 = argument.kind(ctx)?;
                //println!("kind: k1 {constructor}; k2 {argument}");
                k1.apply(k2)
            }
        }
    }

    pub fn fresh() -> Self {
        Self::Variable(MetaVariable::fresh())
    }

    pub fn fresh_with_kind(kind: Kind) -> Self {
        Self::Variable(MetaVariable::fresh_with_kind(kind))
    }

    pub fn is_base(&self) -> bool {
        matches!(self, Type::Base(..))
    }

    pub fn walk<F>(&self, f: &mut F)
    where
        F: FnMut(&Type),
    {
        f(self);

        match self {
            Self::Arrow {
                domain, codomain, ..
            } => {
                f(domain);
                domain.walk(f);
                f(codomain);
                codomain.walk(f);
            }

            Self::Tuple(tuple) => tuple.elements().iter().for_each(|ty| {
                f(ty);
                ty.walk(f)
            }),

            Self::Record(record) => record.0.iter().for_each(|(_, ty)| {
                f(ty);
                ty.walk(f)
            }),

            Self::Coproduct(coproduct) => coproduct.0.iter().for_each(|(_, args)| {
                args.iter().for_each(|ty| {
                    f(ty);
                    ty.walk(f);
                })
            }),

            Self::Apply {
                constructor,
                argument,
                ..
            } => {
                f(constructor);
                constructor.walk(f);
                f(argument);
                argument.walk(f);
            }

            otherwise => f(otherwise),
        }
    }

    pub fn variables(&self) -> HashSet<MetaVariable> {
        let mut vars = HashSet::default();
        self.walk(&mut |ty| {
            if let Type::Variable(tp) = ty {
                vars.insert(tp.clone());
            }
        });
        vars
    }

    pub fn confinement_variables(&self) -> BTreeSet<u32> {
        match self {
            Self::Variable(variable) => variable.kind().confinement_variables(),
            Self::Base(_) | Self::Constructor(_) => BTreeSet::new(),
            Self::Arrow {
                capture,
                domain,
                codomain,
            } => capture
                .variables()
                .into_iter()
                .chain(domain.confinement_variables())
                .chain(codomain.confinement_variables())
                .collect(),
            Self::Tuple(tuple) => tuple
                .elements()
                .iter()
                .flat_map(Self::confinement_variables)
                .collect(),
            Self::Record(record) => record
                .0
                .iter()
                .flat_map(|(_, field)| field.confinement_variables())
                .collect(),
            Self::Coproduct(coproduct) => coproduct
                .0
                .iter()
                .flat_map(|(_, arguments)| arguments)
                .flat_map(Self::confinement_variables)
                .collect(),
            Self::Array(element) => element.confinement_variables(),
            Self::Apply {
                constructor,
                argument,
                capture,
            } => capture
                .iter()
                .flat_map(Confinement::variables)
                .chain(constructor.confinement_variables())
                .chain(argument.confinement_variables())
                .collect(),
        }
    }

    //    #[instrument]
    pub fn apply(&self, subs: &Substitutions) -> Self {
        //trace!("{self} -- subs {subs}");

        match self {
            Self::Variable(param) => {
                // Follow variable→variable chains iteratively. Unification can
                // compose a substitution containing a cycle of mutually-equal
                // variables (e.g. `$a ↦ $b`, `$b ↦ $a`, produced when two match
                // clauses unify their scrutinee spines in opposite directions).
                // Such a cycle is sound — the variables were unified, so they are
                // equal — but chasing it recursively would loop forever. Resolve
                // the chain to a stable canonical representative instead.
                let mut current = param.clone();
                let mut seen = HashSet::<MetaVariable>::default();
                let resolved = loop {
                    match subs.substitution(&current) {
                        None => break Self::Variable(current),
                        // Identity self-binding: nothing more to resolve.
                        Some(Type::Variable(next)) if *next == current => {
                            break Self::Variable(current);
                        }
                        Some(Type::Variable(next)) => {
                            if !seen.insert(current.clone()) {
                                // Closed a variable cycle: every variable in it is
                                // equal, so pick a deterministic representative.
                                let rep = seen.into_iter().min().unwrap_or(current);
                                break Self::Variable(rep);
                            }
                            current = next.clone();
                        }
                        // A non-variable binding: substitute it structurally.
                        Some(t) => break t.clone().apply(subs),
                    }
                };
                match resolved {
                    Self::Variable(variable) => {
                        Self::Variable(variable.apply_confinements(&subs.confinements))
                    }
                    other => other,
                }
            }

            Self::Base(b) => Self::Base(b.clone()),

            Self::Arrow {
                capture,
                domain,
                codomain,
            } => Self::Arrow {
                capture: capture.apply(&subs.confinements),
                domain: domain.apply(subs).into(),
                codomain: codomain.apply(subs).into(),
            },

            Self::Tuple(tuple) => Self::Tuple(TupleType::from_signature(
                &tuple
                    .elements()
                    .iter()
                    .map(|ty| ty.apply(subs))
                    .collect::<Vec<_>>(),
            )),

            Self::Record(record) => Self::Record(record.apply(subs)),

            Self::Coproduct(coproduct) => Self::Coproduct(coproduct.apply(subs)),

            Self::Array(element_type) => Self::Array(element_type.apply(subs).into()),

            Self::Constructor(..) => self.clone(),

            Self::Apply {
                constructor,
                argument,
                capture,
            } => Self::Apply {
                constructor: constructor.apply(subs).into(),
                argument: argument.apply(subs).into(),
                capture: capture
                    .as_ref()
                    .map(|capture| capture.apply(&subs.confinements)),
            },
        }
    }

    pub fn unified_with(
        &self,
        rhs: &Self,
        ctx: &TypeEnvironment,
    ) -> Result<Substitutions, TypeError> {
        let lhs_normalized = ctx.normalize_alias(self)?;
        let rhs_normalized = ctx.normalize_alias(rhs)?;
        if lhs_normalized.is_some() || rhs_normalized.is_some() {
            return lhs_normalized
                .as_ref()
                .unwrap_or(self)
                .unified_with(rhs_normalized.as_ref().unwrap_or(rhs), ctx);
        }

        let lhs_kind = self.kind(ctx)?;
        let rhs_kind = rhs.kind(ctx)?;
        if !lhs_kind.is_compatible_with(&rhs_kind) {
            Err(TypeError::KindMismatch {
                lhs: self.clone(),
                lhs_kind,
                rhs: rhs.clone(),
                rhs_kind,
            })?
        }

        match (self, rhs) {
            (lhs, rhs) if lhs == rhs => Ok(Substitutions::default()),

            (Self::Variable(p), ty) | (ty, Self::Variable(p)) => {
                if ty.variables().contains(p) {
                    Err(TypeError::InfiniteType {
                        param: p.clone(),
                        ty: ty.clone(),
                    })
                } else {
                    let ty_kind = ty.kind(ctx)?;
                    let kind_substitutions = match p.kind().unify_confinements(&ty_kind) {
                        Some(substitutions) => Substitutions::with_confinements(substitutions),
                        None => {
                            if let (Kind::Star(required), Kind::Star(actual)) = (p.kind(), &ty_kind)
                            {
                                return Err(TypeError::ConfinementRequirement {
                                    path: ConfinementPath::default(),
                                    ty: ty.clone(),
                                    actual: actual.clone(),
                                    required: required.clone(),
                                });
                            }
                            return Err(TypeError::KindMismatch {
                                lhs: Self::Variable(p.clone()),
                                lhs_kind: p.kind().clone(),
                                rhs: ty.clone(),
                                rhs_kind: ty_kind,
                            });
                        }
                    };
                    let type_substitution =
                        Substitutions::from(vec![(p.clone(), ty.apply(&kind_substitutions))]);
                    Ok(kind_substitutions.compose(&type_substitution))
                }
            }

            (
                Self::Arrow {
                    capture: lhs_capture,
                    domain: lhs_dom,
                    codomain: lhs_codom,
                },
                Self::Arrow {
                    capture: rhs_capture,
                    domain: rhs_dom,
                    codomain: rhs_codom,
                },
            ) => {
                let captures = lhs_capture
                    .unify(rhs_capture)
                    .map(Substitutions::with_confinements)
                    .ok_or_else(|| TypeError::ConfinementMismatch {
                        lhs: lhs_capture.clone(),
                        rhs: rhs_capture.clone(),
                    })?;
                let domain = lhs_dom
                    .apply(&captures)
                    .unified_with(&rhs_dom.apply(&captures), ctx)?;
                let substitutions = captures.compose(&domain);
                let codomain = lhs_codom
                    .apply(&substitutions)
                    .unified_with(&rhs_codom.apply(&substitutions), ctx)?;
                Ok(substitutions.compose(&codomain))
            }

            (Self::Tuple(lhs), Self::Tuple(rhs)) if lhs.arity() == rhs.arity() => {
                let mut subs = Substitutions::default();

                for (lhs, rhs) in lhs.elements().iter().zip(rhs.elements()) {
                    // compose_mut
                    subs = subs.compose(&lhs.apply(&subs).unified_with(&rhs.apply(&subs), ctx)?);
                }

                Ok(subs)
            }

            (Self::Record(lhs), Self::Record(rhs)) if lhs.0.len() == rhs.0.len() => {
                let mut subs = Substitutions::default();

                // Sort first?
                for ((lhs_label, lhs), (rhs_label, rhs)) in lhs.0.iter().zip(&rhs.0) {
                    if lhs_label != rhs_label {
                        panic!("{lhs_label} != {rhs_label}");
                    }

                    // compose_mut
                    subs = subs.compose(&lhs.apply(&subs).unified_with(&rhs.apply(&subs), ctx)?);
                }

                Ok(subs)
            }

            (
                Self::Apply {
                    constructor: lhs_con,
                    argument: lhs_arg,
                    capture: lhs_capture,
                },
                Self::Apply {
                    constructor: rhs_con,
                    argument: rhs_arg,
                    capture: rhs_capture,
                },
            ) => {
                let captures = match (lhs_capture, rhs_capture) {
                    (Some(lhs), Some(rhs)) => lhs
                        .unify(rhs)
                        .map(Substitutions::with_confinements)
                        .ok_or_else(|| TypeError::ConfinementMismatch {
                            lhs: lhs.clone(),
                            rhs: rhs.clone(),
                        })?,
                    _ => Substitutions::default(),
                };
                let constructor = lhs_con
                    .apply(&captures)
                    .unified_with(&rhs_con.apply(&captures), ctx)?;
                let constructor = captures.compose(&constructor);
                let argument = lhs_arg
                    .apply(&constructor)
                    .unified_with(&rhs_arg.apply(&constructor), ctx)?;
                Ok(constructor.compose(&argument))
            }

            (lhs, rhs) => {
                //panic!("lhs {lhs:?}; rhs {rhs:?}");
                //println!("lhs {lhs:?}; rhs {rhs:?}");

                Err(TypeError::UnificationImpossible {
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                })
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum BaseType {
    Int,
    Float,
    Text,
    Bool,
    Unit,
    Char,
    Array,
}

impl BaseType {
    const fn local_name(&self) -> &str {
        match self {
            Self::Int => "Int",
            Self::Float => "Float",
            Self::Text => "Text",
            Self::Bool => "Bool",
            Self::Unit => "Unit",
            Self::Char => "Char",
            Self::Array => "Array",
        }
    }

    pub fn qualified_name(&self) -> namer::QualifiedName {
        namer::QualifiedName::builtin(self.local_name())
    }
}

// The stdlib `Text` type (`opaque Text ::= Text Bytes`, in `Stdlib/Text.lady`). `Text`
// is no longer a builtin base type: string literals and interpolation elaborate to this
// stdlib DU, whose sole newtype-erased field is a `Bytes` (a raw slice). This is the one
// deliberate compiler->stdlib reference (languages special-case `String` the same way);
// it resolves from the global type table, so any program that reaches the elaborator has
// `Stdlib.Text` on its library path.
pub fn stdlib_text_type() -> Type {
    // `Text` lives in the always-imported primordial `Prelude` (Root.Prelude.Text) -- the
    // single deliberate compiler->stdlib reference for the string-literal type.
    Type::Constructor(prelude_name("Text"))
}

/// The primordial `IO` type constructor (`Root.Prelude.IO`) and its sole constructor
/// `Suspend` (`Root.Prelude.IO = Suspend (Unit -> α)`). These are the single sanctioned
/// compiler->stdlib references for IO, mirroring [`stdlib_text_type`] for string literals;
/// the strict-IO lowering (`simplify::deforest_io`) compares against them by identity rather
/// than matching mangled names.
pub fn io_type_name() -> namer::QualifiedName {
    prelude_name("IO")
}

pub fn suspend_constructor_name() -> namer::QualifiedName {
    prelude_name("Suspend")
}

// A member of the always-imported primordial `Prelude` (`Root.Prelude.<member>`).
fn prelude_name(member: &str) -> namer::QualifiedName {
    let module = parser::IdentifierPath::new("Root").with_suffix("Prelude");
    namer::QualifiedName::new(module, member)
}

// The compiler-derived `Memory_Layout` class (see Prelude): a ground `Memory_Layout τ`
// constraint is discharged not by a user witness but by compiler-synthesised evidence
// -- a reference to the `memory_layout` marker term whose inferred type is the ground
// `Memory_Layout τ`, from which the backend recovers `τ` and emits the layout dictionary.
pub fn memory_layout_class() -> namer::QualifiedName {
    prelude_name("Memory_Layout")
}

pub fn memory_layout_evidence_name() -> namer::QualifiedName {
    prelude_name("memory_layout")
}

/// Whether an abstract layout must be forwarded from a concrete caller.
///
/// Element-zero discovery is complete for products whose abstract parameters sit
/// behind one-word boundaries (for example `Raw_State a b`, whose polymorphic
/// entries field is itself a `Mutable_Array`). It is not complete for a sum such as
/// `Perhaps (Entry a b)`: an array initialized with `Nope` has no payload from which
/// to discover the `This` shape. Keep a hidden dictionary only for the latter class
/// of layout, instead of charging every HashTable operation for its product-state
/// descriptor too.
pub(crate) fn memory_layout_requires_parameter(
    constraint: &Constraint,
    types: &TypeEnvironment,
) -> bool {
    let Type::Apply { argument, .. } = &constraint.constraint_type else {
        return false;
    };
    let required = layout_shape_depends_on_parameters(argument, types, &mut Vec::new());
    if std::env::var_os("DUMP_LAYOUT_PARAMETERS").is_some() {
        eprintln!("[layout-parameter] {argument} required={required}");
    }
    required
}

fn layout_shape_depends_on_parameters(
    ty: &Type,
    types: &TypeEnvironment,
    on_path: &mut Vec<QualifiedName>,
) -> bool {
    match ty {
        // A naked abstract element can later be any representation, including a
        // sum, so its concrete caller must decide the layout.
        Type::Variable(..) => true,
        Type::Tuple(tuple) => tuple
            .elements()
            .iter()
            .any(|field| layout_shape_depends_on_parameters(field, types, on_path)),
        Type::Record(record) => record
            .0
            .iter()
            .any(|(_, field)| layout_shape_depends_on_parameters(field, types, on_path)),
        Type::Coproduct(coproduct) => {
            if coproduct.0.is_empty() {
                // Opaque/foreign types have no visible constructors and are stored
                // as one canonical reference word.
                return false;
            }
            // A single-field newtype is erased, so look through it. Every real sum
            // needs all variants described before element zero is initialized.
            if let [(_, fields)] = coproduct.0.as_slice()
                && let [field] = fields.as_slice()
            {
                layout_shape_depends_on_parameters(field, types, on_path)
            } else {
                true
            }
        }
        Type::Constructor(..) | Type::Apply { .. } => {
            let name = match ty {
                Type::Constructor(name) => name,
                Type::Apply { .. } => ty.applied_name(),
                _ => unreachable!(),
            };
            // Recursive representation knots and unknown/foreign constructors are
            // one boxed word, independent of their arguments.
            if on_path.contains(name) {
                return false;
            }
            let Some(constructor) = types.lookup(name) else {
                return false;
            };
            let Ok(substitutions) = constructor.make_spine().unified_with(ty, types) else {
                return true;
            };
            let Ok(structure) = constructor.structure() else {
                return true;
            };
            let structure = structure.materialize_monotype().apply(&substitutions);
            on_path.push(name.clone());
            let result = layout_shape_depends_on_parameters(&structure, types, on_path);
            on_path.pop();
            result
        }
        // Scalars, functions, arrays, and other canonical references occupy one
        // word regardless of any type hidden behind them.
        Type::Base(..) | Type::Arrow { .. } | Type::Array(..) => false,
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TupleType(pub Vec<Type>);

impl TupleType {
    pub fn from_signature(signature: &[Type]) -> Self {
        Self(signature.to_vec())
    }

    pub fn elements(&self) -> &[Type] {
        self.0.as_slice()
    }

    pub fn arity(&self) -> usize {
        self.0.len()
    }

    pub fn is_fully_typed(&self) -> bool {
        self.0.iter().all(|t| t.variables().is_empty())
    }
}

impl RecordSymbol<QualifiedName> {
    fn synthesize_type(
        &self,
        type_params: &HashMap<parser::Identifier, MetaVariable>,
        ctx: &TypingContext,
    ) -> Typing<TypeStructure> {
        Ok(TypeStructure::PolyRecord(PolyRecordType::from_fields(
            &self
                .fields
                .iter()
                .map(|f| {
                    f.type_signature
                        .type_scheme(type_params, ctx)
                        .map(|scheme| (f.name.clone(), scheme))
                })
                .collect::<Typing<Vec<_>>>()?,
        )))
    }
}

impl CoproductSymbol<QualifiedName> {
    pub fn synthesize_type(
        &self,
        type_params: &HashMap<parser::Identifier, MetaVariable>,
        ctx: &TypingContext,
    ) -> Typing<Type> {
        Ok(Type::Coproduct(CoproductType::from_constructors(
            &self
                .constructors
                .iter()
                .map(|c| {
                    c.signature
                        .iter()
                        .map(|te| te.synthesize_type(type_params, ctx))
                        .collect::<Typing<Vec<_>>>()
                        .map(|signature| (c.name.clone(), signature))
                })
                .collect::<Typing<Vec<_>>>()?,
        )))
    }
}

impl phase::TypeExpression<Named> {
    fn synthesize_type(
        &self,
        type_params: &HashMap<parser::Identifier, MetaVariable>,
        ctx: &TypingContext,
    ) -> Typing<Type> {
        match self {
            Self::Constructor(pi, name) => {
                let constructor = ctx
                    .types
                    .lookup(name)
                    .ok_or_else(|| TypeError::UndefinedType(name.clone()).at(*pi))?;

                Ok(constructor
                    .definition()
                    .as_base_type()
                    .unwrap_or_else(|| constructor.definition().head()))
            }

            Self::Parameter(pi, p) => type_params
                .get(p)
                .cloned()
                .map(Type::Variable)
                .ok_or_else(|| TypeError::UnquantifiedTypeParameter(p.clone()).at(*pi)),

            Self::Apply(
                _,
                ast::ApplyTypeExpr {
                    function, argument, ..
                },
            ) => Ok(Type::application(
                function.synthesize_type(type_params, ctx)?,
                argument.synthesize_type(type_params, ctx)?,
            )),

            Self::ConfinementAscription(pi, body, required) => {
                let body = body.synthesize_type(type_params, ctx)?;
                let kind = body.kind(&ctx.types).map_err(|error| error.at(*pi))?;
                let actual = kind.confinement().cloned().ok_or_else(|| {
                    TypeError::ExpectedMonotypeKind { kind: kind.clone() }.at(*pi)
                })?;
                let required = Confinement::from(*required);
                let substitutions = actual.require(required.clone()).ok_or_else(|| {
                    TypeError::ConfinementMismatch {
                        lhs: actual,
                        rhs: required,
                    }
                    .at(*pi)
                })?;
                Ok(body.apply(&Substitutions::with_confinements(substitutions)))
            }

            Self::Arrow(
                _,
                ast::ArrowTypeExpr {
                    capture,
                    domain,
                    codomain,
                },
            ) => Ok(Type::Arrow {
                // The surface arrow's index is a template, not a named variable:
                // every synthesis of a signature/alias occurrence receives an
                // independent hidden capture metavariable. Capability ascriptions
                // immediately constrain this fresh index when present.
                capture: capture.freshen(&mut BTreeMap::new()),
                domain: domain.synthesize_type(type_params, ctx)?.into(),
                codomain: codomain.synthesize_type(type_params, ctx)?.into(),
            }),

            Self::Tuple(_, TupleTypeExpr(elements)) => Ok(Type::Tuple(TupleType::from_signature(
                &elements
                    .iter()
                    .map(|te| te.synthesize_type(type_params, ctx))
                    .collect::<Typing<Vec<_>>>()?,
            ))),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ElaboratedTypeConstructor {
    pub definition: TypeConstructorDefinition,
    pub structure: TypeStructure,
}

#[derive(Debug, Clone)]
pub struct TypeConstructorDefinition {
    pub name: namer::QualifiedName,
    pub instantiated_params: HashMap<parser::Identifier, MetaVariable>,
    pub defining_symbol: TypeSymbol<namer::QualifiedName>,
    /// The hidden, occurrence-specific capture index of `IO`.  Keeping it on
    /// the instantiated constructor makes the `Suspend` field and the `IO α`
    /// spine refer to the same index.
    hidden_capture: Option<Confinement>,
}

impl TypeConstructorDefinition {
    fn make_spine(&self) -> Type {
        self.make_spine_at(&self.instantiated_params)
    }

    pub fn make_spine_at(
        &self,
        type_parameters: &HashMap<parser::Identifier, MetaVariable>,
    ) -> Type {
        let mut spine = self.defining_symbol.type_parameters().iter().fold(
            Type::Constructor(self.name.clone()),
            |constructor, param| {
                Type::application(
                    constructor,
                    Type::Variable(type_parameters[&param.name].clone()),
                )
            },
        );
        if let (Some(hidden_capture), Type::Apply { capture, .. }) =
            (&self.hidden_capture, &mut spine)
        {
            *capture = Some(hidden_capture.clone());
        }
        spine
    }

    pub fn apply_at(&self, arguments: &[Type]) -> Type {
        arguments.iter().fold(
            Type::Constructor(self.name.clone()),
            |constructor, argument| Type::application(constructor, argument.clone()),
        )
    }

    fn as_base_type(&self) -> Option<Type> {
        match &self.defining_symbol.definition {
            TypeDefinition::BaseType(BaseType::Array) => None,
            TypeDefinition::BaseType(base_type) => Some(Type::Base(base_type.clone())),
            _otherwise => None,
        }
    }

    fn head(&self) -> Type {
        Type::Constructor(self.name.clone())
    }
}

#[derive(Debug, Clone)]
pub struct PolyRecordType(Vec<(parser::Identifier, TypeScheme)>);

impl PolyRecordType {
    pub fn from_fields(fields: &[(parser::Identifier, TypeScheme)]) -> Self {
        let mut fields = fields.to_vec();
        fields.sort_by(|(t, _), (u, _)| t.cmp(u));

        Self(fields.to_vec())
    }

    pub fn shape(&self) -> RecordShape {
        RecordShape(self.0.iter().map(|(label, _)| label).cloned().collect())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn fields(&self) -> impl Iterator<Item = &(parser::Identifier, TypeScheme)> {
        self.0.iter()
    }

    pub fn field_info(&self, field_name: &parser::Identifier) -> Option<(usize, &TypeScheme)> {
        self.0
            .iter()
            .enumerate()
            .find_map(|(index, (name, scheme))| (name == field_name).then_some((index, scheme)))
    }

    pub fn apply(&self, subst: &Substitutions) -> Self {
        Self(
            self.0
                .iter()
                .map(|(label, scheme)| (label.clone(), scheme.apply(subst)))
                .collect(),
        )
    }

    pub fn materialize_type(&self) -> Type {
        Type::Record(RecordType::from_fields(
            &self
                .0
                .iter()
                .map(|(label, scheme)| (label.clone(), scheme.instantiate().underlying.clone()))
                .collect::<Vec<_>>(),
        ))
    }

    pub fn map<F>(&self, f: F) -> Self
    where
        F: Fn(&TypeScheme) -> TypeScheme,
    {
        let Self(fields) = self;
        Self(
            fields
                .iter()
                .map(|(field, scheme)| (field.clone(), f(scheme)))
                .collect(),
        )
    }
}

#[derive(Debug, Clone)]
pub enum TypeStructure {
    Monotype(Type),
    PolyRecord(PolyRecordType),
}

impl TypeStructure {
    fn apply(&self, subst: &Substitutions) -> Self {
        match self {
            Self::Monotype(ty) => Self::Monotype(ty.apply(subst)),
            Self::PolyRecord(shape) => Self::PolyRecord(shape.apply(subst)),
        }
    }

    fn materialize_monotype(&self) -> Type {
        match self {
            Self::Monotype(monotype) => monotype.clone(),
            Self::PolyRecord(record) => record.materialize_type(),
        }
    }

    fn tie_io_capture(&mut self, capture: Confinement) -> bool {
        let Self::Monotype(Type::Coproduct(coproduct)) = self else {
            return false;
        };
        let Some((_, signature)) = coproduct
            .0
            .iter_mut()
            .find(|(name, _)| *name == suspend_constructor_name())
        else {
            return false;
        };
        let [
            Type::Arrow {
                capture: thunk_capture,
                ..
            },
        ] = signature.as_mut_slice()
        else {
            return false;
        };
        *thunk_capture = capture;
        true
    }
}

#[derive(Debug, Clone)]
pub enum TypeConstructor {
    Unelaborated(TypeConstructorDefinition),
    Elaborated(ElaboratedTypeConstructor),
}

impl TypeConstructor {
    fn arity(&self) -> usize {
        self.definition().defining_symbol.arity
    }

    fn kind(&self) -> &Kind {
        &self.definition().defining_symbol.kind
    }

    fn from_symbol(symbol: &TypeSymbol<namer::QualifiedName>) -> Self {
        if let TypeDefinition::BaseType(base_type) = &symbol.definition {
            Self::Elaborated(ElaboratedTypeConstructor {
                definition: TypeConstructorDefinition {
                    name: symbol.qualified_name(),
                    instantiated_params: HashMap::default(),
                    defining_symbol: symbol.clone(),
                    hidden_capture: None,
                },
                structure: TypeStructure::Monotype(Type::Base(base_type.clone())),
            })
        } else {
            Self::Unelaborated(TypeConstructorDefinition {
                name: symbol.qualified_name(),
                instantiated_params: fresh_type_parameters(symbol),
                defining_symbol: symbol.clone(),
                hidden_capture: (symbol.qualified_name() == io_type_name())
                    .then(Confinement::fresh),
            })
        }
    }

    fn elaborate(&mut self, ctx: &TypingContext) -> Typing<()> {
        if let Self::Unelaborated(constructor) = self {
            *self = from_definition(constructor, ctx)?;
        }

        Ok(())
    }

    fn reelaborate(&self, ctx: &TypingContext) -> Typing<TypeConstructor> {
        let (Self::Unelaborated(definition)
        | Self::Elaborated(ElaboratedTypeConstructor { definition, .. })) = self;

        from_definition(definition, ctx)
    }

    fn apply(&self, subs: &Substitutions) -> Self {
        if let Self::Elaborated(constructor) = self {
            Self::Elaborated(ElaboratedTypeConstructor {
                definition: constructor.definition.clone(),
                structure: constructor.structure.apply(subs),
            })
        } else {
            panic!("Attempt to substitute into unelaborated type constructor `{self}`")
        }
    }

    fn make_spine(&self) -> Type {
        self.definition().make_spine()
    }

    fn definition(&self) -> &TypeConstructorDefinition {
        match self {
            Self::Unelaborated(header) => header,
            Self::Elaborated(constructor) => &constructor.definition,
        }
    }

    fn definition_mut(&mut self) -> &mut TypeConstructorDefinition {
        match self {
            Self::Unelaborated(header) => header,
            Self::Elaborated(constructor) => &mut constructor.definition,
        }
    }

    pub fn structure(&self) -> Typing<&TypeStructure> {
        if let Self::Elaborated(c) = self {
            Ok(&c.structure)
        } else {
            Err(
                TypeError::UnelaboratedConstructor(self.definition().name.clone())
                    .at(ParseInfo::default()),
            )
        }
    }

    pub fn structure_mut(&mut self) -> Typing<&mut TypeStructure> {
        if let Self::Elaborated(c) = self {
            Ok(&mut c.structure)
        } else {
            Err(
                TypeError::UnelaboratedConstructor(self.definition().name.clone())
                    .at(ParseInfo::default()),
            )
        }
    }

    fn instantiate(&self, ctx: &TypingContext) -> Typing<Self> {
        let mut the = Self::from_symbol(&self.definition().defining_symbol);
        the.elaborate(ctx)?;
        Ok(the)
    }

    fn defining_context(&self) -> &parser::IdentifierPath {
        self.definition().name.module()
    }
}

fn from_definition(
    definition: &TypeConstructorDefinition,
    ctx: &TypingContext,
) -> Typing<TypeConstructor> {
    let mut structure = definition
        .defining_symbol
        .definition
        .synthesize_type(&definition.instantiated_params, ctx)?;
    if let Some(capture) = &definition.hidden_capture
        && !structure.tie_io_capture(capture.clone())
    {
        Err(TypeError::InternalAssertion(
            "Prelude.IO must have the form `IO ::= ∀α. Suspend (Unit -> α)`".to_owned(),
        )
        .at(ParseInfo::default()))?;
    }
    Ok(TypeConstructor::Elaborated(ElaboratedTypeConstructor {
        definition: definition.clone(),
        structure,
    }))
}

fn fresh_type_parameters(
    symbol: &TypeSymbol<QualifiedName>,
) -> HashMap<parser::Identifier, MetaVariable> {
    symbol
        .type_parameters()
        .iter()
        .map(|tv| {
            (
                tv.name.clone(),
                MetaVariable::fresh_with_kind(tv.kind.clone()),
            )
        })
        .collect()
}

impl TypeDefinition<QualifiedName> {
    pub fn synthesize_type(
        &self,
        type_param_map: &HashMap<parser::Identifier, MetaVariable>,
        ctx: &TypingContext,
    ) -> Typing<TypeStructure> {
        match self {
            Self::Record(record) => record.synthesize_type(type_param_map, ctx),
            Self::Signature(sig) => sig.vtable.synthesize_type(type_param_map, ctx),
            Self::Coproduct(coproduct) => Ok(TypeStructure::Monotype(
                coproduct.synthesize_type(type_param_map, ctx)?,
            )),
            Self::Alias(alias) => Ok(TypeStructure::Monotype(
                alias.body.synthesize_type(type_param_map, ctx)?,
            )),
            Self::BaseType(base_type) => Ok(TypeStructure::Monotype(Type::Base(base_type.clone()))),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeScheme {
    pub quantifiers: Vec<MetaVariable>,
    pub confinement_quantifiers: BTreeSet<u32>,
    pub underlying: Type,
    pub constraints: ConstraintSet,
}

impl TypeScheme {
    pub fn apply(&self, subst: &Substitutions) -> Self {
        let mut subst = subst.clone();
        for q in &self.quantifiers {
            subst.remove(q);
        }
        for q in &self.confinement_quantifiers {
            subst.confinements.remove(q);
        }
        Self {
            quantifiers: self.quantifiers.clone(),
            confinement_quantifiers: self.confinement_quantifiers.clone(),
            underlying: self.underlying.apply(&subst),
            constraints: self.constraints.apply(&subst),
        }
    }

    fn instantiation_substitutions(&self) -> Substitutions {
        let confinements = self
            .confinement_quantifiers
            .iter()
            .map(|id| (*id, Confinement::fresh()))
            .collect::<BTreeMap<_, _>>();
        let types = self
            .quantifiers
            .iter()
            .map(|tp| {
                (
                    tp.clone(),
                    Type::fresh_with_kind(tp.kind().apply_confinement_substitutions(&confinements)),
                )
            })
            .collect::<Vec<_>>();
        Substitutions {
            types,
            confinements,
        }
    }

    /// Reject a declared signature the body cannot actually deliver: instantiate the
    /// `∀`-vars, unify with `inferred`, and fail if any collapsed with another or was
    /// pinned to a concrete type -- i.e. this scheme promises more polymorphism than
    /// the definition has.
    fn reject_if_more_general_than(
        &self,
        inferred: &Type,
        name: &QualifiedName,
        pi: ParseInfo,
        ctx: &TypingContext,
    ) -> Typing<()> {
        let quantifiers = self.instantiation_substitutions();
        let reconciliation = self
            .underlying
            .apply(&quantifiers)
            .unified_with(inferred, &ctx.types)
            .map_err(|e| e.at(pi))?;

        let mut witnessed = HashSet::new();
        for (_, fresh) in quantifiers.iter() {
            match fresh.apply(&reconciliation) {
                Type::Variable(v) if witnessed.insert(v.clone()) => {}
                _ => Err(TypeError::SignatureTooGeneral {
                    name: name.clone(),
                    declared: self.underlying.clone(),
                    inferred: inferred.clone(),
                }
                .at(pi))?,
            }
        }
        Ok(())
    }

    pub fn instantiate(&self) -> Constrained<Type> {
        let subst = self.instantiation_substitutions();
        Constrained {
            constraints: self.constraints.apply(&subst),
            underlying: self.underlying.apply(&subst),
        }
    }

    pub fn from_constant(ty: Type) -> TypeScheme {
        Self {
            quantifiers: vec![],
            confinement_quantifiers: BTreeSet::new(),
            underlying: ty,
            constraints: ConstraintSet::default(),
        }
    }

    pub fn free_variables(&self) -> HashSet<MetaVariable> {
        let mut vars = self.underlying.variables();
        for q in &self.quantifiers {
            vars.remove(q);
        }
        vars
    }

    pub fn free_confinement_variables(&self) -> BTreeSet<u32> {
        self.underlying
            .confinement_variables()
            .difference(&self.confinement_quantifiers)
            .copied()
            .collect()
    }
}

#[derive(Debug, Clone)]
pub struct MetaVariable(u32, Kind);

static FRESH_TYPE_ID: AtomicU32 = AtomicU32::new(0);

impl MetaVariable {
    pub fn fresh() -> Self {
        Self::fresh_with_kind(Kind::default())
    }

    pub fn fresh_with_kind(kind: Kind) -> Self {
        Self(FRESH_TYPE_ID.fetch_add(1, Ordering::SeqCst), kind)
    }

    pub fn kind(&self) -> &Kind {
        &self.1
    }

    fn apply_confinements(&self, substitutions: &BTreeMap<u32, Confinement>) -> Self {
        Self(
            self.0,
            self.1.apply_confinement_substitutions(substitutions),
        )
    }
}

impl PartialEq for MetaVariable {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for MetaVariable {}

impl Hash for MetaVariable {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl PartialOrd for MetaVariable {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for MetaVariable {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

//pub struct Substitutions(Vec<(TypeParamter, Type)>);
#[derive(Debug, Default, Clone)]
pub struct Substitutions {
    types: Vec<(MetaVariable, Type)>,
    confinements: BTreeMap<u32, Confinement>,
}

impl Substitutions {
    pub fn substitution(&self, rhs: &MetaVariable) -> Option<&Type> {
        self.iter()
            .rev()
            .find_map(|(lhs, ty)| (lhs == rhs).then_some(ty))
    }

    fn compose(&self, rhs: &Self) -> Self {
        let mut out = Vec::new();

        for (param, ty) in rhs.iter() {
            out.push((param.clone(), ty.apply(self)));
        }

        for (param, ty) in self.iter() {
            out.push((param.clone(), ty.clone()));
        }

        let confinements = rhs
            .confinements
            .iter()
            .map(|(id, confinement)| (*id, confinement.apply(&self.confinements)))
            .chain(
                self.confinements
                    .iter()
                    .map(|(id, confinement)| (*id, confinement.clone())),
            )
            .collect();

        Substitutions {
            types: out,
            confinements,
        }
    }

    fn with_confinements(confinements: BTreeMap<u32, Confinement>) -> Self {
        Self {
            types: Vec::new(),
            confinements,
        }
    }

    fn remove(&mut self, param: &MetaVariable) {
        self.types.retain(|(tp, ..)| param != tp);
        if let Some(confinement) = param.kind().confinement() {
            for variable in confinement.variables() {
                self.confinements.remove(&variable);
            }
        }
    }
}

impl fmt::Display for Substitutions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut subs = self.types.iter();
        write!(f, "{{")?;

        if let Some((p, ty)) = subs.next() {
            write!(f, " {p} -> {ty}")?;
        }

        for (p, ty) in subs {
            write!(f, "; {p} -> {ty}")?;
        }

        write!(f, " }}")
    }
}

impl From<Vec<(MetaVariable, Type)>> for Substitutions {
    fn from(value: Vec<(MetaVariable, Type)>) -> Self {
        Self {
            types: value,
            confinements: BTreeMap::new(),
        }
    }
}

impl Deref for Substitutions {
    type Target = [(MetaVariable, Type)];

    fn deref(&self) -> &Self::Target {
        &self.types
    }
}

#[derive(Debug, Clone, Default)]
pub struct TermEnvironment {
    bound: Vec<TypeScheme>,
    free: HashMap<namer::QualifiedName, TypeScheme>,
}

impl TermEnvironment {
    pub fn lookup_free(&self, term: &namer::QualifiedName) -> Option<&TypeScheme> {
        self.free.get(term)
    }

    pub fn lookup(&self, term: &namer::Identifier) -> Option<&TypeScheme> {
        match term {
            namer::Identifier::Bound(index) => {
                (*index < self.bound.len()).then(|| &self.bound[*index])
            }
            namer::Identifier::Free(member) => self.free.get(member),
        }
    }

    pub fn free_variables(&self) -> HashSet<MetaVariable> {
        self.bound
            .iter()
            .flat_map(|ts| ts.free_variables())
            .chain(self.free.values().flat_map(|ts| ts.free_variables()))
            .collect()
    }

    pub fn free_confinement_variables(&self) -> BTreeSet<u32> {
        self.bound
            .iter()
            .flat_map(TypeScheme::free_confinement_variables)
            .chain(
                self.free
                    .values()
                    .flat_map(TypeScheme::free_confinement_variables),
            )
            .collect()
    }
}

impl phase::StructPattern<Named> {
    fn shape(&self) -> RecordShape {
        RecordShape(self.fields.iter().map(|(l, ..)| l.clone()).collect())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecordShape(Vec<parser::Identifier>);

impl RecordShape {
    pub fn fields(&self) -> &[parser::Identifier] {
        self.0.as_slice()
    }

    pub fn index_of(&self, field_name: &parser::Identifier) -> Option<usize> {
        self.0.iter().position(|f| f == field_name)
    }

    pub fn contains(&self, field_name: &parser::Identifier) -> bool {
        self.0.contains(field_name)
    }

    pub fn into_vec(self) -> Vec<parser::Identifier> {
        self.0
    }
}

impl fmt::Display for RecordShape {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self(image) = self;
        let mut image = image.iter();
        if let Some(id) = image.next() {
            write!(f, "[{id}")?;
        }

        for id in image {
            write!(f, ", {id}")?;
        }

        write!(f, "]")?;

        Ok(())
    }
}

#[derive(Debug, Clone, Default)]
struct RecordShapeIndex {
    shape_name: HashMap<RecordShape, Vec<namer::QualifiedName>>,
    field_names: HashMap<parser::Identifier, Vec<namer::QualifiedName>>,
}

impl RecordShapeIndex {
    fn insert(&mut self, record: RecordShape, name: namer::QualifiedName) {
        for field_name in record.fields() {
            self.field_names
                .entry(field_name.clone())
                .or_default()
                .push(name.clone());
        }
        self.shape_name.entry(record).or_default().push(name);
    }

    fn type_constructor_names_by_shape(
        &self,
        image: &RecordShape,
    ) -> impl Iterator<Item = &namer::QualifiedName> {
        self.shape_name.get(image).into_iter().flatten()
    }

    fn type_constructor_names_by_field(
        &self,
        field: &parser::Identifier,
    ) -> impl Iterator<Item = &namer::QualifiedName> {
        self.field_names.get(field).into_iter().flatten()
    }
}

#[derive(Debug, Clone, Default)]
struct CoproductIndex(HashMap<namer::QualifiedName, Vec<namer::QualifiedName>>);

impl CoproductIndex {
    fn insert(&mut self, constructor: namer::QualifiedName, coproduct: namer::QualifiedName) {
        self.0.entry(constructor).or_default().push(coproduct);
    }

    fn matching(
        &self,
        constructor: &namer::QualifiedName,
    ) -> impl Iterator<Item = &namer::QualifiedName> {
        self.0.get(constructor).into_iter().flatten()
    }
}

#[derive(Debug, Clone, Default)]
pub struct TypeEnvironment {
    bindings: HashMap<namer::QualifiedName, TypeConstructor>,
    // Is this the best datatype for this?
    record_shapes: RecordShapeIndex,
    coproduct_constructors: CoproductIndex,
}

impl TypeEnvironment {
    fn bind(&mut self, name: namer::QualifiedName, tc: TypeConstructor) {
        self.bindings.insert(name, tc);
    }

    pub fn lookup(&self, name: &namer::QualifiedName) -> Option<&TypeConstructor> {
        self.bindings.get(name)
    }

    pub fn lookup_mut(&mut self, name: &namer::QualifiedName) -> Option<&mut TypeConstructor> {
        self.bindings.get_mut(name)
    }

    fn normalize_alias(&self, ty: &Type) -> Result<Option<Type>, TypeError> {
        self.normalize_alias_on_path(ty, &mut Vec::new())
    }

    fn normalize_alias_on_path(
        &self,
        ty: &Type,
        path: &mut Vec<QualifiedName>,
    ) -> Result<Option<Type>, TypeError> {
        let mut head = ty;
        while let Type::Apply { constructor, .. } = head {
            head = constructor;
        }

        let Type::Constructor(name) = head else {
            return Ok(None);
        };
        let Some(constructor) = self.lookup(name) else {
            return Ok(None);
        };
        let TypeDefinition::Alias(_) = &constructor.definition().defining_symbol.definition else {
            return Ok(None);
        };
        let mut arguments = Vec::new();
        let mut application = ty;
        while let Type::Apply {
            constructor,
            argument,
            ..
        } = application
        {
            arguments.push(argument.as_ref());
            application = constructor;
        }
        arguments.reverse();
        if arguments.len() < constructor.arity() {
            return Ok(None);
        }
        if let Some(start) = path.iter().position(|candidate| candidate == name) {
            let mut cycle = path[start..].to_vec();
            cycle.push(name.clone());
            return Err(TypeError::CyclicTypeAlias { cycle });
        }

        let TypeConstructor::Elaborated(alias) = constructor else {
            return Err(TypeError::UnelaboratedConstructor(name.clone()));
        };
        path.push(name.clone());
        let parameter_count = alias.definition.defining_symbol.type_parameters().len();
        let substitutions = Substitutions::from(
            alias
                .definition
                .defining_symbol
                .type_parameters()
                .iter()
                .map(|parameter| alias.definition.instantiated_params[&parameter.name].clone())
                .zip(
                    arguments
                        .iter()
                        .take(parameter_count)
                        .map(|argument| (*argument).clone()),
                )
                .collect::<Vec<_>>(),
        );
        let expanded = arguments[parameter_count..].iter().fold(
            alias.structure.materialize_monotype().apply(&substitutions),
            |constructor, argument| Type::application(constructor, (*argument).clone()),
        );
        let result = self
            .normalize_alias_on_path(&expanded, path)
            .map(|normalized| Some(normalized.unwrap_or(expanded)));
        path.pop();
        result
    }

    fn query_record_type_constructor(&self, shape: &RecordShape) -> Vec<&TypeConstructor> {
        self.record_shapes
            .type_constructor_names_by_shape(shape)
            .flat_map(|name| self.lookup(name))
            .collect()
    }

    fn query_record_type_from_field(
        &self,
        field_name: &parser::Identifier,
    ) -> Vec<&TypeConstructor> {
        self.record_shapes
            .type_constructor_names_by_field(field_name)
            .flat_map(|name| self.lookup(name))
            .collect()
    }

    fn query_coproduct_type_constructors(
        &self,
        name: &QualifiedName,
    ) -> Typing<Vec<&TypeConstructor>> {
        Ok(self
            .coproduct_constructors
            .matching(name)
            .flat_map(|name| self.lookup(name))
            .collect())
    }

    fn apply(&self, subs: &Substitutions) -> Self {
        Self {
            bindings: self
                .bindings
                .iter()
                .map(|(id, tc)| (id.clone(), tc.apply(subs)))
                .collect(),
            record_shapes: self.record_shapes.clone(),
            coproduct_constructors: self.coproduct_constructors.clone(),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct TypingContext {
    types: TypeEnvironment,
    terms: TermEnvironment,
}

impl TypingContext {
    /// Clear the local (`Bound`) term stack. Used before binding a top-level
    /// symbol's self-reference (`#0`) during constraint discharge, so it does not
    /// resolve to a stale entry left by an earlier symbol.
    pub fn reset_self_reference(&mut self) {
        self.terms.bound.clear();
    }

    pub fn expand_type_constructor(
        &self,
        pi: ParseInfo,
        ty: &Type,
    ) -> Typing<Option<TypeStructure>> {
        let normalized = self
            .types
            .normalize_alias(ty)
            .map_err(|error| error.at(pi))?;
        if let Some(normalized) = normalized {
            return if matches!(normalized, Type::Constructor { .. } | Type::Apply { .. }) {
                self.reduce_applied_constructor(pi, &normalized, &mut vec![], &mut None)
                    .map(Some)
            } else {
                Ok(Some(TypeStructure::Monotype(normalized)))
            };
        }
        if let Type::Constructor { .. } | Type::Apply { .. } = ty {
            self.reduce_applied_constructor(pi, ty, &mut vec![], &mut None)
                .map(Some)
        } else {
            Ok(None)
        }
    }

    fn reduce_applied_constructor(
        &self,
        pi: ParseInfo,
        applied: &Type,
        arguments: &mut Vec<Type>,
        application_capture: &mut Option<Confinement>,
    ) -> Typing<TypeStructure> {
        match applied {
            Type::Constructor(name) => {
                let constructor = self
                    .types
                    .lookup(name)
                    .ok_or_else(|| TypeError::UndefinedType(name.clone()).at(pi))?
                    .instantiate(self)?;

                if constructor.arity() != arguments.len() {
                    Err(TypeError::WrongArity {
                        constructor: constructor.definition().name.clone(),
                        was: arguments.clone(),
                        expected: constructor.arity(),
                    }
                    .at(pi))?;
                }

                // Given (((f a) b) c), the recursion sees the outer
                // Apply node first.
                arguments.reverse();

                let definition = constructor.definition();
                let mut subs = Substitutions::from(
                    definition
                        .defining_symbol
                        .type_parameters()
                        .iter()
                        .map(|tv| {
                            definition
                                .instantiated_params
                                .get(&tv.name)
                                .unwrap_or_else(|| panic!("Unmapped type parameter: {tv}"))
                        })
                        .cloned()
                        .zip(arguments.drain(..))
                        .collect::<Vec<_>>(),
                );

                if let (Some(hidden), Some(actual)) =
                    (&definition.hidden_capture, application_capture.as_ref())
                {
                    let captures = hidden.unify(actual).ok_or_else(|| {
                        TypeError::ConfinementMismatch {
                            lhs: hidden.clone(),
                            rhs: actual.clone(),
                        }
                        .at(pi)
                    })?;
                    subs = subs.compose(&Substitutions::with_confinements(captures));
                }

                Ok(constructor.structure()?.apply(&subs))
            }

            Type::Apply {
                constructor,
                argument,
                capture,
            } => {
                arguments.push(*argument.clone());
                if let Some(capture) = capture {
                    *application_capture = Some(capture.clone());
                }
                self.reduce_applied_constructor(pi, constructor, arguments, application_capture)
            }

            _ => {
                tracing::trace!("fallback with {applied}");
                // The head isn't a reducible named constructor (e.g. a type
                // variable `f` in `f α`, or an otherwise-neutral head). Rebuild
                // the applied spine from the arguments we peeled off on the way
                // down — otherwise `f α` collapses to just `f`, dropping `α` and
                // mis-binding pattern variables at a truncated (mis-kinded) type.
                arguments.reverse();
                let ty = arguments.drain(..).fold(applied.clone(), Type::application);
                Ok(TypeStructure::Monotype(ty))
            }
        }
    }

    // Why isn't this fucker &mut self?
    pub fn apply(&self, subs: &Substitutions) -> Self {
        Self {
            types: self.types.apply(subs),
            terms: TermEnvironment {
                bound: Self::substitute_bound(&self.terms.bound, subs),
                free: Self::substitute_free(&self.terms.free, subs),
            },
        }
    }

    fn substitute_mut(&mut self, subst: &Substitutions) {
        let new_self = self.apply(subst);
        *self = new_self;
    }

    fn substitute_bound(terms: &[TypeScheme], subst: &Substitutions) -> Vec<TypeScheme> {
        terms.iter().map(|ty| ty.apply(subst)).collect()
    }

    fn substitute_free(
        terms: &HashMap<namer::QualifiedName, TypeScheme>,
        subs: &Substitutions,
    ) -> HashMap<namer::QualifiedName, TypeScheme> {
        terms
            .iter()
            .map(|(k, v)| (k.clone(), v.apply(subs)))
            .collect()
    }

    fn elaborate_type_constructors(&mut self) -> Typing<()> {
        let alt_ctx = self.clone();

        for constructor in self.types.bindings.values_mut() {
            // This means that the elaboration phase does not
            // see its own results
            constructor.elaborate(&alt_ctx)?;
        }

        for constructor in self.types.bindings.values() {
            if let TypeConstructor::Elaborated(constructor) = constructor {
                match &constructor.structure {
                    TypeStructure::PolyRecord(record_type) => self
                        .types
                        .record_shapes
                        .insert(record_type.shape(), constructor.definition.name.clone()),

                    TypeStructure::Monotype(Type::Coproduct(coproduct)) => {
                        for (constructor_name, _) in &coproduct.0 {
                            self.types.coproduct_constructors.insert(
                                constructor_name.clone(),
                                constructor.definition.name.clone(),
                            );
                        }
                    }

                    _ => (),
                }
            }
        }

        Ok(())
    }

    pub fn bind_type(&mut self, name: namer::QualifiedName, constructor: TypeConstructor) {
        self.types.bind(name, constructor);
    }

    pub fn bind_free_term(&mut self, name: namer::QualifiedName, scheme: TypeScheme) {
        self.terms.free.insert(name, scheme);
    }

    pub fn bind_term(&mut self, name: Identifier, scheme: TypeScheme) {
        match name {
            Identifier::Bound(..) => self.terms.bound.push(scheme),
            Identifier::Free(name) => self.bind_free_term(*name, scheme),
        }
    }

    pub fn bind_term_and_then<F, A>(
        &mut self,
        name: namer::Identifier,
        scheme: TypeScheme,
        block: F,
    ) -> A
    where
        F: FnOnce(&mut TypingContext) -> A,
    {
        match name {
            namer::Identifier::Bound(ix) => {
                if self.terms.bound.len() != ix {
                    panic!(
                        "bind_term_and_then: de Bruijn index missmatch; bound {ix}, len {}",
                        self.terms.bound.len()
                    );
                }
                self.terms.bound.push(scheme);
                let v = block(self);
                self.terms.bound.pop();
                v
            }

            namer::Identifier::Free(id) => {
                let previous = self.terms.free.insert(*id.clone(), scheme);
                let v = block(self);
                if let Some(previous) = previous {
                    self.terms.free.insert(*id, previous);
                } else {
                    self.terms.free.remove(&id);
                }
                v
            }
        }
    }

    #[instrument]
    fn check_expr(&mut self, expected_type: &Type, expr: &UntypedExpr) -> Typing {
        match expr {
            UntypedExpr::RecursiveLambda(pi, rec) => {
                self.check_recursive_lambda(*pi, expected_type, rec)
            }

            UntypedExpr::Lambda(pi, lambda) => self.check_lambda(*pi, expected_type, lambda),

            UntypedExpr::Tuple(pi, tuple) => self.check_tuple(*pi, expected_type, tuple),

            UntypedExpr::Record(pi, record) => self.check_record(*pi, expected_type, record),

            UntypedExpr::Inject(pi, construct) => {
                self.check_injection(*pi, expected_type, construct)
            }

            UntypedExpr::Deconstruct(pi, deconstruct) => {
                self.check_deconstruction(*pi, expected_type, deconstruct)
            }

            // Push the expected type through a `let`/sequence to its tail expression,
            // rather than inferring the whole chain and blaming the outer node. A
            // `let a = .. in let b = .. in body` carries the outermost `let`'s
            // parse-info, so inferring-then-unifying reports a body/expected mismatch at
            // the first `let`; checking the tail attributes it to the actual returning
            // expression instead.
            UntypedExpr::Let(pi, binding) => self.check_binding(*pi, expected_type, binding),

            UntypedExpr::Sequence(_pi, sequence) => self.check_sequence(expected_type, sequence),

            _ => self.check_expr_fallback_inferencing(expected_type, expr),
        }
    }

    fn check_expr_fallback_inferencing(
        &mut self,
        expected_type: &Type,
        expr: &UntypedExpr,
    ) -> Typing {
        // Extract this to check_inferencing_fallback or something
        let expr = self.infer_expr(expr)?;

        let lhs = expr
            .tree
            .type_info()
            .inferred_type
            .apply(&expr.substitutions);
        let rhs = expected_type.apply(&expr.substitutions);

        let s_unification = lhs
            .unified_with(&rhs, &self.types)
            .map_err(|e| e.at(expr.tree.annotation().parse_info))?;

        let substitutions = expr.substitutions.compose(&s_unification);
        let constraints = expr.constraints.apply(&substitutions);

        let expr = expr.tree.apply(&substitutions);
        Ok(Typed::computed(substitutions, constraints, expr))
    }

    #[instrument]
    fn check_injection(
        &mut self,
        pi: ParseInfo,
        expected_type: &Type,
        construct: &phase::Injection<Named>,
    ) -> Typing {
        let normalized_type = self.expand_type_constructor(pi, expected_type)?;

        if let Some(TypeStructure::Monotype(Type::Coproduct(coproduct))) = &normalized_type {
            let signature = coproduct.signature(&construct.constructor).ok_or_else(|| {
                TypeError::NoSuchCoproductConstructor(construct.constructor.clone()).at(pi)
            })?;
            let mut typed_args = Vec::with_capacity(signature.len());
            let mut substitutions = Substitutions::default();
            let mut constraints = ConstraintSet::default();

            for (expected, expr) in signature.iter().zip(&construct.arguments) {
                let typed_arg = self.check_expr(expected, expr)?;
                substitutions = substitutions.compose(&typed_arg.substitutions);
                constraints = constraints
                    .apply(&substitutions)
                    .union(typed_arg.constraints);
                typed_args.push(typed_arg.tree.into());
            }

            constraints = constraints.apply(&substitutions);
            let type_info = pi.with_inferred_type(expected_type.apply(&substitutions));
            Ok(Typed::computed(
                substitutions,
                constraints,
                Expr::Inject(
                    type_info,
                    Injection {
                        constructor: construct.constructor.clone(),
                        arguments: typed_args,
                    },
                ),
            ))
        } else {
            self.infer_inject(pi, construct)
        }
    }

    #[instrument]
    fn check_recursive_lambda(
        &mut self,
        pi: ParseInfo,
        expected_type: &Type,
        rec: &phase::SelfReferential<Named>,
    ) -> Typing {
        let normalized_type = self
            .expand_type_constructor(pi, expected_type)?
            .unwrap_or_else(|| TypeStructure::Monotype(expected_type.clone()));

        tracing::trace!("expected {expected_type} tree {:?}", rec.lambda);

        if let TypeStructure::Monotype(Type::Arrow {
            capture,
            domain,
            codomain,
        }) = &normalized_type
        {
            self.bind_term_and_then(
                rec.own_name.clone(),
                TypeScheme::from_constant(expected_type.clone()),
                |ctx| {
                    ctx.bind_term_and_then(
                        rec.lambda.parameter.clone(),
                        TypeScheme::from_constant(*domain.clone()),
                        |ctx| {
                            let typed_body = ctx.check_expr(codomain, &rec.lambda.body)?;

                            let body = typed_body.tree.apply(&typed_body.substitutions);
                            let actual_capture = ctx.lambda_capture_confinement(
                                &rec.lambda.parameter,
                                Some(&rec.own_name),
                                &body,
                            )?;
                            let expected_capture =
                                capture.apply(&typed_body.substitutions.confinements);
                            let capture_substitutions = expected_capture
                                .unify(&actual_capture.joined)
                                .map(Substitutions::with_confinements)
                                .ok_or_else(|| actual_capture.mismatch(expected_capture, pi))?;
                            let substitutions =
                                typed_body.substitutions.compose(&capture_substitutions);
                            let type_info =
                                pi.with_inferred_type(expected_type.apply(&substitutions));
                            Ok(Typed::computed(
                                substitutions.clone(),
                                typed_body.constraints.apply(&substitutions),
                                Expr::RecursiveLambda(
                                    type_info,
                                    SelfReferential {
                                        own_name: rec.own_name.clone(),
                                        lambda: Lambda {
                                            parameter: rec.lambda.parameter.clone(),
                                            body: body.apply(&substitutions).into(),
                                        },
                                    },
                                ),
                            ))
                        },
                    )
                },
            )
        } else {
            self.infer_recursive_lambda(pi, rec)
        }
    }

    #[instrument]
    fn check_lambda(
        &mut self,
        pi: ParseInfo,
        expected_type: &Type,
        lambda: &phase::Lambda<Named>,
    ) -> Typing {
        let normalized_type = self
            .expand_type_constructor(pi, expected_type)?
            .unwrap_or_else(|| TypeStructure::Monotype(expected_type.clone()));

        if let TypeStructure::Monotype(Type::Arrow {
            capture,
            domain,
            codomain,
        }) = &normalized_type
        {
            self.bind_term_and_then(
                lambda.parameter.clone(),
                TypeScheme::from_constant(*domain.clone()),
                |ctx| {
                    let body = ctx.check_expr(codomain, &lambda.body)?;

                    let typed_body = body.tree.apply(&body.substitutions);
                    let actual_capture =
                        ctx.lambda_capture_confinement(&lambda.parameter, None, &typed_body)?;
                    let expected_capture = capture.apply(&body.substitutions.confinements);
                    let capture_substitutions = expected_capture
                        .unify(&actual_capture.joined)
                        .map(Substitutions::with_confinements)
                        .ok_or_else(|| actual_capture.mismatch(expected_capture, pi))?;
                    let substitutions = body.substitutions.compose(&capture_substitutions);
                    ctx.substitute_mut(&substitutions);

                    let type_info = pi.with_inferred_type(expected_type.apply(&substitutions));
                    Ok(Typed::computed(
                        substitutions.clone(),
                        body.constraints.apply(&substitutions),
                        Expr::Lambda(
                            type_info,
                            Lambda {
                                parameter: lambda.parameter.clone(),
                                body: typed_body.apply(&substitutions).into(),
                            },
                        ),
                    ))
                },
            )
        } else {
            // In check mode a lambda must be given a function type. If the expected type is
            // not an arrow -- e.g. a signature ascribes `Text -> Float` to a two-parameter
            // lambda, so the trailing `λtemp. ...` is checked against the codomain `Float` --
            // the lambda cannot have that type: always an error. We still INFER the lambda's
            // own type, but solely to name it in the diagnostic (`Float -> File_Row` reads far
            // better than `?a -> ?b`); the inferred typing is otherwise discarded -- we never
            // proceed with it, since that would silently discard the ascription being checked.
            let (substitutions, _, typing_info, _) = self.infer_lambda(pi, lambda)?;
            Err(TypeError::UnificationImpossible {
                lhs: typing_info.inferred_type.apply(&substitutions),
                rhs: expected_type.apply(&substitutions),
            }
            .at(pi))
        }
    }

    #[instrument]
    fn check_record(
        &mut self,
        pi: ParseInfo,
        expected_type: &Type,
        record: &phase::Record<Named>,
    ) -> Typing {
        let normalized_type = self
            .expand_type_constructor(pi, expected_type)?
            .unwrap_or_else(|| TypeStructure::Monotype(expected_type.clone()));

        match normalized_type {
            TypeStructure::PolyRecord(record_type) => {
                let mut constraints = ConstraintSet::default();
                let mut subst = Substitutions::default();
                let mut typed_fields = Vec::with_capacity(record_type.len());
                let mut expected_types = Vec::with_capacity(record_type.len());

                if record.fields.len() != record_type.len() {
                    let lhs = record.fields.iter().map(|(l, _)| l).collect::<HashSet<_>>();
                    let rhs = record_type.fields().map(|(l, _)| l).collect::<HashSet<_>>();

                    let missing_bindings = rhs.difference(&lhs);
                    let extra_bindings = lhs.difference(&rhs);
                    Err(TypeError::BadRecordLiteral {
                        missing: missing_bindings.copied().cloned().collect(),
                        superfluous: extra_bindings.copied().cloned().collect(),
                    }
                    .at(pi))?;
                }

                for ((name, expr), (_, expected_scheme)) in
                    record.fields.iter().zip(record_type.fields())
                {
                    let expected_field_type = expected_scheme.instantiate();
                    let typed = self.check_expr(&expected_field_type.underlying, expr)?;
                    expected_types.push((name.clone(), expected_field_type.underlying));
                    subst = subst.compose(&typed.substitutions);

                    // A method whose signature carries its own constraint (e.g.
                    // `mconcat :: ∀α. Monoid α |- m α -> α`) is a rank-2 field: its
                    // value must be a polymorphic, dictionary-taking function, so
                    // the constraint is discharged *inside the field* and must not
                    // escape to the witness. Ordinary (unconstrained) fields bubble
                    // their inferred constraints as usual.
                    constraints = constraints.apply(&subst);
                    if expected_field_type.constraints.is_empty() {
                        constraints = constraints.union(typed.constraints.apply(&subst));
                    }
                    typed_fields.push((name.clone(), typed.tree.into()));
                }

                // This is wrong - it must be a spine
                //let type_info = pi
                //    .with_inferred_type(Type::Record(RecordType::from_fields(&expected_types)))
                //    .apply(&subst);

                let type_info = pi.with_inferred_type(expected_type.clone());

                Ok(Typed::computed(
                    subst,
                    constraints,
                    Expr::Record(
                        type_info,
                        Record {
                            fields: typed_fields,
                        },
                    ),
                ))
            }

            //TypeStructure::Monotype(Type::Variable(..)) => {
            //    todo!()
            //}
            _otherwise => Err(TypeError::Disappointed {
                expected: expected_type.clone(),
                from: namer::Expr::Record(pi, record.clone()),
            }
            .at(pi)),
        }
    }

    #[instrument]
    fn infer_record_update(
        &mut self,
        pi: ParseInfo,
        update: &ast::RecordUpdate<ParseInfo, namer::Identifier>,
    ) -> Typing {
        let typed_base = self.infer_expr(&update.base)?;
        let mut substitutions = typed_base.substitutions;
        let mut constraints = typed_base.constraints;
        let base_type = typed_base
            .tree
            .type_info()
            .inferred_type
            .apply(&substitutions);
        let normalized = self
            .expand_type_constructor(pi, &base_type)?
            .unwrap_or_else(|| TypeStructure::Monotype(base_type.clone()));
        let TypeStructure::PolyRecord(record_type) = normalized else {
            return Err(TypeError::Disappointed {
                expected: base_type,
                from: namer::Expr::RecordUpdate(pi, update.clone()),
            }
            .at(pi));
        };

        let mut seen: Vec<Vec<parser::Identifier>> = Vec::new();
        let mut typed_fields = Vec::with_capacity(update.fields.len());
        for field in &update.fields {
            let conflicts = seen.iter().any(|previous| {
                previous == &field.path
                    || previous.starts_with(&field.path)
                    || field.path.starts_with(previous)
            });
            if field.path.is_empty() || conflicts {
                return Err(TypeError::BadRecordLiteral {
                    missing: Vec::new(),
                    superfluous: field.path.last().cloned().into_iter().collect(),
                }
                .at(pi));
            }
            seen.push(field.path.clone());

            let mut current = base_type.clone();
            let mut indices = Vec::with_capacity(field.path.len());
            let mut arities = Vec::with_capacity(field.path.len());
            for name in &field.path {
                let structure = self
                    .expand_type_constructor(pi, &current.apply(&substitutions))?
                    .unwrap_or_else(|| TypeStructure::Monotype(current.apply(&substitutions)));
                let TypeStructure::PolyRecord(record) = structure else {
                    return Err(TypeError::BadRecordLiteral {
                        missing: Vec::new(),
                        superfluous: vec![name.clone()],
                    }
                    .at(pi));
                };
                let Some((index, scheme)) = record.field_info(name) else {
                    return Err(TypeError::BadRecordLiteral {
                        missing: Vec::new(),
                        superfluous: vec![name.clone()],
                    }
                    .at(pi));
                };
                indices.push(index);
                arities.push(record.len());
                current = scheme.instantiate().underlying;
            }

            let typed = self.check_expr(&current.apply(&substitutions), &field.value)?;
            substitutions = substitutions.compose(&typed.substitutions);
            constraints = constraints
                .apply(&substitutions)
                .union(typed.constraints.apply(&substitutions));
            typed_fields.push(ast::RecordUpdateField {
                path: field.path.clone(),
                indices,
                arities,
                value: typed.tree.into(),
            });
        }

        let result_type = base_type.apply(&substitutions);
        Ok(Typed::computed(
            substitutions,
            constraints,
            Expr::RecordUpdate(
                pi.with_inferred_type(result_type),
                ast::RecordUpdate {
                    base: typed_base.tree.into(),
                    fields: typed_fields,
                    field_order: record_type.fields().map(|(name, _)| name.clone()).collect(),
                },
            ),
        ))
    }

    #[instrument]
    fn check_tuple(
        &mut self,
        pi: ParseInfo,
        expected_type: &Type,
        tuple: &phase::Tuple<Named>,
    ) -> Typing {
        let mut constraints = ConstraintSet::default();
        let normalized_type = self
            .expand_type_constructor(pi, expected_type)?
            .unwrap_or_else(|| TypeStructure::Monotype(expected_type.clone()));

        match normalized_type {
            TypeStructure::Monotype(Type::Tuple(TupleType(elements))) => {
                let mut typed_elements = Vec::with_capacity(elements.len());
                let mut substitutions = Substitutions::default();

                for (expr, expected) in tuple.elements.iter().zip(elements) {
                    let typed_element = self.check_expr(&expected, expr)?;
                    substitutions = substitutions.compose(&typed_element.substitutions);
                    typed_elements.push(typed_element.tree.into());
                    constraints = constraints
                        .apply(&substitutions)
                        .union(typed_element.constraints.apply(&substitutions))
                }

                let type_info = pi.with_inferred_type(expected_type.apply(&substitutions));
                Ok(Typed::computed(
                    substitutions,
                    constraints,
                    Expr::Tuple(
                        type_info,
                        Tuple {
                            elements: typed_elements,
                        },
                    ),
                ))
            }

            TypeStructure::Monotype(ty @ Type::Variable(..)) => {
                let inferred = self.infer_expr(&namer::Expr::Tuple(pi, tuple.clone()))?;
                let unification = inferred
                    .tree
                    .type_info()
                    .inferred_type
                    .unified_with(&ty, &self.types)
                    .map_err(|e| e.at(pi))?;
                Ok(inferred.apply(&unification))
            }

            _otherwise => Err(TypeError::Disappointed {
                expected: expected_type.clone(),
                from: namer::Expr::Tuple(pi, tuple.clone()),
            }
            .at(pi)),
        }
    }

    #[instrument]
    pub fn infer_expr(&mut self, expr: &UntypedExpr) -> Typing {
        match expr {
            UntypedExpr::Variable(pi, name) => {
                let inferred_type = self
                    .terms
                    .lookup(name)
                    .ok_or_else(|| {
                        TypeError::UndefinedName {
                            parse_info: *pi,
                            name: name.clone(),
                        }
                        .at(*pi)
                    })?
                    .instantiate();

                Ok(Typed::computed(
                    Substitutions::default(),
                    inferred_type.constraints,
                    Expr::Variable(
                        (*pi).with_inferred_type(inferred_type.underlying),
                        name.clone(),
                    ),
                ))
            }

            UntypedExpr::InvokeBridge(pi, bridge) => {
                let inferred_type = bridge.intrinsic.type_scheme().instantiate();

                Ok(Typed::computed(
                    Substitutions::default(),
                    inferred_type.constraints,
                    Expr::InvokeBridge(
                        (*pi).with_inferred_type(inferred_type.underlying),
                        bridge.clone(),
                    ),
                ))
            }

            UntypedExpr::Constant(pi, literal) => Ok(Typed::constant(Expr::Constant(
                (*pi).with_inferred_type(literal.synthesize_type()),
                literal.clone(),
            ))),

            UntypedExpr::RecursiveLambda(pi, rec_lambda) => {
                self.infer_recursive_lambda(*pi, rec_lambda)
            }

            UntypedExpr::Lambda(pi, lambda) => {
                // todo: infer_lambda has a stupid signature
                let (substitutions, constraints, typing_info, lambda) =
                    self.infer_lambda(*pi, lambda)?;

                Ok(Typed::computed(
                    substitutions,
                    constraints,
                    Expr::Lambda(typing_info, lambda),
                ))
            }

            UntypedExpr::Apply(pi, ast::Apply { function, argument }) => {
                if let UntypedExpr::Apply(_, inner) = &**function
                    && let UntypedExpr::Variable(_, Identifier::Free(name)) = &*inner.function
                    && matches!(name.member().as_str(), "bind" | "fmap")
                {
                    self.infer_reverse_binary_apply(*pi, &inner.function, &inner.argument, argument)
                } else {
                    self.infer_apply(*pi, function, argument)
                }
            }

            UntypedExpr::Let(pi, binding) => self.infer_binding(*pi, binding),

            UntypedExpr::Record(pi, record) => self.infer_record(*pi, record),

            UntypedExpr::RecordUpdate(pi, update) => self.infer_record_update(*pi, update),

            UntypedExpr::Tuple(pi, tuple) => self.infer_tuple(*pi, tuple),

            UntypedExpr::Inject(pi, constructor) => self.infer_inject(*pi, constructor),

            UntypedExpr::Array(pi, array) => self.infer_array(*pi, array),

            UntypedExpr::Project(pi, projection) => self.infer_projection(*pi, projection),

            UntypedExpr::Sequence(_pi, sequence) => self.infer_sequence(sequence),

            UntypedExpr::Deconstruct(pi, deconstruct) => {
                self.infer_deconstruction(*pi, deconstruct)
            }

            UntypedExpr::If(pi, if_then_else) => self.infer_if_then_else(*pi, if_then_else),

            UntypedExpr::Interpolate(pi, ast::Interpolate(segments)) => {
                self.infer_interpolation(*pi, segments)
            }

            UntypedExpr::Ascription(pi, ascription) => self.infer_ascription(*pi, ascription),

            UntypedExpr::MakeClosure(..) => panic!("Does not type"),
        }
    }

    #[instrument]
    fn infer_ascription(
        &mut self,
        pi: ParseInfo,
        ascription: &phase::TypeAscription<Named>,
    ) -> Typing {
        // What is a good way to deal with a "current set" of alpha type parameters?
        let ascribed_scheme = ascription
            .type_signature
            .type_scheme(&HashMap::default(), self)?;

        tracing::trace!("scheme {ascribed_scheme}");

        let ascribed_type = ascribed_scheme.instantiate();
        let ascribed_tree =
            self.check_expr(&ascribed_type.underlying, &ascription.ascribed_tree)?;

        let subst = ascribed_type
            .underlying
            .unified_with(&ascribed_tree.tree.type_info().inferred_type, &self.types)
            .map_err(|e| e.at(pi))?;

        let tree = ascribed_tree.apply(&subst).tree;

        Ok(Typed::computed(
            ascribed_tree.substitutions.compose(&subst),
            ascribed_tree.constraints.apply(&subst),
            Expr::Ascription(
                tree.type_info().clone(),
                TypeAscription {
                    ascribed_tree: tree.into(),
                    type_signature: ascription.type_signature.map_annotation(&|pi| TypeInfo {
                        parse_info: *pi,
                        inferred_type: ascribed_type.underlying.clone(),
                        enclosing_term: None,
                    }),
                },
            ),
        ))
    }

    #[instrument]
    fn infer_interpolation(&mut self, pi: ParseInfo, segments: &[phase::Segment<Named>]) -> Typing {
        let mut segs = vec![];
        let mut substitutions = Substitutions::default();
        let mut constraints = ConstraintSet::default();

        for segment in segments {
            match segment {
                Segment::Literal(pi, literal) => segs.push(Segment::Literal(
                    (*pi).with_inferred_type(literal.synthesize_type()),
                    literal.clone(),
                )),
                Segment::Expression(expr) => {
                    let typed_expr = self.infer_expr(expr)?;
                    segs.push(ast::Segment::Expression(typed_expr.tree.into()));
                    substitutions = substitutions.compose(&typed_expr.substitutions);
                    constraints = constraints
                        .apply(&substitutions)
                        .union(typed_expr.constraints.apply(&substitutions))
                }
            }
        }

        let segs = segs
            .into_iter()
            .map(|s| match s {
                Segment::Expression(expr) => Segment::Expression(expr.apply(&substitutions)),
                lit => lit,
            })
            .collect();

        constraints = constraints.apply(&substitutions);
        Ok(Typed::computed(
            substitutions,
            constraints,
            Expr::Interpolate(
                pi.with_inferred_type(stdlib_text_type()),
                ast::Interpolate(segs),
            ),
        ))
    }

    #[instrument]
    fn check_deconstruction(
        &mut self,
        pi: ParseInfo,
        expected_type: &Type,
        deconstruct: &phase::Deconstruct<Named>,
    ) -> Typing {
        let Typed {
            mut substitutions,
            tree: scrutinee,
            mut constraints,
        } = self.infer_expr(&deconstruct.scrutinee)?;
        let scrutinee_type = &scrutinee.type_info().inferred_type;
        let mut typed_match_clauses = Vec::with_capacity(deconstruct.match_clauses.len());
        let mut space = MatchSpace::default();

        for clause in &deconstruct.match_clauses {
            let mut clause_ctx = self.clone();
            let mut bindings = Vec::default();
            let (s_pattern, pattern) = clause_ctx.check_pattern(
                &clause.pattern,
                &mut bindings,
                &scrutinee_type.apply(&substitutions),
            )?;
            clause_ctx.substitute_mut(&s_pattern);
            for (binding, ty) in bindings {
                clause_ctx.bind_term(binding, TypeScheme::from_constant(ty));
            }
            let consequent = clause_ctx.check_expr(expected_type, &clause.consequent)?;
            substitutions = substitutions
                .compose(&consequent.substitutions)
                .compose(&s_pattern);
            constraints = constraints
                .apply(&substitutions)
                .union(consequent.apply(&substitutions).constraints);

            if !space.join(&pattern) {
                let parse_info = pattern.annotation().parse_info;
                Err(TypeError::UselessMatchClause {
                    clause: MatchClause {
                        pattern,
                        consequent: consequent.tree.into(),
                    },
                }
                .at(parse_info))?;
            } else {
                typed_match_clauses.push(MatchClause {
                    pattern,
                    consequent: consequent.tree.into(),
                });
            }
        }

        let missing = space.uncovered(pi, &scrutinee_type.apply(&substitutions), self)?;
        if !missing.is_empty() {
            Err(TypeError::MatchNotExhaustive { missing }.at(pi))
        } else {
            let type_info = pi.with_inferred_type(expected_type.apply(&substitutions));
            Ok(Typed::computed(
                substitutions,
                constraints,
                Expr::Deconstruct(
                    type_info,
                    Deconstruct {
                        scrutinee: scrutinee.into(),
                        match_clauses: typed_match_clauses,
                    },
                ),
            ))
        }
    }

    #[instrument]
    fn infer_deconstruction(
        &mut self,
        pi: ParseInfo,
        deconstruct: &phase::Deconstruct<Named>,
    ) -> Typing {
        let Typed {
            mut substitutions,
            tree: mut scrutinee,
            mut constraints,
        } = self.infer_expr(&deconstruct.scrutinee)?;

        let mut clauses = Vec::with_capacity(deconstruct.match_clauses.len());
        let mut match_clauses = deconstruct.match_clauses.iter();

        let Some(clause) = match_clauses.next() else {
            Err(TypeError::InternalAssertion(
                "parser promises at least one clause".to_owned(),
            ))
            .map_err(|e| e.at(pi))?
        };

        let mut first_clause = self.apply(&substitutions).infer_match_clause(
            &mut substitutions,
            &mut constraints,
            clause,
            &scrutinee.type_info().inferred_type,
        )?;
        scrutinee = scrutinee.apply(&substitutions);

        while let Some(clause) = match_clauses.next() {
            let mut clause_ctx = self.apply(&substitutions);
            let clause = clause_ctx.infer_match_clause(
                &mut substitutions,
                &mut constraints,
                clause,
                &scrutinee.type_info().inferred_type,
            )?;
            let lhs = first_clause
                .consequent
                .type_info()
                .inferred_type
                .apply(&substitutions);
            let rhs = clause
                .consequent
                .type_info()
                .inferred_type
                .apply(&substitutions);
            let subst = lhs.unified_with(&rhs, &self.types).map_err(|e| e.at(pi))?;
            substitutions = substitutions.compose(&subst);
            constraints = constraints.apply(&substitutions);
            scrutinee = scrutinee.apply(&substitutions);
            first_clause.consequent = first_clause.consequent.apply(&substitutions);

            clauses.push(clause);
        }

        let type_info =
            pi.with_inferred_type(first_clause.consequent.type_info().inferred_type.clone());

        clauses.insert(0, first_clause);

        let mut match_space = MatchSpace::default();
        for clause in &clauses {
            if !match_space.join(&clause.pattern) {
                Err(TypeError::UselessMatchClause {
                    clause: clause.clone(),
                }
                .at(clause.pattern.annotation().parse_info))?;
            }
        }

        let missing = match_space.uncovered(pi, &scrutinee.type_info().inferred_type, self)?;
        if !missing.is_empty() {
            Err(TypeError::MatchNotExhaustive { missing }.at(pi))
        } else {
            Ok(Typed::computed(
                substitutions,
                constraints,
                Expr::Deconstruct(
                    type_info,
                    Deconstruct {
                        scrutinee: scrutinee.into(),
                        match_clauses: clauses,
                    },
                ),
            ))
        }
    }

    fn infer_match_clause(
        &mut self,
        substitutions: &mut Substitutions,
        constraints: &mut ConstraintSet,
        clause: &phase::MatchClause<Named>,
        scrutinee: &Type,
    ) -> Typing<phase::MatchClause<Types>> {
        let mut bindings = Vec::default();
        let (p_subst, pattern) = self.check_pattern(&clause.pattern, &mut bindings, &scrutinee)?;
        //self.substitute_mut(&p_subst);

        for (binding, ty) in bindings {
            self.bind_term(binding, TypeScheme::from_constant(ty));
        }
        let consequent = self.infer_expr(&clause.consequent)?;

        *substitutions = substitutions
            .compose(&p_subst)
            .compose(&consequent.substitutions);
        let consequent = consequent.apply(&substitutions);
        *constraints = constraints
            .apply(&substitutions)
            .union(consequent.constraints);

        Ok(MatchClause {
            pattern,
            consequent: consequent.tree.into(),
        })
    }

    fn resolve_unique_record_type_constructor(
        &self,
        pi: ParseInfo,
        shape: &RecordShape,
    ) -> Typing<&TypeConstructor> {
        let candidates = self.types.query_record_type_constructor(shape);

        if candidates.len() != 1 {
            if candidates.is_empty() {
                Err(TypeError::NoRecordTypWithShape(shape.clone()).at(pi))?
            } else {
                Err(TypeError::AmbiguousRecord {
                    shape: shape.clone(),
                    candidates: candidates
                        .iter()
                        .map(|c| c.definition().name.clone())
                        .collect(),
                }
                .at(pi))?
            }
        } else {
            Ok(candidates.first().unwrap())
        }
    }

    #[instrument]
    fn infer_pattern_scrutinee(
        &mut self,
        pattern: &phase::Pattern<Named>,
        bindings: &mut Vec<(namer::Identifier, Type)>,
        scrutinee: &MetaVariable,
    ) -> Typing<(Substitutions, phase::Pattern<Types>)> {
        match pattern {
            Pattern::Coproduct(pi, coproduct) => {
                // This could be lifted into the pattern match
                let constructor = coproduct
                    .constructor
                    .try_as_free()
                    .expect("expected Free identifier");

                let inferred = self
                    .resolve_unique_coproduct_type_constructor(*pi, constructor)?
                    .instantiate(self)?
                    .make_spine();

                let substitutions =
                    Substitutions::from(vec![(scrutinee.clone(), inferred.clone())]);

                self.substitute_mut(&substitutions);

                let (s_pattern, pattern) = self.check_pattern(pattern, bindings, &inferred)?;
                Ok((s_pattern.compose(&substitutions), pattern))
            }

            Pattern::Struct(pi, record) => {
                let shape = record.shape();
                let inferred = self
                    .resolve_unique_record_type_constructor(*pi, &shape)?
                    .instantiate(self)?
                    .make_spine();

                let subst = Substitutions::from(vec![(scrutinee.clone(), inferred.clone())]);

                self.substitute_mut(&subst);

                let (s_pattern, pattern) = self.check_pattern(pattern, bindings, &inferred)?;
                Ok((s_pattern.compose(&subst), pattern))
            }

            Pattern::Tuple(pi, tuple) => {
                let tuple = Type::Tuple(TupleType(
                    tuple.elements.iter().map(|_| Type::fresh()).collect(),
                ));
                let unification = tuple
                    .unified_with(&Type::Variable(scrutinee.clone()), &self.types)
                    .map_err(|e| e.at(*pi))?;

                self.substitute_mut(&unification);

                let (s_pattern, pattern) = self.check_pattern(pattern, bindings, &tuple)?;

                Ok((s_pattern.compose(&unification), pattern))
            }

            Pattern::Literally(pi, pattern) => {
                let scrutinee = Type::Variable(scrutinee.clone());
                let inferred = pattern.synthesize_type();
                let s_pattern = inferred
                    .unified_with(&scrutinee, &self.types)
                    .map_err(|e| e.at(*pi))?;

                Ok((
                    s_pattern,
                    Pattern::Literally((*pi).with_inferred_type(inferred), pattern.clone()),
                ))
            }

            Pattern::Bind(pi, pattern) => {
                let scrutinee = Type::Variable(scrutinee.clone());
                bindings.push((pattern.clone(), scrutinee.clone()));
                Ok((
                    Substitutions::default(),
                    Pattern::Bind((*pi).with_inferred_type(scrutinee), pattern.clone()),
                ))
            }
        }
    }

    #[instrument]
    fn check_pattern(
        &mut self,
        pattern: &phase::Pattern<Named>,
        bindings: &mut Vec<(namer::Identifier, Type)>,
        scrutinee: &Type,
    ) -> Typing<(Substitutions, phase::Pattern<Types>)> {
        let pi = *pattern.annotation();
        let normalized_scrutinee = self
            .expand_type_constructor(pi, scrutinee)?
            .unwrap_or_else(|| TypeStructure::Monotype(scrutinee.clone()));

        match (pattern, &normalized_scrutinee) {
            (_, TypeStructure::Monotype(Type::Variable(p))) => {
                self.infer_pattern_scrutinee(pattern, bindings, p)
            }

            (
                Pattern::Coproduct(pi, pattern),
                TypeStructure::Monotype(Type::Coproduct(coproduct)),
            ) => {
                let namer::Identifier::Free(constructor) = &pattern.constructor else {
                    // After naming, a constructor-pattern head is always a free qualified
                    // name; a bound one is a compiler invariant break, not user error.
                    return Err(TypeError::InternalAssertion(
                        "constructor pattern head is not a free name".to_owned(),
                    )
                    .at(*pi));
                };
                // The constructor must belong to the coproduct being deconstructed, with a
                // matching argument count. Both failures used to panic ("Bad coproduct
                // deconstruction") with no location; report them as located type errors so
                // a bad `deconstruct ... into C ...` names `C` and points at the pattern.
                let Some(signature) = coproduct.signature(constructor) else {
                    return Err(
                        TypeError::NoSuchCoproductConstructor((**constructor).clone()).at(*pi),
                    );
                };
                if pattern.arguments.len() != signature.len() {
                    return Err(TypeError::ConstructorPatternArity {
                        constructor: (**constructor).clone(),
                        expected: signature.len(),
                        got: pattern.arguments.len(),
                    }
                    .at(*pi));
                }

                let mut arguments = Vec::with_capacity(signature.len());
                let mut substitutions = Substitutions::default();

                for (scrutinee, pattern) in signature.iter().zip(&pattern.arguments) {
                    let (subs, argument) =
                        self.check_pattern(pattern, bindings, &scrutinee.apply(&substitutions))?;
                    self.substitute_mut(&subs);
                    arguments.push(argument.apply(&substitutions));
                    substitutions = substitutions.compose(&subs);
                }

                Ok((
                    substitutions,
                    Pattern::Coproduct(
                        (*pi).with_inferred_type(scrutinee.clone()),
                        ConstructorPattern {
                            constructor: namer::Identifier::Free(constructor.clone()),
                            arguments,
                        },
                    ),
                ))
            }

            (Pattern::Tuple(pi, tuple), _) => {
                // Synthesize a tuple type of the pattern's arity and unify it with the scrutinee,
                // exactly as `infer_pattern_scrutinee` does for a variable scrutinee. A shape or
                // arity mismatch -- e.g. a nested `((a, b), c)` against a flat `(Int, Int, Int)` --
                // then surfaces as an ordinary `cannot unify` error rather than the catch-all
                // panic below. On success the fresh element types carry the scrutinee's elements.
                let element_types: Vec<Type> =
                    tuple.elements.iter().map(|_| Type::fresh()).collect();
                let unification = Type::Tuple(TupleType(element_types.clone()))
                    .unified_with(scrutinee, &self.types)
                    .map_err(|e| e.at(*pi))?;
                self.substitute_mut(&unification);

                let mut elements = Vec::with_capacity(tuple.elements.len());
                let mut substitutions = unification;
                for (pattern, element_type) in tuple.elements.iter().zip(&element_types) {
                    let (subst, element) =
                        self.check_pattern(pattern, bindings, &element_type.apply(&substitutions))?;
                    elements.push(element);
                    substitutions = substitutions.compose(&subst);
                }

                Ok((
                    substitutions,
                    Pattern::Tuple(
                        (*pi).with_inferred_type(scrutinee.clone()),
                        TuplePattern { elements },
                    ),
                ))
            }

            (Pattern::Struct(pi, pattern), TypeStructure::PolyRecord(record))
                if pattern.fields.len() == record.len() =>
            {
                let mut arguments = Vec::with_capacity(record.len());
                let mut substitutions = Substitutions::default();

                for ((pattern_field, pattern), (scrutinee_field, scrutinee)) in
                    (pattern.fields).iter().zip(record.fields())
                {
                    if pattern_field != scrutinee_field {
                        Err(TypeError::BadRecordPatternField {
                            record_type: scrutinee.instantiate().underlying,
                            field: pattern_field.clone(),
                        }
                        .at(*pi))?;
                    }

                    let (subst, pattern) =
                        self.check_pattern(pattern, bindings, &scrutinee.instantiate().underlying)?;
                    arguments.push((pattern_field.clone(), pattern));
                    substitutions = substitutions.compose(&subst);
                }

                Ok((
                    substitutions,
                    Pattern::Struct(
                        (*pi).with_inferred_type(scrutinee.clone()),
                        StructPattern { fields: arguments },
                    ),
                ))
            }

            // Check pattern at ty
            (Pattern::Literally(pi, pattern), ..) => {
                let inferred = pattern.synthesize_type();
                let subs = inferred
                    .unified_with(scrutinee, &self.types)
                    .map_err(|e| e.at(*pi))?;

                Ok((
                    subs,
                    Pattern::Literally((*pi).with_inferred_type(inferred), pattern.clone()),
                ))
            }

            (Pattern::Bind(pi, pattern), ..) => {
                bindings.push((pattern.clone(), scrutinee.clone()));
                Ok((
                    Substitutions::default(),
                    Pattern::Bind((*pi).with_inferred_type(scrutinee.clone()), pattern.clone()),
                ))
            }

            (pattern, _) => Err(TypeError::PatternTypeMismatch {
                pattern: pattern.to_string(),
                scrutinee: normalized_scrutinee,
            }
            .at(pi)),
        }
    }

    fn resolve_unique_coproduct_type_constructor(
        &self,
        pi: ParseInfo,
        name: &QualifiedName,
    ) -> Typing<&TypeConstructor> {
        let candidates = self.types.query_coproduct_type_constructors(&name)?;

        if candidates.len() != 1 {
            let constructor = name.clone();
            if candidates.is_empty() {
                Err(TypeError::NoSuchCoproductConstructor(constructor).at(pi))?
            } else {
                Err(TypeError::AmbiguousCoproduct {
                    constructor,
                    candidates: candidates
                        .iter()
                        .map(|c| c.definition().name.clone())
                        .collect(),
                }
                .at(pi))?
            }
        } else {
            Ok(candidates.first().unwrap())
        }
    }

    #[instrument]
    fn infer_inject(&mut self, pi: ParseInfo, construct: &phase::Injection<Named>) -> Typing {
        let (substitutions, constraints, typed_arguments, argument_types) =
            self.infer_several(&construct.arguments)?;

        let type_constructor = self
            .resolve_unique_coproduct_type_constructor(pi, &construct.constructor)?
            .instantiate(self)?;

        let subst = if let TypeStructure::Monotype(Type::Coproduct(coproduct)) =
            type_constructor.structure()?
        {
            let signature = coproduct.signature(&construct.constructor).ok_or_else(|| {
                TypeError::NoSuchCoproductConstructor(construct.constructor.clone()).at(pi)
            })?;
            Type::Tuple(TupleType::from_signature(signature))
                .unified_with(
                    &Type::Tuple(TupleType::from_signature(&argument_types)),
                    &self.types,
                )
                .map_err(|e| e.at(pi))?
        } else {
            Err(TypeError::InternalAssertion("expected a coproduct".to_owned()).at(pi))?
        };

        let constraints = constraints.apply(&substitutions);

        Ok(Typed::computed(
            substitutions,
            constraints,
            Expr::Inject(
                pi.with_inferred_type(type_constructor.make_spine().apply(&subst)),
                Injection {
                    constructor: construct.constructor.clone(),
                    arguments: typed_arguments,
                },
            ),
        ))
    }

    #[instrument]
    fn infer_array(&mut self, pi: ParseInfo, array: &phase::Array<Named>) -> Typing {
        if let Some(first_element) = array.elements.first() {
            let mut elements = Vec::with_capacity(array.elements.len());
            let Typed {
                mut substitutions,
                mut constraints,
                tree,
            } = self.infer_expr(&first_element)?;

            let mut array_element_type = tree.type_info().inferred_type.clone();
            elements.push(tree.into());

            for element in &array.elements[1..] {
                let element = self.infer_expr(&element)?;
                let unifier = array_element_type
                    .unified_with(&element.tree.type_info().inferred_type, &self.types)
                    .map_err(|e| e.at(pi))?;

                substitutions = substitutions
                    .compose(&unifier)
                    .compose(&element.substitutions);
                constraints = constraints.union(element.constraints.apply(&substitutions));

                array_element_type = array_element_type.apply(&substitutions);
                elements.push(element.tree.apply(&substitutions).into());
            }

            Ok(Typed::computed(
                substitutions,
                constraints,
                Expr::Array(
                    pi.with_inferred_type(
                        //Type::Array(array_element_type.into()),
                        Type::application(
                            Type::Constructor(QualifiedName::builtin("Array")),
                            array_element_type,
                        ),
                    ),
                    Array { elements },
                ),
            ))
        } else {
            Ok(Typed::constant(Expr::Array(
                pi.with_inferred_type(Type::Array(Type::fresh().into())),
                Array { elements: vec![] },
            )))
        }
    }

    #[instrument]
    fn infer_record(&mut self, pi: ParseInfo, record: &phase::Record<Named>) -> Typing {
        let mut substitutions = Substitutions::default();
        let mut fields = Vec::with_capacity(record.fields.len());
        let mut constraints = ConstraintSet::default();

        for (label, initializer) in &record.fields {
            let typed_field = self.infer_expr(initializer)?;
            fields.push((label, typed_field.tree));
            substitutions = substitutions.compose(&typed_field.substitutions);
            constraints = constraints
                .apply(&substitutions)
                .union(typed_field.constraints.apply(&substitutions));
        }

        let fields = fields
            .iter()
            .map(|(label, e)| ((*label).clone(), e.apply(&substitutions).into()))
            .collect::<Vec<_>>();

        let record_type = RecordType::from_fields(
            &fields
                .iter()
                .map(
                    |(label, e): &(parser::Identifier, Tree<TypeInfo, namer::Identifier>)| {
                        (label.clone(), e.type_info().inferred_type.clone())
                    },
                )
                .collect::<Vec<_>>(),
        );

        let type_constructor = self
            .resolve_unique_record_type_constructor(pi, &record_type.shape())?
            .instantiate(self)?;

        let subst = type_constructor
            .structure()?
            .materialize_monotype()
            .unified_with(&Type::Record(record_type), &self.types)
            .map_err(|e| e.at(pi))?;

        let substitutions = substitutions.compose(&subst);
        let constraints = constraints.apply(&substitutions);
        let type_info = pi.with_inferred_type(type_constructor.make_spine().apply(&substitutions));
        Ok(Typed::computed(
            substitutions,
            constraints,
            Expr::Record(type_info, Record { fields }),
        ))
    }

    #[instrument]
    fn infer_projection(&mut self, pi: ParseInfo, projection: &phase::Projection<Named>) -> Typing {
        let Typed {
            substitutions,
            tree: base,
            constraints,
        } = self.infer_expr(&projection.base)?;
        let base_type = &base.type_info().inferred_type;

        // This is where the elaboration of the polyrecord disappears
        let expanded_base_type = self
            .expand_type_constructor(pi, base_type)?
            .unwrap_or_else(|| TypeStructure::Monotype(base_type.clone()));

        tracing::trace!("base {base_type} expanded {expanded_base_type}");

        for (k, v) in &self.types.bindings {
            tracing::trace!("{k} is {v}");
        }

        match &projection.select {
            ProductElement::Name(field_name) => match expanded_base_type {
                TypeStructure::PolyRecord(record) => {
                    tracing::trace!("{record:?}");

                    if let Some((field_index, (_, field_scheme))) = record
                        .0
                        .iter()
                        .enumerate()
                        .find(|(_, (label, _))| label == field_name)
                    {
                        let field_type = field_scheme.instantiate();

                        tracing::trace!("{field_name} :: {field_type}");

                        Ok(Typed::computed(
                            substitutions,
                            constraints.union(field_type.constraints),
                            Expr::Project(
                                pi.with_inferred_type(field_type.underlying),
                                Projection {
                                    base: base.into(),
                                    select: ProductElement::Ordinal(field_index),
                                },
                            ),
                        ))
                    } else {
                        Err(TypeError::BadProjection {
                            projection: projection.clone(),
                            inferred_base_type: base_type.clone(),
                        }
                        .at(pi))
                    }
                }

                TypeStructure::Monotype(base_type @ Type::Variable(..)) => {
                    let candidates = self.types.query_record_type_from_field(field_name);
                    if candidates.len() == 1 {
                        let base_type_constructor = candidates[0].instantiate(self)?;
                        let structure = base_type_constructor.structure()?;
                        if let TypeStructure::PolyRecord(record_type) = structure
                            && let Some((field_index, field_scheme)) =
                                record_type.field_info(field_name)
                        {
                            let unification = base_type
                                .unified_with(&base_type_constructor.make_spine(), &self.types)
                                .map_err(|e| e.at(pi))?;
                            let field_type = field_scheme.instantiate();

                            let base = base.apply(&unification);
                            Ok(Typed::computed(
                                unification,
                                constraints.union(field_type.constraints),
                                Expr::Project(
                                    pi.with_inferred_type(field_type.underlying),
                                    Projection {
                                        base: base.into(),
                                        select: ProductElement::Ordinal(field_index),
                                    },
                                ),
                            ))
                        } else {
                            Err(TypeError::BadProjection {
                                projection: projection.clone(),
                                inferred_base_type: structure.materialize_monotype(),
                            }
                            .at(pi))
                        }
                    } else if candidates.is_empty() {
                        Err(TypeError::BadProjection {
                            projection: projection.clone(),
                            inferred_base_type: base_type,
                        }
                        .at(pi))
                    } else {
                        Err(TypeError::AmbiguousRecordProjection {
                            projection: projection.clone(),
                            choices: candidates
                                .iter()
                                .map(|tc| tc.structure().map(|s| s.materialize_monotype()))
                                .collect::<Typing<_>>()?,
                        }
                        .at(pi))
                    }
                }

                _ => Err(TypeError::BadProjection {
                    projection: projection.clone(),
                    inferred_base_type: base.type_info().inferred_type.clone(),
                }
                .at(pi)),
            },

            ProductElement::Ordinal(ordinal) => match expanded_base_type {
                TypeStructure::Monotype(Type::Tuple(tuple)) => {
                    if let Some(element) = tuple.elements().get(*ordinal) {
                        Ok(Typed::computed(
                            substitutions,
                            constraints,
                            Expr::Project(
                                pi.with_inferred_type(element.clone()),
                                Projection {
                                    base: base.into(),
                                    select: ProductElement::Ordinal(*ordinal),
                                },
                            ),
                        ))
                    } else {
                        Err(TypeError::TupleOrdinalOutOfBounds {
                            base: (*projection.base).clone(),
                            select: projection.select.clone(),
                        }
                        .at(pi))?
                    }
                }

                TypeStructure::Monotype(Type::Variable(..)) => {
                    let mut elems = Vec::with_capacity(ordinal + 1);
                    for _ in 0..=*ordinal {
                        elems.push(Type::fresh());
                    }
                    let tuple_ty = Type::Tuple(TupleType::from_signature(&elems));
                    let subs = base_type
                        .unified_with(&tuple_ty, &self.types)
                        .map_err(|e| e.at(pi))?;

                    let projected_ty = match tuple_ty.apply(&subs) {
                        Type::Tuple(tuple) => tuple.elements()[*ordinal].clone(),
                        _ => unreachable!(),
                    };

                    let substitutions = substitutions.compose(&subs);
                    let constraints = constraints.apply(&substitutions);
                    Ok(Typed::computed(
                        substitutions,
                        constraints,
                        Expr::Project(
                            pi.with_inferred_type(projected_ty),
                            Projection {
                                base: base.into(),
                                select: ProductElement::Ordinal(*ordinal),
                            },
                        ),
                    ))
                }

                _ => Err(TypeError::BadProjection {
                    projection: projection.clone(),
                    inferred_base_type: base.type_info().inferred_type.clone(),
                }
                .at(pi)),
            },
        }
    }

    #[instrument]
    fn infer_tuple(&mut self, pi: ParseInfo, tuple: &phase::Tuple<Named>) -> Typing {
        let (substitutions, constraints, elements, element_types) =
            self.infer_several(&tuple.elements)?;

        Ok(Typed::computed(
            substitutions,
            constraints,
            Expr::Tuple(
                pi.with_inferred_type(Type::Tuple(TupleType::from_signature(&element_types))),
                Tuple { elements },
            ),
        ))
    }

    #[instrument]
    fn infer_several(
        &mut self,
        elements: &Vec<Tree<ParseInfo, Identifier>>,
    ) -> Typing<(
        Substitutions,
        ConstraintSet,
        Vec<Tree<TypeInfo, Identifier>>,
        Vec<Type>,
    )> {
        let mut substitutions = Substitutions::default();
        let mut typed_elements = Vec::with_capacity(elements.len());
        let mut constraints = ConstraintSet::default();

        for element in elements {
            let typed = self.infer_expr(element)?;
            typed_elements.push(typed.tree);
            substitutions = substitutions.compose(&typed.substitutions);
            constraints = constraints.union(typed.constraints.apply(&substitutions));
        }

        let typed_elements = typed_elements
            .iter()
            .map(|e| e.apply(&substitutions).into())
            .collect::<Vec<_>>();

        let element_types = typed_elements
            .iter()
            .map(|e: &Tree<TypeInfo, namer::Identifier>| e.type_info().inferred_type.clone())
            .collect();

        Ok((substitutions, constraints, typed_elements, element_types))
    }

    #[instrument]
    fn infer_recursive_lambda(
        &mut self,
        pi: ParseInfo,
        rec_lambda: &phase::SelfReferential<Named>,
    ) -> Typing {
        let domain = Type::fresh();
        let codomain = Type::fresh();
        let own_capture = Confinement::fresh();
        let own_ty = Type::Arrow {
            capture: own_capture.clone(),
            domain: domain.clone().into(),
            codomain: codomain.clone().into(),
        };
        self.bind_term_and_then(
            rec_lambda.own_name.clone(),
            TypeScheme::from_constant(own_ty.clone()),
            |ctx| {
                ctx.bind_term_and_then(
                    rec_lambda.lambda.parameter.clone(),
                    TypeScheme::from_constant(domain),
                    |ctx| {
                        let typed = ctx.infer_expr(&rec_lambda.lambda.body)?;
                        let s_codomain = typed
                            .tree
                            .type_info()
                            .inferred_type
                            .unified_with(&codomain.apply(&typed.substitutions), &ctx.types)
                            .map_err(|e| e.at(pi))?;

                        let substitutions = typed.substitutions.compose(&s_codomain);
                        let tree = typed.tree.apply(&substitutions);
                        let actual_capture = ctx.lambda_capture_confinement(
                            &rec_lambda.lambda.parameter,
                            Some(&rec_lambda.own_name),
                            &tree,
                        )?;
                        let expected_capture = own_capture.apply(&substitutions.confinements);
                        let capture_substitutions = expected_capture
                            .unify(&actual_capture.joined)
                            .map(Substitutions::with_confinements)
                            .ok_or_else(|| actual_capture.mismatch(expected_capture, pi))?;
                        let substitutions = substitutions.compose(&capture_substitutions);

                        Ok(Typed::computed(
                            substitutions.clone(),
                            typed.constraints.apply(&substitutions),
                            Expr::RecursiveLambda(
                                pi.with_inferred_type(own_ty.apply(&substitutions)),
                                SelfReferential {
                                    own_name: rec_lambda.own_name.clone(),
                                    lambda: Lambda {
                                        parameter: rec_lambda.lambda.parameter.clone(),
                                        body: tree.apply(&substitutions).into(),
                                    },
                                },
                            ),
                        ))
                    },
                )
            },
        )
    }

    #[instrument]
    fn _infer_apply_with_checked_arg(
        &mut self,
        pi: ParseInfo,
        function: &phase::Expr<Named>,
        argument: &phase::Expr<Named>,
    ) -> Typing {
        let mut function = self.infer_expr(function)?;
        let function_type = &function.tree.type_info().inferred_type;

        if let Type::Variable(..) = function_type {
            tracing::trace!("unknown function");
            let domain = Type::fresh();
            let codomain = Type::fresh();
            let unification = Type::Arrow {
                capture: Confinement::fresh(),
                domain: domain.into(),
                codomain: codomain.into(),
            }
            .unified_with(function_type, &self.types)
            .map_err(|e| e.at(pi))?;

            let s_function = function.substitutions.compose(&unification);
            function = function.apply(&s_function);
            self.substitute_mut(&s_function);
        }

        let function_type = &function.tree.type_info().inferred_type;
        if let Type::Arrow {
            domain, codomain, ..
        } = &function_type
        {
            let argument = self.check_expr(&domain.apply(&function.substitutions), argument)?;

            let substitutions = function.substitutions.compose(&argument.substitutions);
            let codomain = codomain.apply(&substitutions);
            let argument = argument.apply(&substitutions);

            let constraints = function
                .constraints
                .apply(&substitutions)
                .union(argument.constraints);

            Ok(Typed::computed(
                substitutions,
                constraints,
                Expr::Apply(
                    pi.with_inferred_type(codomain),
                    Apply {
                        function: function.tree.into(),
                        argument: argument.tree.into(),
                    },
                ),
            ))
        } else {
            todo!()
        }
    }

    /// Infer a curried binary combinator whose second argument determines the type
    /// expected by its first. Desugared `let*`/`let+` have precisely this shape:
    /// `bind (lambda x. body) action`. Inferring the lambda first leaves `x` as an
    /// unconstrained metavariable, which makes an otherwise concrete `x.Field`
    /// spuriously ambiguous. Infer `action`, unify it with argument two, then check
    /// the continuation against the now-refined argument-one type.
    fn infer_reverse_binary_apply(
        &mut self,
        pi: ParseInfo,
        function: &phase::Expr<Named>,
        first: &phase::Expr<Named>,
        second: &phase::Expr<Named>,
    ) -> Typing {
        let function = self.infer_expr(function)?;
        let mut substitutions = function.substitutions.clone();
        let mut ctx = self.apply(&substitutions);
        let second = ctx.infer_expr(second)?;
        substitutions = substitutions.compose(&second.substitutions);

        let function_type = function
            .tree
            .type_info()
            .inferred_type
            .apply(&substitutions);
        let Type::Arrow {
            domain: first_domain,
            codomain,
            ..
        } = function_type
        else {
            unreachable!("bind/fmap are functions")
        };
        let Type::Arrow {
            domain: second_domain,
            codomain: result,
            ..
        } = *codomain
        else {
            unreachable!("bind/fmap are curried binary functions")
        };

        let second_unification = second_domain
            .apply(&substitutions)
            .unified_with(
                &second.tree.type_info().inferred_type.apply(&substitutions),
                &ctx.types,
            )
            .map_err(|e| e.at(pi))?;
        substitutions = substitutions.compose(&second_unification);
        ctx = self.apply(&substitutions);

        let first = ctx.check_expr(&first_domain.apply(&substitutions), first)?;
        substitutions = substitutions.compose(&first.substitutions);
        let constraints = function
            .constraints
            .apply(&substitutions)
            .union(first.constraints.apply(&substitutions))
            .union(second.constraints.apply(&substitutions));

        let inner_type = Type::Arrow {
            capture: Confinement::fresh(),
            domain: second_domain,
            codomain: result.clone(),
        }
        .apply(&substitutions);
        let inner = Expr::Apply(
            pi.with_inferred_type(inner_type),
            Apply {
                function: function.tree.apply(&substitutions).into(),
                argument: first.tree.apply(&substitutions).into(),
            },
        );
        Ok(Typed::computed(
            substitutions.clone(),
            constraints,
            Expr::Apply(
                pi.with_inferred_type(result.apply(&substitutions)),
                Apply {
                    function: inner.into(),
                    argument: second.tree.apply(&substitutions).into(),
                },
            ),
        ))
    }

    #[instrument]
    fn infer_apply(
        &mut self,
        pi: ParseInfo,
        function: &phase::Expr<Named>,
        argument: &phase::Expr<Named>,
    ) -> Typing {
        let function = self.infer_expr(function)?;

        let mut ctx = self.apply(&function.substitutions);
        let mut constraints = function.constraints;

        let argument = ctx.infer_expr(argument)?;
        constraints = constraints
            .apply(&argument.substitutions)
            .union(argument.constraints.apply(&function.substitutions));
        let return_ty = Type::fresh();

        let substitutions = function.substitutions.compose(&argument.substitutions);

        let expected_ty = Type::Arrow {
            capture: Confinement::fresh(),
            domain: argument
                .tree
                .type_info()
                .inferred_type
                .apply(&substitutions)
                .into(),
            codomain: return_ty.clone().into(),
        };

        let substitutions = function
            .tree
            .type_info()
            .inferred_type
            .apply(&substitutions)
            .unified_with(&expected_ty.apply(&substitutions), &self.types)
            // Attribution runs only on the error path: rebuilding the typed
            // argument is not worth doing for every application that succeeds.
            .map_err(|e| {
                ctx.attribute_confined_capture(e, &argument.tree.apply(&substitutions))
                    .at(pi)
            })?
            .compose(&substitutions);

        let apply = Apply {
            function: function.tree.apply(&substitutions).into(),
            argument: argument.tree.apply(&substitutions).into(),
        };

        let inferred_type = return_ty.apply(&substitutions);
        constraints = constraints.apply(&substitutions);

        Ok(Typed::computed(
            substitutions,
            constraints,
            Expr::Apply(pi.with_inferred_type(inferred_type), apply),
        ))
    }

    /// How far `confinement_path` descends before giving up. A diagnostic aid, so
    /// the bound only needs to cover the nesting a person would want named.
    const CONFINEMENT_PATH_DEPTH: usize = 8;

    /// Is this type opaque, so that its representation is not the caller's
    /// business? Descent stops here: the answer to "why is this confined" is the
    /// abstraction's own name, not the field it happens to wrap.
    fn is_opaque(&self, ty: &Type) -> bool {
        let mut head = ty;
        while let Type::Apply { constructor, .. } = head {
            head = constructor;
        }
        match head {
            Type::Constructor(name) => self.types.lookup(name).is_some_and(|constructor| {
                matches!(
                    constructor.definition().defining_symbol.opacity,
                    namer::Access::Within(_)
                )
            }),
            _ => false,
        }
    }

    /// Explain *why* a composite is confined: the field or constructor chain down
    /// to the confined leaf, plus that leaf's type. `Workspace` yields
    /// (`["scratch"]`, `Buffer`). Returns `None` when the type is confined in
    /// itself, when nothing is visible, or when expansion fails -- callers then
    /// report the type alone.
    ///
    /// Purely a diagnostic aid, so it prefers giving up to being wrong: it bounds
    /// the descent rather than tracking visited constructors, which keeps a
    /// recursive type from looping.
    fn confinement_path(
        &self,
        ty: &Type,
        pi: ParseInfo,
        fuel: usize,
    ) -> Option<(Vec<String>, Type)> {
        if fuel == 0 || self.is_opaque(ty) {
            return None;
        }
        let confined = |ty: &Type| {
            matches!(
                ty.kind(&self.types)
                    .ok()
                    .as_ref()
                    .and_then(Kind::confinement),
                Some(Confinement::Confined)
            )
        };

        // Descend through the first confined component. If the component cannot
        // itself be explained further, it is the leaf we are looking for.
        let step = |label: String, field: &Type| -> Option<(Vec<String>, Type)> {
            confined(field).then(|| match self.confinement_path(field, pi, fuel - 1) {
                Some((rest, leaf)) => (
                    std::iter::once(label.clone()).chain(rest).collect(),
                    leaf,
                ),
                None => (vec![label], field.clone()),
            })
        };

        let structure = match self.expand_type_constructor(pi, ty) {
            Ok(Some(TypeStructure::Monotype(expanded))) => expanded,
            // A declared record expands to its field schemes rather than a
            // structural record type.
            Ok(Some(TypeStructure::PolyRecord(record))) => {
                return record.fields().find_map(|(name, scheme)| {
                    step(name.to_string(), &scheme.underlying)
                });
            }
            _ => return None,
        };

        match &structure {
            Type::Record(record) => record
                .0
                .iter()
                .find_map(|(name, field)| step(name.to_string(), field)),
            Type::Coproduct(coproduct) => {
                coproduct.0.iter().find_map(|(constructor, arguments)| {
                    arguments
                        .iter()
                        .find_map(|argument| step(constructor.member.to_string(), argument))
                })
            }
            Type::Tuple(tuple) => tuple
                .0
                .iter()
                .enumerate()
                .find_map(|(index, element)| step(format!("{index}"), element)),
            Type::Array(element) => step("[]".to_string(), element),
            _ => None,
        }
    }

    /// Turn an opaque capture-index mismatch into one that names the offending
    /// capture. Unification reports `IO unconfined _` against `IO confined _`
    /// without knowing *why* the action is confined -- that lives in the lambda
    /// it is applied to. This is a pure diagnostic pass: it runs only once an
    /// error has already been produced, and can never change what is accepted.
    fn attribute_confined_capture(
        &self,
        error: TypeError,
        argument: &phase::Expr<Types>,
    ) -> TypeError {
        // A requirement failure already names the offending type; it only lacks
        // the path explaining why that type is confined.
        if let TypeError::ConfinementRequirement {
            ty,
            actual,
            required,
            path: _,
        } = error
        {
            let pi = argument.annotation().parse_info;
            return TypeError::ConfinementRequirement {
                path: ConfinementPath(self.confinement_path(
                    &ty,
                    pi,
                    Self::CONFINEMENT_PATH_DEPTH,
                )),
                ty,
                actual,
                required,
            };
        }

        if !matches!(error, TypeError::ConfinementMismatch { .. }) {
            return error;
        }

        let mut blamed = None;
        argument.walk(&mut |expression| {
            if blamed.is_some() {
                return;
            }
            let (parameter, body, own) = match expression {
                Expr::Lambda(_, lambda) => (&lambda.parameter, &lambda.body, None),
                Expr::RecursiveLambda(_, rec) => (
                    &rec.lambda.parameter,
                    &rec.lambda.body,
                    Some(&rec.own_name),
                ),
                _ => return,
            };
            if let Ok(captures) = self.lambda_capture_confinement(parameter, own, body) {
                blamed = captures.confined().cloned();
            }
        });

        match blamed {
            Some(capture) => TypeError::ConfinedCapture {
                path: ConfinementPath(self.confinement_path(
                    &capture.ty,
                    capture.parse_info,
                    Self::CONFINEMENT_PATH_DEPTH,
                )),
                ty: capture.ty,
            },
            None => error,
        }
    }

    fn lambda_capture_confinement(
        &self,
        parameter: &namer::Identifier,
        ignored_capture: Option<&namer::Identifier>,
        body: &phase::Expr<Types>,
    ) -> Typing<CaptureConfinement> {
        let namer::Identifier::Bound(parameter_level) = parameter else {
            return Err(TypeError::InternalAssertion(
                "lambda parameter was not a bound identifier".into(),
            )
            .at(body.annotation().parse_info));
        };

        let mut captures = Vec::new();
        body.walk(&mut |expression| {
            if let Expr::Variable(type_info, identifier) = &expression {
                let is_capture = match identifier {
                    namer::Identifier::Bound(level) => level < parameter_level,
                    // Closure capture inference is deliberately lexical. Global
                    // reachability is a separate whole-program dependency check at
                    // the eventual spawn boundary; treating code/constructor names
                    // as heap captures here both conflates the two judgments and
                    // destroys principal capture equations for ordinary functions.
                    namer::Identifier::Free(_) => false,
                };
                if is_capture && ignored_capture != Some(identifier) {
                    captures.push((type_info.parse_info, type_info.inferred_type.clone()));
                }
            }
        });

        let captures = captures
            .into_iter()
            .map(|(parse_info, ty)| {
                ty.kind(&self.types)
                    .map_err(|error| error.at(parse_info))
                    .and_then(|kind| {
                        kind.confinement().cloned().ok_or_else(|| {
                            TypeError::ExpectedMonotypeKind { kind }.at(parse_info)
                        })
                    })
                    .map(|confinement| Capture {
                        parse_info,
                        ty,
                        confinement,
                    })
            })
            .collect::<Typing<Vec<_>>>()?;

        Ok(CaptureConfinement {
            joined: Confinement::join(
                captures
                    .iter()
                    .map(|capture| capture.confinement.clone())
                    .collect::<Vec<_>>(),
            ),
            captures,
        })
    }

    #[instrument]
    fn infer_lambda(
        &mut self,
        pi: ParseInfo,
        lambda: &phase::Lambda<Named>,
    ) -> Typing<(Substitutions, ConstraintSet, TypeInfo, phase::Lambda<Types>)> {
        let domain = Type::fresh();
        let codomain = Type::fresh();

        self.bind_term_and_then(
            lambda.parameter.clone(),
            TypeScheme::from_constant(domain.clone()),
            |ctx| {
                let Typed {
                    mut substitutions,
                    tree: body,
                    constraints,
                } = ctx.infer_expr(&lambda.body)?;

                let body_type = body.type_info().inferred_type.apply(&substitutions);

                let unify_subs = body_type
                    .unified_with(&codomain.apply(&substitutions), &ctx.types)
                    .map_err(|e| e.at(pi))?;

                substitutions = substitutions.compose(&unify_subs);

                let body = body.apply(&substitutions);
                let capture = ctx.lambda_capture_confinement(&lambda.parameter, None, &body)?;

                let inferred_type = Type::Arrow {
                    capture: capture.joined,
                    domain: domain.apply(&substitutions).into(),
                    codomain: codomain.apply(&substitutions).into(),
                };

                let constraints = constraints.apply(&substitutions);

                Ok((
                    substitutions,
                    constraints,
                    pi.with_inferred_type(inferred_type),
                    Lambda {
                        parameter: lambda.parameter.clone(),
                        body: body.into(),
                    },
                ))
            },
        )
    }

    #[instrument]
    // Check-mode counterpart of [`infer_binding`]: the bound is still inferred (and
    // generalized) exactly the same way, but the body is *checked* against the expected
    // type instead of inferred-then-unified. That pushes the expectation down to the
    // body's tail expression, so a mismatch is reported there rather than at this `let`.
    fn check_binding(
        &mut self,
        pi: ParseInfo,
        expected_type: &Type,
        binding: &phase::Binding<Named>,
    ) -> Typing {
        let typed_bound = self.infer_expr(&binding.bound)?;
        let mut ctx1 = self.apply(&typed_bound.substitutions);

        let bound_type = typed_bound.as_constrained_type().generalize(&ctx1);
        // A constrained local binding stays MONOMORPHIC. Generalisation quantifies the
        // type but does not abstract the DICTIONARY -- the scheme would carry
        // `Applicative m` while the bound lambda is still `λi. λacc. …` with no dictionary
        // parameter and no use site supplying one, leaving the body's evidence reference
        // dangling (it then resolves to whatever local shares that level). Keeping it
        // monomorphic lets the metavariable stay shared, so the use site's unification
        // grounds it (`m := IO`) and the constraint resolves to a real witness. This is the
        // monomorphism restriction, forced here by the absence of dictionary abstraction
        // for local bindings.
        let generalizes = typed_bound.constraints.is_empty()
            || (is_generalizable_value(binding.bound.as_ref())
                && bound_type.underlying.constraints.is_empty());
        // A constraint that generalisation moved INTO the binding's scheme is discharged
        // afresh at each use site, where the instantiated variable unifies with the
        // actual type. Propagating the definition's copy outward as well leaks the
        // binding's OWN metavariable into the enclosing term, where it appears nowhere in
        // that term's type -- an ambiguous residual. Being variable-headed it is then
        // misclassified as parametric and becomes a leading dictionary parameter that the
        // enclosing term's registered scheme does not mention, so callers never pass one:
        // the body reads its dictionary out of whatever argument does arrive.
        //
        // That is how `let loop = λi acc. … pure acc in let* c = loop 0 0 …` silently
        // dropped its continuation (`pure` projected out of the `IO` suspension's Unit),
        // or segfaulted outright at higher arity. Constraints generalisation did NOT take
        // (they mention variables bound outside) still have to be retained here.
        let retained_constraints = if generalizes {
            typed_bound
                .constraints
                .difference(&bound_type.underlying.constraints)
        } else {
            typed_bound.constraints.clone()
        };
        let bound_scheme = if generalizes {
            bound_type.underlying
        } else {
            TypeScheme::from_constant(bound_type.underlying.underlying)
        };

        let expected = expected_type.apply(&typed_bound.substitutions);
        ctx1.bind_term_and_then(binding.binder.clone(), bound_scheme, |ctx| {
            let typed_body = ctx.check_expr(&expected, &binding.body)?;

            let substitutions = typed_bound.substitutions.compose(&typed_body.substitutions);

            let bound = typed_bound.tree.apply(&substitutions);
            let body = typed_body.tree.apply(&substitutions);
            let constraints = retained_constraints
                .apply(&substitutions)
                .union(typed_body.constraints.apply(&substitutions));

            Ok(Typed::computed(
                substitutions,
                constraints,
                Expr::Let(
                    pi.with_inferred_type(body.type_info().inferred_type.clone()),
                    Binding {
                        binder: binding.binder.clone(),
                        operator: binding.operator,
                        bound: bound.into(),
                        body: body.into(),
                    },
                ),
            ))
        })
    }

    // Check-mode counterpart of [`infer_sequence`]: `this` is inferred for its effect,
    // and `and_then` is checked against the expected type so a mismatch lands on the
    // sequence's tail rather than the sequence node.
    fn check_sequence(
        &mut self,
        expected_type: &Type,
        sequence: &phase::Sequence<Named>,
    ) -> Typing {
        let this = self.infer_expr(&sequence.this)?;
        self.substitute_mut(&this.substitutions);
        let and_then = self.check_expr(
            &expected_type.apply(&this.substitutions),
            &sequence.and_then,
        )?;
        let substitutions = this.substitutions.compose(&and_then.substitutions);
        let constraints = this
            .constraints
            .apply(&substitutions)
            .union(and_then.constraints.apply(&substitutions));
        Ok(Typed::computed(
            substitutions,
            constraints,
            Expr::Sequence(
                and_then.tree.type_info().clone(),
                Sequence {
                    this: this.tree.into(),
                    and_then: and_then.tree.into(),
                },
            ),
        ))
    }

    fn infer_binding(&mut self, pi: ParseInfo, binding: &phase::Binding<Named>) -> Typing {
        let typed_bound = self.infer_expr(&binding.bound)?;
        let mut ctx1 = self.apply(&typed_bound.substitutions);

        let bound_type = typed_bound.as_constrained_type().generalize(&ctx1);
        // A constrained local binding stays MONOMORPHIC. Generalisation quantifies the
        // type but does not abstract the DICTIONARY -- the scheme would carry
        // `Applicative m` while the bound lambda is still `λi. λacc. …` with no dictionary
        // parameter and no use site supplying one, leaving the body's evidence reference
        // dangling (it then resolves to whatever local shares that level). Keeping it
        // monomorphic lets the metavariable stay shared, so the use site's unification
        // grounds it (`m := IO`) and the constraint resolves to a real witness. This is the
        // monomorphism restriction, forced here by the absence of dictionary abstraction
        // for local bindings.
        let generalizes = typed_bound.constraints.is_empty()
            || (is_generalizable_value(binding.bound.as_ref())
                && bound_type.underlying.constraints.is_empty());
        // See `check_binding`: a constraint generalisation moved into the binding's own
        // scheme must NOT also be propagated outward, or the binding's metavariable leaks
        // into the enclosing term as an ambiguous residual and becomes a phantom
        // dictionary parameter.
        let retained_constraints = if generalizes {
            typed_bound
                .constraints
                .difference(&bound_type.underlying.constraints)
        } else {
            typed_bound.constraints.clone()
        };
        let bound_scheme = if generalizes {
            bound_type.underlying
        } else {
            // Expansive constrained bindings remain monomorphic. Their result type
            // and wanted constraints therefore share metavariables with the body,
            // allowing later uses to ground the evidence instead of creating stale,
            // independently-generalized dictionary parameters.
            TypeScheme::from_constant(bound_type.underlying.underlying)
        };

        ctx1.bind_term_and_then(binding.binder.clone(), bound_scheme, |ctx| {
            let typed_body = ctx.infer_expr(&binding.body)?;

            let substitutions = typed_bound.substitutions.compose(&typed_body.substitutions);

            let bound = typed_bound.tree.apply(&substitutions);
            let body = typed_body.tree.apply(&substitutions);
            let constraints = retained_constraints
                .apply(&substitutions)
                .union(typed_body.constraints.apply(&substitutions));

            Ok(Typed::computed(
                substitutions,
                constraints,
                Expr::Let(
                    pi.with_inferred_type(body.type_info().inferred_type.clone()),
                    Binding {
                        binder: binding.binder.clone(),
                        operator: binding.operator,
                        bound: bound.into(),
                        body: body.into(),
                    },
                ),
            ))
        })
    }

    #[instrument]
    fn infer_sequence(&mut self, sequence: &phase::Sequence<Named>) -> Typing {
        let this = self.infer_expr(&sequence.this)?;
        self.substitute_mut(&this.substitutions);
        let and_then = self.infer_expr(&sequence.and_then)?;
        let substitutions = this.substitutions.compose(&and_then.substitutions);
        let constraints = this
            .constraints
            .apply(&substitutions)
            .union(and_then.constraints.apply(&substitutions));
        Ok(Typed::computed(
            substitutions,
            constraints,
            Expr::Sequence(
                and_then.tree.type_info().clone(),
                Sequence {
                    this: this.tree.into(),
                    and_then: and_then.tree.into(),
                },
            ),
        ))
    }

    #[instrument]
    fn infer_if_then_else(
        &mut self,
        pi: ParseInfo,
        if_then_else: &phase::IfThenElse<Named>,
    ) -> Typing {
        let predicate = self.infer_expr(&if_then_else.predicate)?;
        let s_bool_predicate = predicate
            .tree
            .type_info()
            .inferred_type
            .unified_with(&Type::Base(BaseType::Bool), &self.types)
            .map_err(|e| e.at(pi))?;
        let s_predicate = predicate.substitutions.compose(&s_bool_predicate);

        self.substitute_mut(&s_predicate);
        let consequent = self.infer_expr(&if_then_else.consequent)?;

        self.substitute_mut(&consequent.substitutions);
        let alternate = self.infer_expr(&if_then_else.alternate)?;

        let s_branches = s_predicate
            .compose(&consequent.substitutions)
            .compose(&alternate.substitutions);

        let consequent_type = consequent
            .tree
            .apply(&s_branches)
            .type_info()
            .inferred_type
            .clone();

        let substitutions = consequent_type
            .unified_with(
                &alternate.tree.apply(&s_branches).type_info().inferred_type,
                &self.types,
            )
            .map_err(|e| e.at(pi))?;

        let substitutions = s_branches.compose(&substitutions);

        let predicate = predicate.apply(&substitutions);
        let consequent = consequent.apply(&substitutions);
        let alternate = alternate.apply(&substitutions);

        Ok(Typed::computed(
            substitutions,
            predicate
                .constraints
                .union(consequent.constraints)
                .union(alternate.constraints),
            Expr::If(
                pi.with_inferred_type(consequent_type),
                IfThenElse {
                    predicate: predicate.tree.into(),
                    consequent: consequent.tree.into(),
                    alternate: alternate.tree.into(),
                },
            ),
        ))
    }

    fn free_variables(&self) -> HashSet<MetaVariable> {
        self.terms.free_variables()
    }

    fn free_confinement_variables(&self) -> BTreeSet<u32> {
        self.terms.free_confinement_variables()
    }
}

impl Literal {
    fn synthesize_type(&self) -> Type {
        // A string literal is a `Text` -- the stdlib DU (`opaque Text ::= Text Bytes`),
        // not a builtin base type -- so it flows through the same elaboration as any
        // other constructor value. Every other literal is still a base type.
        if let Self::Text(..) = self {
            return stdlib_text_type();
        }
        Type::Base(match self {
            Self::Int(..) => BaseType::Int,
            Self::Float(..) => BaseType::Float,
            Self::Text(..) => unreachable!("handled above"),
            Self::Bool(..) => BaseType::Bool,
            Self::Unit => BaseType::Unit,
            Self::Char(..) => BaseType::Char,
        })
    }
}

impl ParseInfo {
    pub fn with_inferred_type(self, inferred_type: Type) -> TypeInfo {
        TypeInfo {
            parse_info: self,
            inferred_type,
            enclosing_term: None,
        }
    }
}

// todo: move to pattern.rs
impl Denotation {
    // The uncovered cases of this denotation against `scrutinee`, each a human-readable
    // pattern description (empty = exhaustive). Mirrors the old boolean `covers`, but
    // collects *which* cases are missing so the exhaustiveness error can name them.
    fn uncovered(
        &self,
        pi: ParseInfo,
        scrutinee: &Type,
        ctx: &TypingContext,
    ) -> Typing<Vec<String>> {
        match self {
            Self::Structured(shape) => shape.uncovered(pi, scrutinee, ctx),

            Self::Universal => Ok(vec![]),

            // Nothing matched (an empty match), or only specific literals over a type we
            // do not finitely enumerate here (Int/Char/...): report a wildcard gap.
            Self::Empty | Self::Finite(..) => Ok(vec!["_".to_owned()]),
        }
    }
}

// todo: move to pattern.rs
impl Shape {
    fn uncovered(
        &self,
        pi: ParseInfo,
        scrutinee: &Type,
        ctx: &TypingContext,
    ) -> Typing<Vec<String>> {
        let scrutinee = ctx
            .expand_type_constructor(pi, scrutinee)?
            .unwrap_or_else(|| TypeStructure::Monotype(scrutinee.clone()));

        match (self, scrutinee) {
            (
                Self::Coproduct(denotations),
                TypeStructure::Monotype(Type::Coproduct(CoproductType(constructors))),
            ) => {
                let mut missing = Vec::new();

                // Iterated in the coproduct type's stored constructor order, so the
                // reported list is deterministic.
                for (constructor, arguments) in constructors {
                    match denotations.get(&constructor) {
                        // The constructor is never matched at all.
                        None => missing.push(constructor.member.as_str().to_owned()),
                        // Matched, but an argument leaves a gap -- e.g. `This Nope`.
                        Some(argument_denotations) => {
                            for (denotation, scrutinee) in
                                argument_denotations.iter().zip(arguments)
                            {
                                for sub in denotation.uncovered(pi, &scrutinee, ctx)? {
                                    missing.push(format!("{} {sub}", constructor.member.as_str()));
                                }
                            }
                        }
                    }
                }

                Ok(missing)
            }

            (Self::Struct(denotations), TypeStructure::PolyRecord(record_type)) => {
                let mut missing = Vec::new();
                for (field, scrutinee) in record_type.fields() {
                    let scrutinee = scrutinee.instantiate();
                    for sub in denotations[field].uncovered(pi, &scrutinee.underlying, ctx)? {
                        missing.push(format!("{{ {field} = {sub} }}"));
                    }
                }
                Ok(missing)
            }

            (Self::Tuple(denotations), TypeStructure::Monotype(Type::Tuple(TupleType(types)))) => {
                let mut missing = Vec::new();
                for (denotation, scrutinee) in denotations.iter().zip(types) {
                    missing.extend(denotation.uncovered(pi, &scrutinee, ctx)?);
                }
                Ok(missing)
            }

            otherwise => panic!("Latent type error. {otherwise:?}"),
        }
    }
}

// todo: move to pattern.rs
impl phase::Pattern<Types> {
    fn denotation(&self) -> Denotation {
        match self {
            Pattern::Coproduct(_, pattern) => {
                Denotation::Structured(Shape::Coproduct(HashMap::from([(
                    pattern.constructor.try_as_free().cloned().expect("this is what I get for having constructor be namer::Identifier when it ought to be a QualifiedName"),
                    pattern.arguments.iter().map(|p| p.denotation()).collect(),
                )])))
            }

            Pattern::Tuple(_, pattern) => Denotation::Structured(Shape::Tuple(
                pattern.elements.iter().map(|e| e.denotation()).collect(),
            )),

            Pattern::Struct(_, pattern) => Denotation::Structured(Shape::Struct(
                pattern
                    .fields
                    .iter()
                    .map(|(field, pattern)| (field.clone(), pattern.denotation()))
                    .collect(),
            )),

            Pattern::Literally(_, pattern) => Denotation::Finite(
                BTreeSet::from([pattern.clone()])
            ),

            Pattern::Bind(..) => Denotation::Universal,
        }
    }

    fn map_binders<F>(self, f: &F) -> Self
    where
        F: Fn(namer::Identifier) -> namer::Identifier,
    {
        match self {
            Self::Coproduct(
                a,
                ConstructorPattern {
                    constructor,
                    arguments,
                },
            ) => Self::Coproduct(
                a,
                ConstructorPattern {
                    constructor,
                    arguments: arguments
                        .into_iter()
                        .map(|pattern| pattern.map_binders(f))
                        .collect(),
                },
            ),
            Self::Tuple(a, pattern) => Self::Tuple(
                a,
                TuplePattern {
                    elements: pattern
                        .elements
                        .into_iter()
                        .map(|pattern| pattern.map_binders(f))
                        .collect(),
                },
            ),
            Self::Struct(a, pattern) => Self::Struct(
                a,
                StructPattern {
                    fields: pattern
                        .fields
                        .into_iter()
                        .map(|(field, pattern)| (field, pattern.map_binders(f)))
                        .collect(),
                },
            ),
            Self::Literally(..) => self,
            Self::Bind(a, pattern) => Self::Bind(a, f(pattern)),
        }
    }
}

// todo: move to pattern.rs
#[derive(Debug, Default)]
pub struct MatchSpace {
    pub covered: Denotation,
}

// todo: move to pattern.rs
impl MatchSpace {
    // The uncovered cases of this match against `scrutinee` (empty = exhaustive), each a
    // readable pattern description for the exhaustiveness diagnostic.
    pub fn uncovered(
        &self,
        pi: ParseInfo,
        scrutinee: &Type,
        ctx: &TypingContext,
    ) -> Typing<Vec<String>> {
        self.covered.normalize().uncovered(pi, scrutinee, ctx)
    }

    pub fn join(&mut self, p: &phase::Pattern<Types>) -> bool {
        let new_coverage = p
            .denotation()
            .join(&self.covered)
            .expect("code that typechecks");

        let useful = new_coverage != self.covered;
        self.covered = new_coverage;

        useful
    }
}

impl<E> fmt::Display for Located<E>
where
    E: fmt::Display + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { parse_info, error } = self;
        // Prefix with the source file when we know it. `ParseInfo`'s own `Display`
        // stays file-free on purpose -- it's also printed inside inferred-type dumps,
        // which shouldn't be cluttered with paths.
        match crate::source_map::path_of(parse_info.file) {
            Some(path) => write!(f, "{}:{parse_info}: {error}", path.display())?,
            None => write!(f, "{parse_info}: {error}")?,
        }
        // Quote the offending source line beneath the message, so a diagnostic points
        // at real code rather than a phase-internal term rendering (e.g. `#3`).
        let loc = parse_info.location;
        if let Some(snippet) = crate::source_map::snippet(parse_info.file, loc.row, loc.column) {
            write!(f, "\n{snippet}")?;
        }
        Ok(())
    }
}

impl fmt::Display for TypeInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            parse_info,
            inferred_type,
            ..
        } = self;
        write!(f, "{{{parse_info}:{inferred_type}}}")
    }
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // Capability indices are normally elided from existing type output.
            Kind::Star(_) => write!(f, "*"),
            Kind::Arrow(k1, k2) => write!(f, "{k1} -> {k2}"),
        }
    }
}

impl fmt::Display for Confinement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unconfined => write!(f, "unconfined"),
            Self::Confined => write!(f, "confined"),
            Self::Variable(id) => write!(f, "κ{id}"),
            Self::Join(parts) => {
                let mut parts = parts.iter();
                if let Some(first) = parts.next() {
                    write!(f, "{first}")?;
                    for part in parts {
                        write!(f, " ⊔ {part}")?;
                    }
                }
                Ok(())
            }
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Variable(MetaVariable(p, k)) => write!(f, "${p}:{k}"),

            Self::Base(base_type) => write!(f, "{base_type}"),

            Self::Arrow {
                domain, codomain, ..
            } => write!(f, "({domain} -> {codomain})"),

            Self::Tuple(tuple) => {
                let tuple_rendering = tuple
                    .elements()
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({tuple_rendering})")
            }

            Self::Record(record) => {
                let struct_rendering = record
                    .0
                    .iter()
                    .map(|(label, ty)| format!("{label} : {ty}"))
                    .collect::<Vec<_>>()
                    .join("; ");
                write!(f, "{{ {struct_rendering} }}")
            }

            Self::Coproduct(coproduct) => {
                let constructor_rendering = coproduct
                    .0
                    .iter()
                    .map(|(constructor, signature)| {
                        format!(
                            "{constructor} :: {}",
                            Self::Tuple(TupleType::from_signature(signature))
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(" | ");

                write!(f, "{constructor_rendering}")
            }

            Self::Array(array_element_type) => {
                write!(f, "[{array_element_type}]")
            }

            Self::Constructor(name) => write!(f, "{name}"),

            Self::Apply {
                constructor,
                argument,
                ..
            } => write!(f, "{constructor} [ {argument} ]"),
        }
    }
}

impl<A> fmt::Display for Constrained<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            constraints,
            underlying,
        } = self;
        write!(f, "[{constraints}] => {underlying}")
    }
}

impl fmt::Display for ConstraintSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            display_list(", ", &self.0.iter().collect::<Vec<_>>())
        )
    }
}

impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { constraint_type } = self;
        write!(f, "constraint {constraint_type}")
    }
}

impl fmt::Display for BaseType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int => write!(f, "Int"),
            Self::Float => write!(f, "Float"),
            Self::Text => write!(f, "Text"),
            Self::Bool => write!(f, "Bool"),
            Self::Unit => write!(f, "Unit"),
            Self::Char => write!(f, "Char"),
            Self::Array => write!(f, "Array"),
        }
    }
}

impl fmt::Display for TypeScheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.quantifiers.is_empty() {
            write!(f, "forall {}", self.quantifiers[0])?;
            for param in &self.quantifiers[1..] {
                write!(f, ", {param}")?;
            }
            if self.constraints.is_empty() {
                write!(f, ". ",)?;
            } else {
                write!(f, ". {} |- ", self.constraints)?;
            }
        }

        write!(f, "{}", self.underlying)
    }
}

impl fmt::Display for MetaVariable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "${}", self.0)
    }
}

impl fmt::Display for TypeConstructor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unelaborated(definition) => {
                write!(
                    f,
                    "Suspended {}",
                    definition.defining_symbol.qualified_name()
                )
            }
            Self::Elaborated(constructor) => {
                write!(f, "{}", constructor.definition.name)?;

                for p in constructor.definition.instantiated_params.values() {
                    write!(f, " {p}")?;
                }

                write!(f, " ::= {}", constructor.structure)
            }
        }
    }
}

impl fmt::Display for TypeStructure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Monotype(ty) => write!(f, "{ty}"),
            Self::PolyRecord(record) => {
                write!(f, "{{ ")?;
                for (label, scheme) in record.fields() {
                    writeln!(f, "{label} :: {scheme}")?;
                }
                writeln!(f, "}}")
            }
        }
    }
}

impl fmt::Display for RecordType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self(fields) = self;
        write!(f, "{{ ")?;
        let mut fields = fields.iter();

        if let Some((label, ty)) = fields.next() {
            write!(f, "{label} : {ty}")?;
        }

        for (label, ty) in fields {
            write!(f, "; {label} : {ty}")?;
        }

        write!(f, " }}")
    }
}

#[cfg(test)]
mod confinement_kind_tests {
    use super::*;
    use crate::ast::namer::ConstructorSymbol;
    use crate::ast::{ApplyTypeExpr, TypeVariable};

    fn name(member: &str) -> QualifiedName {
        QualifiedName::new(parser::IdentifierPath::new("Test"), member)
    }

    fn parameter(image: &str, confinement: Confinement) -> TypeVariable {
        TypeVariable::with_kind(parser::Identifier::from_str(image), Kind::Star(confinement))
    }

    #[test]
    fn higher_kinded_confinement_is_a_result_mapping() {
        let raw_name = name("Raw_Mutable_Array");
        let list_name = name("List");
        let mutable_name = name("Mutable_Array");
        let pi = ParseInfo::default();

        let list_element = Confinement::fresh();
        let list_parameter = parameter("a", list_element.clone());
        let list_kind = Kind::Arrow(list_parameter.kind.clone().into(), Kind::star().into());
        let recursive_list = TypeExpression::Apply(
            pi,
            ApplyTypeExpr {
                function: TypeExpression::Constructor(pi, list_name.clone()).into(),
                argument: TypeExpression::Parameter(pi, parser::Identifier::from_str("a")).into(),
                phase: PhantomData,
            },
        );

        let mutable_element = Confinement::fresh();
        let mutable_parameter = parameter("a", mutable_element);
        let mutable_kind = Kind::Arrow(mutable_parameter.kind.clone().into(), Kind::star().into());

        let mut table: phase::SymbolTable<Named> = Default::default();
        table.symbols.insert(
            SymbolName::Type(raw_name.clone()),
            Symbol::Type(TypeSymbol {
                definition: TypeDefinition::Coproduct(CoproductSymbol {
                    name: raw_name.clone(),
                    type_parameters: vec![],
                    constructors: vec![],
                }),
                origin: namer::TypeOrigin::Foreign,
                opacity: namer::Access::Within(parser::IdentifierPath::new("Test")),
                arity: 0,
                kind: Kind::confined(),
            }),
        );
        table.symbols.insert(
            SymbolName::Type(list_name.clone()),
            Symbol::Type(TypeSymbol {
                definition: TypeDefinition::Coproduct(CoproductSymbol {
                    name: list_name.clone(),
                    type_parameters: vec![list_parameter],
                    constructors: vec![
                        ConstructorSymbol {
                            name: name("Empty"),
                            signature: vec![],
                        },
                        ConstructorSymbol {
                            name: name("Cons"),
                            signature: vec![
                                TypeExpression::Parameter(pi, parser::Identifier::from_str("a")),
                                recursive_list,
                            ],
                        },
                    ],
                }),
                origin: namer::TypeOrigin::UserDefined,
                opacity: namer::Access::Anywhere,
                arity: 1,
                kind: list_kind,
            }),
        );
        table.symbols.insert(
            SymbolName::Type(mutable_name.clone()),
            Symbol::Type(TypeSymbol {
                definition: TypeDefinition::Coproduct(CoproductSymbol {
                    name: mutable_name.clone(),
                    type_parameters: vec![mutable_parameter],
                    constructors: vec![ConstructorSymbol {
                        name: name("Mutable"),
                        signature: vec![TypeExpression::Constructor(pi, raw_name)],
                    }],
                }),
                origin: namer::TypeOrigin::UserDefined,
                opacity: namer::Access::Within(parser::IdentifierPath::new("Test")),
                arity: 1,
                kind: mutable_kind,
            }),
        );

        let kinds = table.infer_type_kinds().unwrap();
        for confinement in [Confinement::Unconfined, Confinement::Confined] {
            assert_eq!(
                kinds[&list_name]
                    .clone()
                    .apply(Kind::Star(confinement.clone()))
                    .unwrap(),
                Kind::Star(confinement)
            );
        }
        for confinement in [Confinement::Unconfined, Confinement::Confined] {
            assert_eq!(
                kinds[&mutable_name]
                    .clone()
                    .apply(Kind::Star(confinement))
                    .unwrap(),
                Kind::confined()
            );
        }
    }

    #[test]
    fn unconfined_requirement_distributes_over_a_symbolic_join() {
        let left = Confinement::fresh();
        let right = Confinement::fresh();
        let joined = Confinement::join([left.clone(), right.clone()]);

        let substitutions = joined.require(Confinement::Unconfined).unwrap();

        assert_eq!(left.apply(&substitutions), Confinement::Unconfined);
        assert_eq!(right.apply(&substitutions), Confinement::Unconfined);
        assert_eq!(joined.apply(&substitutions), Confinement::Unconfined);
    }

    #[test]
    fn lambda_capture_confinement_uses_lexically_outer_bound_values() {
        let raw_name = name("Raw_Buffer");
        let raw_symbol = TypeSymbol {
            definition: TypeDefinition::Coproduct(CoproductSymbol {
                name: raw_name.clone(),
                type_parameters: vec![],
                constructors: vec![],
            }),
            origin: namer::TypeOrigin::Foreign,
            opacity: namer::Access::Within(parser::IdentifierPath::new("Test")),
            arity: 0,
            kind: Kind::confined(),
        };
        let mut context = TypingContext::default();
        context
            .types
            .bind(raw_name.clone(), TypeConstructor::from_symbol(&raw_symbol));
        let body = Expr::Variable(
            TypeInfo::new(ParseInfo::default(), Type::Constructor(raw_name)),
            Identifier::Bound(0),
        );

        assert_eq!(
            context
                .lambda_capture_confinement(&Identifier::Bound(1), None, &body)
                .unwrap()
                .joined,
            Confinement::Confined
        );
        assert_eq!(
            context
                .lambda_capture_confinement(&Identifier::Bound(0), None, &body)
                .unwrap()
                .joined,
            Confinement::Unconfined
        );
    }

    #[test]
    fn unconfined_type_ascription_rejects_a_confined_leaf() {
        let raw_name = name("Raw_Buffer");
        let raw_symbol = TypeSymbol {
            definition: TypeDefinition::Coproduct(CoproductSymbol {
                name: raw_name.clone(),
                type_parameters: vec![],
                constructors: vec![],
            }),
            origin: namer::TypeOrigin::Foreign,
            opacity: namer::Access::Within(parser::IdentifierPath::new("Test")),
            arity: 0,
            kind: Kind::confined(),
        };
        let mut context = TypingContext::default();
        context
            .types
            .bind(raw_name.clone(), TypeConstructor::from_symbol(&raw_symbol));
        let expression = TypeExpression::ConfinementAscription(
            ParseInfo::default(),
            TypeExpression::Constructor(ParseInfo::default(), raw_name).into(),
            ast::ConfinementModifier::Unconfined,
        );

        let error = expression
            .synthesize_type(&HashMap::new(), &context)
            .unwrap_err()
            .to_string();
        assert!(
            error.contains("cannot unify confined with unconfined"),
            "{error}"
        );
    }

    #[test]
    fn unconfined_type_variable_cannot_bind_a_confined_type() {
        let raw_name = name("Raw_Buffer");
        let raw_symbol = TypeSymbol {
            definition: TypeDefinition::Coproduct(CoproductSymbol {
                name: raw_name.clone(),
                type_parameters: vec![],
                constructors: vec![],
            }),
            origin: namer::TypeOrigin::Foreign,
            opacity: namer::Access::Within(parser::IdentifierPath::new("Test")),
            arity: 0,
            kind: Kind::confined(),
        };
        let mut context = TypingContext::default();
        context
            .types
            .bind(raw_name.clone(), TypeConstructor::from_symbol(&raw_symbol));

        let error = Type::fresh_with_kind(Kind::unconfined())
            .unified_with(&Type::Constructor(raw_name), &context.types)
            .unwrap_err()
            .to_string();

        assert_eq!(
            error,
            "type `Test.Raw_Buffer` is confined, but this context requires unconfined"
        );
    }
}
