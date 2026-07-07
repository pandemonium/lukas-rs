use std::{
    collections::{BTreeSet, HashMap, HashSet},
    fmt,
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
        self, Apply, ApplyTypeExpr, ArrowTypeExpr, Binding, ConstraintExpression, Deconstruct,
        IfThenElse, Injection, Kind, Lambda, Literal, ProductElement, Projection, Record, Segment,
        SelfReferential, Sequence, Tree, Tuple, TupleTypeExpr, TypeAscription, TypeExpression,
        annotation::Annotated,
        constraints::{Witness, WitnessEnvironment},
        namer::{
            self, CoproductSymbol, DependencyMatrix, Identifier, Named, QualifiedName,
            RecordSymbol, Symbol, SymbolName, TermSymbol, TypeDefinition, TypeSymbol,
        },
        pattern::{
            ConstructorPattern, Denotation, MatchClause, Pattern, Shape, StructPattern,
            TuplePattern,
        },
    },
    compiler::{Located, LocatedError},
    parser::{self, IdentifierPath, ParseInfo, Parsed},
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
                        && let TypeDefinition::Record(symbol) = &symbol.definition
                    {
                        Some(symbol)
                    } else {
                        None
                    }
                })
                .expect("Internal error");
            let semantic_context = constraint_name.module();

            for method in &constraint.fields {
                let name = QualifiedName::new(semantic_context.clone(), method.name.as_str());
                matrix.add_edge(SymbolName::Term(name), vec![]);
            }
        }

        for external in &self.externals {
            matrix.add_edge(SymbolName::Term(external.name.clone()), vec![]);
        }

        matrix
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

        let quantifiers = type_params.iter().map(|(_, p)| p.clone()).collect();

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

        Ok(TypeScheme {
            quantifiers,
            underlying: self.body.synthesize_type(&type_param_map, ctx)?,
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

impl phase::SymbolTable<Named> {
    pub fn elaborate_compilation_unit(mut self) -> Typing<phase::SymbolTable<Types>> {
        let mut ctx = self.elaborate_types()?;

        self.elaborate_externals(&mut ctx)?;

        // Gives rise to signature method placeholders -- term typer needs this
        let selectors_names = self.elaborate_constraints(&mut ctx)?;

        // This runs the term typer core
        let symbols =
            self.elaborate_terms(&selectors_names.iter().collect::<Vec<_>>(), &mut ctx)?;

        Ok(SymbolTable {
            module_members: self.module_members,
            member_modules: self.member_modules,
            symbols,
            imports: self.imports,
            externals: self.externals,
            signatures: self.signatures,
            witnesses: self.witnesses,
        })
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

            // this has to bind every term in TypingContext so that later elaborations
            // can discover constraints (type and order)
            // So it needs the name!
            let expr = elaborate_term_constraints(
                &symbol.name,
                &witnesses,
                term.constraints,
                term.tree,
                ctx,
            )
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
                typed_terms.push((symbol, self.type_term(symbol, ctx)?))
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

    fn elaborate_types(&self) -> Typing<TypingContext> {
        let mut ctx = TypingContext::default();

        for symbol in self.symbols.iter().filter_map(|(_, sym)| match sym {
            Symbol::Type(symbol) => Some(symbol),
            _ => None,
        }) {
            ctx.bind_type(
                symbol.qualified_name().clone(),
                TypeConstructor::from_symbol(symbol),
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
                && let TypeDefinition::Record(record) = &tc.definition().defining_symbol.definition
            {
                for field in &record.fields {
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

            if let TypeDefinition::Record(record) =
                &mut type_constructor.definition_mut().defining_symbol.definition
            {
                for field in &mut record.fields {
                    let pi = *field.type_signature.body.annotation();
                    let mut c = signature_constraint.clone();
                    c.annotation = pi;

                    field.type_signature.desugar_constraints();
                }
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

            if let TypeDefinition::Record(record) =
                &type_constructor.definition().defining_symbol.definition
            {
                for field in record.fields.iter() {
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
                for (method_id, scheme) in record_type.fields() {
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

        let expr = ctx.infer_expr(&symbol.body)?;
        let qualified_name = symbol.name.clone();

        let scheme = if let Some(signature) = &symbol.type_signature {
            signature.type_scheme(&HashMap::default(), ctx)?
        } else {
            let inferred_type = &expr.as_constrained_type();
            inferred_type.generalize(ctx).underlying
        };

        tracing::trace!(">>> {} :: {}", qualified_name, scheme);
        ctx.bind_free_term(qualified_name.clone(), scheme.clone());

        Ok(expr)
    }

    pub fn elaborate_externals(&self, ctx: &mut TypingContext) -> Typing<()> {
        for ext in &self.externals {
            let type_scheme = ext.type_signature.type_scheme(&HashMap::default(), ctx)?;
            ctx.bind_free_term(ext.name.clone(), type_scheme);
        }
        Ok(())
    }
}

#[instrument(skip_all)]
fn elaborate_term_constraints(
    symbol_name: &QualifiedName,
    witnesses: &WitnessEnvironment,
    constraints: ConstraintSet,
    tree: ast::Expr<TypeInfo, Identifier>,
    ctx: &mut TypingContext,
) -> Result<ast::Expr<TypeInfo, Identifier>, TypeError> {
    tracing::trace!("{symbol_name} has {constraints} tree {tree}");

    let selectors = SelectorTable::from_constraints(&constraints, &ctx.types)?;

    Ok(resolve_constraints(
        symbol_name,
        tree,
        constraints,
        witnesses,
        ctx,
    )?)
}

#[instrument(skip_all)]
fn resolve_constraints(
    symbol_name: &QualifiedName,
    mut tree: Expr,
    constraints: ConstraintSet,
    witnesses: &WitnessEnvironment,
    ctx: &mut TypingContext,
) -> Result<Expr, TypeError> {
    let is_constrained = !constraints.is_empty();

    // Variable-headed constraints (e.g. `Eq α`) can never be matched by an
    // instance, so they must become dictionary parameters. Everything else --
    // ground constraints (`Eq Int`) and constructor-headed constraints
    // (`Eq (List α)`) -- is discharged by an instance, whose own premises are in
    // turn satisfied by those parameters.
    let (parametric, resolvable) = constraints
        .clone()
        .into_iter()
        .partition::<Vec<_>, _>(|c| c.is_parametric());

    tracing::trace!(
        "{symbol_name} parametric: {:?} resolvable {:?}",
        &parametric,
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
                constraints: ConstraintSet::from(parametric.as_slice()),
                underlying: tree.type_info().inferred_type.clone(),
            }
            .generalize(ctx)
            .underlying,
        );
    }

    let mut evidence = HashMap::new();

    // Bind a dictionary parameter (#1, #2, ...) for each variable-headed
    // constraint. `add_dictionary_parameter_slot` always yields a
    // self-referential tree -- `own_name` at slot #0 and parameters from #1 --
    // both when prepending to an existing lambda and when wrapping a non-lambda
    // body (e.g. a witness whose body is a record), so the i-th parameter is at
    // #(1 + i).
    for (i, c) in parametric.iter().enumerate() {
        let name = Identifier::Bound(1 + i);
        tracing::trace!("binding {name} to {}", c.constraint_type);

        tree = add_dictionary_parameter_slot(&tree);

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

            if let Some(type_scheme) = ctx.terms.lookup(&term_id)
                && !type_scheme.constraints.is_empty()
            {
                let use_site_type = type_scheme.instantiate();

                tracing::trace!("scheme {use_site_type} type {}", type_info.inferred_type);

                let use_site_subst = use_site_type
                    .underlying
                    .unified_with(&type_info.inferred_type, &ctx.types)
                    .expect("expr.typed");
                let use_site_constraints = use_site_type.constraints.apply(&use_site_subst);

                let is_injection_site = use_site_constraints
                    .iter()
                    .any(|c| evidence.contains_key(c));

                if is_injection_site {
                    //tracing::trace!("{method_name} ")

                    use_site_constraints.iter().fold(
                        Expr::Variable(type_info.clone(), term_id.clone()),
                        |f, c| {
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

struct SelectorTable<'a>(HashMap<parser::Identifier, Vec<&'a Constraint>>);

impl<'a> SelectorTable<'a> {
    fn from_constraints(set: &'a ConstraintSet, ctx: &TypeEnvironment) -> Result<Self, TypeError> {
        let mut constraint_signatures = HashMap::<_, Vec<_>>::new();

        for c in set.iter() {
            let signature = c.signature(&ctx)?;
            for method in signature.vtable.into_vec() {
                constraint_signatures.entry(method).or_default().push(c);
            }
        }

        Ok(Self(constraint_signatures))
    }

    // This could give an iterator instead
    fn selector_names(&self, placeholder: &QualifiedName) -> Vec<(&Constraint, QualifiedName)> {
        let candidates = self.0.get(placeholder.member()).unwrap_or(&vec![]);

        todo!()
    }
}

#[instrument(skip_all)]
fn elaborate_constraint_method_placeholders(
    tree: Expr,
    evidence: &ConstraintSet,
    ctx: &TypingContext,
) -> Expr {
    let mut constraint_signatures = HashMap::new();
    for c in evidence.iter() {
        let signature = c.signature(&ctx.types).expect("expr.typed");
        for method in signature.vtable.into_vec() {
            constraint_signatures.insert(method, c);
        }
    }

    // What if this function resolves the type scheme of the selector method name
    // it names?

    tree.map(&mut |e| match e {
        Expr::Variable(type_info, ref term_id @ Identifier::Free(ref method_name))
            if constraint_signatures.contains_key(method_name.member()) =>
        {
            let constraint = constraint_signatures[method_name.member()];
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

fn add_dictionary_parameter_slot(expr: &Expr) -> Expr {
    if let Expr::Ascription(a0, ascription) = expr {
        match ascription.ascribed_tree.as_ref() {
            Expr::RecursiveLambda(a1, rec) => Expr::Ascription(
                a0.clone(),
                TypeAscription {
                    ascribed_tree: Expr::RecursiveLambda(
                        a1.clone(),
                        SelfReferential {
                            own_name: rec.own_name.clone(),
                            lambda: rec.lambda.clone().prepend_parameter().clone(),
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
                        a0.clone(),
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
                a1.clone(),
                SelfReferential {
                    own_name: rec.own_name.clone(),
                    lambda: rec.lambda.clone().prepend_parameter().clone(),
                },
            ),

            other => Expr::RecursiveLambda(
                other.annotation().clone(),
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
    fn prepend_parameter(self) -> Self {
        let Identifier::Bound(first_level) = self.parameter else {
            panic!("expected locally bound")
        };

        Lambda {
            parameter: Identifier::Bound(first_level),
            body: Expr::Lambda(
                self.body.annotation().clone(),
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
        "bad projection\nfrom type: {inferred_base_type}\n{} does not have a member: {}",
        projection.base, projection.select
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

    #[error("{clause} is not useful")]
    UselessMatchClause { clause: phase::MatchClause<Types> },

    #[error("all of {} is not covered", deconstruct.scrutinee)]
    MatchNotExhaustive {
        deconstruct: phase::Deconstruct<Types>,
    },

    #[error("Bad specialization: {0}")]
    BadSpecialization(Specialization),

    #[error("expected: {expected}; found: {found}")]
    ExpectedType { expected: Type, found: Type },

    #[error("{from} is not {expected}")]
    Disappointed { expected: Type, from: namer::Expr },

    #[error("undefined constraint signature {0}")]
    UndefinedSignature(QualifiedName),

    #[error("no witness found for constraint {0}")]
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
        "record shape missmatch, missing: {} (and superfluous: {}).",
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
}

impl TypeInfo {
    pub fn new(parse_info: ParseInfo, inferred_type: Type) -> Self {
        Self {
            parse_info,
            inferred_type,
        }
    }

    pub fn apply(&self, subs: &Substitutions) -> Self {
        Self {
            parse_info: self.parse_info,
            inferred_type: self.inferred_type.apply(subs),
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

    fn map_tree<F>(self, f: &mut F) -> Self
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
    fn len(&self) -> usize {
        self.0.len()
    }

    fn contains(&self, constraint: &Constraint) -> bool {
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
            _otherwise => todo!(),
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

    fn is_ground(&self) -> bool {
        let variables = self.variables();
        variables.is_empty()
    }

    /// A constraint whose constrained type is a bare type variable (e.g. `Eq α`).
    /// No instance can ever match a bare variable, so such a constraint must be
    /// discharged by a dictionary *parameter*. Every other constraint -- ground
    /// (`Eq Int`) or constructor-headed (`Eq (List α)`) -- is discharged by an
    /// instance instead, with that instance's own premises satisfied by the
    /// parameters.
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
    fn from_constructors(constructors: &[(QualifiedName, Vec<Type>)]) -> Self {
        let mut constructors = constructors.to_vec();
        constructors.sort_by(|(t, _), (u, _)| t.cmp(u));

        Self(constructors)
    }

    fn cardinality(&self) -> usize {
        self.0.len()
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
            Kind::Arrow(k1, k2) if *k1 == at => Ok(*k2),
            otherwise => Err(TypeError::KindMismatchError {
                function: otherwise,
                argument: at,
            }),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Type {
    Variable(MetaVariable),
    Base(BaseType),
    Arrow {
        domain: Box<Type>,
        codomain: Box<Type>,
    },
    Tuple(TupleType),
    Record(RecordType),
    // Could this be used as the backing for Opaque types? A zero arity coproduct
    Coproduct(CoproductType),
    Constructor(namer::QualifiedName),
    Apply {
        constructor: Box<Type>,
        argument: Box<Type>,
    },
}

impl Type {
    pub fn kind(&self, ctx: &TypeEnvironment) -> Result<Kind, TypeError> {
        match self {
            Self::Variable(tp) => Ok(tp.kind().clone()),
            Self::Base(..) => Ok(Kind::Star),
            Self::Arrow { .. } => Ok(Kind::Star),
            Self::Tuple(..) => Ok(Kind::Star),
            Self::Record(..) => Ok(Kind::Star),
            Self::Coproduct(..) => Ok(Kind::Star),
            Self::Constructor(name) => ctx
                .lookup(name)
                .ok_or_else(|| TypeError::UndefinedType(name.clone()))
                .map(|tc| tc.kind())
                .cloned(),
            Self::Apply {
                constructor,
                argument,
            } => {
                let k1 = constructor.kind(ctx)?;
                let k2 = argument.kind(ctx)?;
                k1.apply(k2)
            }
        }
    }

    pub fn reify(&self, type_param_map: &[parser::Identifier]) -> phase::TypeExpression<Parsed> {
        let pi = ParseInfo::default();

        let reified_name =
            |qn: &QualifiedName| IdentifierPath::new(&qn.clone().into_identifier_path().tail[0]);

        match self {
            Self::Variable(MetaVariable(p, _)) => {
                TypeExpression::Parameter(pi, type_param_map[*p as usize].clone())
            }
            Self::Base(BaseType::Int) => {
                TypeExpression::Constructor(pi, IdentifierPath::new("Int"))
            }
            Self::Base(BaseType::Text) => {
                TypeExpression::Constructor(pi, IdentifierPath::new("Text"))
            }
            Self::Base(BaseType::Bool) => {
                TypeExpression::Constructor(pi, IdentifierPath::new("Bool"))
            }
            Self::Base(BaseType::Unit) => {
                TypeExpression::Constructor(pi, IdentifierPath::new("Unit"))
            }
            Self::Base(BaseType::Char) => {
                TypeExpression::Constructor(pi, IdentifierPath::new("Char"))
            }
            Self::Arrow { domain, codomain } => TypeExpression::Arrow(
                pi,
                ArrowTypeExpr {
                    domain: domain.reify(type_param_map).into(),
                    codomain: codomain.reify(type_param_map).into(),
                },
            ),
            Self::Tuple(..) => todo!(),
            Self::Record(..) => todo!(),
            Self::Coproduct(..) => todo!(),
            Self::Constructor(qualified_name) => {
                TypeExpression::Constructor(pi, reified_name(qualified_name))
            }
            Self::Apply {
                constructor,
                argument,
            } => TypeExpression::Apply(
                pi,
                ApplyTypeExpr {
                    function: constructor.reify(type_param_map).into(),
                    argument: argument.reify(type_param_map).into(),
                    phase: PhantomData,
                },
            ),
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
            Self::Arrow { domain, codomain } => {
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
                loop {
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
                }
            }

            Self::Base(b) => Self::Base(*b),

            Self::Arrow { domain, codomain } => Self::Arrow {
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

            Self::Constructor(..) => self.clone(),

            Self::Apply {
                constructor,
                argument,
            } => Self::Apply {
                constructor: constructor.apply(subs).into(),
                argument: argument.apply(subs).into(),
            },
        }
    }

    pub fn unified_with(
        &self,
        rhs: &Self,
        ctx: &TypeEnvironment,
    ) -> Result<Substitutions, TypeError> {
        let lhs_kind = self.kind(ctx)?;
        let rhs_kind = rhs.kind(ctx)?;
        if lhs_kind != rhs_kind {
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
                    Ok(vec![(p.clone(), ty.clone())].into())
                }
            }

            (
                Self::Arrow {
                    domain: lhs_dom,
                    codomain: lhs_codom,
                },
                Self::Arrow {
                    domain: rhs_dom,
                    codomain: rhs_codom,
                },
            ) => {
                let domain = lhs_dom.unified_with(rhs_dom, ctx)?;
                let codomain = lhs_codom
                    .apply(&domain)
                    .unified_with(
                        &rhs_codom.apply(&domain), ctx
                    )?;
                Ok(domain.compose(&codomain))
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

            (Self::Coproduct(lhs), Self::Coproduct(rhs))
                if lhs.cardinality() == rhs.cardinality() /*&& {
                    let rhs_names = rhs.constructor_names().collect::<HashSet<_>>();
                    lhs.constructor_names().all(|lhs| rhs_names.contains(lhs))
                }*/ =>
            {
                // What in the flightrecorder?
                // I never unify Coproducts?! Or is it that I never unify expanded types?
                todo!()
            }

            (
                Self::Apply {
                    constructor: lhs_con,
                    argument: lhs_arg,
                },
                Self::Apply {
                    constructor: rhs_con,
                    argument: rhs_arg,
                },
            ) => {
                let constructor = lhs_con.unified_with(rhs_con, ctx)?;
                let argument = lhs_arg.apply(&constructor).unified_with(&rhs_arg.apply(&constructor), ctx)?;
                Ok(constructor.compose(&argument))
            }

            (lhs, rhs) => {
//                panic!("{lhs} != {rhs}");
                //panic!("unification failed: lhs {lhs} rhs {rhs}");
                Err(TypeError::UnificationImpossible { lhs: lhs.clone(), rhs: rhs.clone() })
            },
        }
    }
}

#[derive(Copy, Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum BaseType {
    Int,
    Text,
    Bool,
    Unit,
    Char,
}

impl BaseType {
    const fn local_name(&self) -> &str {
        match self {
            Self::Int => "Int",
            Self::Text => "Text",
            Self::Bool => "Bool",
            Self::Unit => "Unit",
            Self::Char => "Char",
        }
    }

    pub fn qualified_name(&self) -> namer::QualifiedName {
        namer::QualifiedName::builtin(self.local_name())
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
            ) => Ok(Type::Apply {
                constructor: function.synthesize_type(type_params, ctx)?.into(),
                argument: argument.synthesize_type(type_params, ctx)?.into(),
            }),

            Self::Arrow(_, ast::ArrowTypeExpr { domain, codomain }) => Ok(Type::Arrow {
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
}

impl TypeConstructorDefinition {
    fn make_spine(&self) -> Type {
        self.make_spine_at(&self.instantiated_params)
    }

    pub fn make_spine_at(
        &self,
        type_parameters: &HashMap<parser::Identifier, MetaVariable>,
    ) -> Type {
        self.defining_symbol.type_parameters().iter().fold(
            Type::Constructor(self.name.clone()),
            |constructor, param| Type::Apply {
                constructor: constructor.into(),
                argument: Type::Variable(type_parameters[&param.name].clone()).into(),
            },
        )
    }

    fn make_spine_expr(&self) -> phase::TypeExpression<Named> {
        let pi = ParseInfo::default();
        self.defining_symbol.type_parameters().iter().fold(
            ast::TypeExpression::Constructor(pi, self.name.clone()),
            |constructor, param| {
                ast::TypeExpression::Apply(
                    pi,
                    ApplyTypeExpr {
                        function: constructor.into(),
                        argument: ast::TypeExpression::Parameter(pi, param.name.clone()).into(),
                        phase: PhantomData,
                    },
                )
            },
        )
    }

    pub fn apply_at(&self, arguments: &[Type]) -> Type {
        arguments.iter().fold(
            Type::Constructor(self.name.clone()),
            |constructor, argument| Type::Apply {
                constructor: constructor.into(),
                argument: argument.clone().into(),
            },
        )
    }

    fn as_base_type(&self) -> Option<Type> {
        if let TypeDefinition::Builtin(base_type) = self.defining_symbol.definition {
            Some(Type::Base(base_type))
        } else {
            None
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
        if let TypeDefinition::Builtin(base_type) = &symbol.definition {
            Self::Elaborated(ElaboratedTypeConstructor {
                definition: TypeConstructorDefinition {
                    name: symbol.qualified_name(),
                    instantiated_params: HashMap::default(),
                    defining_symbol: symbol.clone(),
                },
                structure: TypeStructure::Monotype(Type::Base(*base_type)),
            })
        } else {
            Self::Unelaborated(TypeConstructorDefinition {
                name: symbol.qualified_name(),
                instantiated_params: fresh_type_parameters(symbol),
                defining_symbol: symbol.clone(),
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
    Ok(TypeConstructor::Elaborated(ElaboratedTypeConstructor {
        definition: definition.clone(),
        structure: definition
            .defining_symbol
            .definition
            .synthesize_type(&definition.instantiated_params, ctx)?,
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
            Self::Coproduct(coproduct) => Ok(TypeStructure::Monotype(
                coproduct.synthesize_type(type_param_map, ctx)?,
            )),
            Self::Builtin(base_type) => Ok(TypeStructure::Monotype(Type::Base(*base_type))),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeScheme {
    pub quantifiers: Vec<MetaVariable>,
    pub underlying: Type,
    pub constraints: ConstraintSet,
}

impl TypeScheme {
    pub fn apply(&self, subst: &Substitutions) -> Self {
        let mut subst = subst.clone();
        for q in &self.quantifiers {
            subst.remove(q);
        }
        Self {
            quantifiers: self.quantifiers.clone(),
            underlying: self.underlying.apply(&subst),
            constraints: self.constraints.apply(&subst),
        }
    }

    fn instantiation_substitutions(&self) -> Substitutions {
        self.quantifiers
            .iter()
            .map(|tp| (tp.clone(), Type::fresh_with_kind(tp.kind().clone())))
            .collect::<Vec<_>>()
            .into()
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
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
}

//pub struct Substitutions(Vec<(TypeParamter, Type)>);
#[derive(Debug, Default, Clone)]
pub struct Substitutions(Vec<(MetaVariable, Type)>);

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

        Substitutions(out)
    }

    fn remove(&mut self, param: &MetaVariable) {
        self.0.retain(|(tp, ..)| param != tp);
    }
}

impl fmt::Display for Substitutions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self(subs) = self;
        let mut subs = subs.iter();
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
        Self(value)
    }
}

impl Deref for Substitutions {
    type Target = [(MetaVariable, Type)];

    fn deref(&self) -> &Self::Target {
        &self.0
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
        if let Type::Constructor { .. } | Type::Apply { .. } = ty {
            self.reduce_applied_constructor(pi, ty, &mut vec![])
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
                let subs = Substitutions::from(
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

                Ok(constructor.structure()?.apply(&subs))
            }

            Type::Apply {
                constructor,
                argument,
            } => {
                arguments.push(*argument.clone());
                self.reduce_applied_constructor(pi, constructor, arguments)
            }

            _ => {
                tracing::trace!("fallback with {applied}");
                // The head isn't a reducible named constructor (e.g. a type
                // variable `f` in `f α`, or an otherwise-neutral head). Rebuild
                // the applied spine from the arguments we peeled off on the way
                // down — otherwise `f α` collapses to just `f`, dropping `α` and
                // mis-binding pattern variables at a truncated (mis-kinded) type.
                arguments.reverse();
                let ty = arguments
                    .drain(..)
                    .fold(applied.clone(), |constructor, argument| Type::Apply {
                        constructor: constructor.into(),
                        argument: argument.into(),
                    });
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

        if let TypeStructure::Monotype(Type::Arrow { domain, codomain }) = &normalized_type {
            self.bind_term_and_then(
                rec.own_name.clone(),
                TypeScheme::from_constant(expected_type.clone()),
                |ctx| {
                    ctx.bind_term_and_then(
                        rec.lambda.parameter.clone(),
                        TypeScheme::from_constant(*domain.clone()),
                        |ctx| {
                            let typed_body = ctx.check_expr(codomain, &rec.lambda.body)?;

                            let type_info = pi.with_inferred_type(
                                expected_type.apply(&typed_body.substitutions).clone(),
                            );
                            Ok(Typed::computed(
                                typed_body.substitutions,
                                typed_body.constraints,
                                Expr::RecursiveLambda(
                                    type_info,
                                    SelfReferential {
                                        own_name: rec.own_name.clone(),
                                        lambda: Lambda {
                                            parameter: rec.lambda.parameter.clone(),
                                            body: typed_body.tree.into(),
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

        if let TypeStructure::Monotype(Type::Arrow { domain, codomain }) = &normalized_type {
            self.bind_term_and_then(
                lambda.parameter.clone(),
                TypeScheme::from_constant(*domain.clone()),
                |ctx| {
                    let body = ctx.check_expr(codomain, &lambda.body)?;

                    ctx.substitute_mut(&body.substitutions);

                    let type_info = pi.with_inferred_type(expected_type.apply(&body.substitutions));
                    Ok(Typed::computed(
                        body.substitutions,
                        body.constraints,
                        Expr::Lambda(
                            type_info,
                            Lambda {
                                parameter: lambda.parameter.clone(),
                                body: body.tree.into(),
                            },
                        ),
                    ))
                },
            )
        } else {
            panic!("{normalized_type:?}")
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
                let inferred_type = bridge.external.type_scheme().instantiate();

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
                //                self.infer_apply_with_arg_check(*pi, function, argument)
                self.infer_apply(*pi, function, argument)
            }

            UntypedExpr::Let(pi, binding) => self.infer_binding(*pi, binding),

            UntypedExpr::Record(pi, record) => self.infer_record(*pi, record),

            UntypedExpr::Tuple(pi, tuple) => self.infer_tuple(*pi, tuple),

            UntypedExpr::Inject(pi, constructor) => self.infer_inject(*pi, constructor),

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
                pi.with_inferred_type(Type::Base(BaseType::Text)),
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

        if !space.is_exhaustive(pi, &scrutinee_type.apply(&substitutions), self)? {
            Err(TypeError::MatchNotExhaustive {
                deconstruct: Deconstruct {
                    scrutinee: scrutinee.into(),
                    match_clauses: typed_match_clauses,
                },
            }
            .at(pi))
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

        if !match_space.is_exhaustive(pi, &scrutinee.type_info().inferred_type, self)? {
            Err(TypeError::MatchNotExhaustive {
                deconstruct: Deconstruct {
                    scrutinee: scrutinee.clone().into(),
                    match_clauses: clauses.clone(),
                },
            }
            .at(pi))
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
                if let namer::Identifier::Free(constructor) = &pattern.constructor
                    && let Some(signature) = coproduct.signature(constructor)
                    && pattern.arguments.len() == signature.len()
                {
                    let mut arguments = Vec::with_capacity(signature.len());
                    let mut substitutions = Substitutions::default();

                    for (scrutinee, pattern) in signature.iter().zip(&pattern.arguments) {
                        let (subs, argument) = self.check_pattern(
                            pattern,
                            bindings,
                            &scrutinee.apply(&substitutions),
                        )?;
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
                } else {
                    panic!("Bad coproduct deconstruction")
                }
            }

            (Pattern::Tuple(pi, pattern), TypeStructure::Monotype(Type::Tuple(tuple)))
                if pattern.elements.len() == tuple.arity() =>
            {
                let mut elements = Vec::with_capacity(tuple.arity());
                let mut substitutions = Substitutions::default();

                for (pattern, scrutinee) in pattern.elements.iter().zip(tuple.elements()) {
                    let (subst, element) = self.check_pattern(pattern, bindings, scrutinee)?;
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

            (pattern, _) => {
                panic!("Type error. Illegal pattern. `{pattern}` `{normalized_scrutinee}`",)
            }
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
        let own_ty = Type::Arrow {
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
                        Ok(Typed::computed(
                            substitutions.clone(),
                            typed.constraints.apply(&substitutions),
                            Expr::RecursiveLambda(
                                pi.with_inferred_type(own_ty.apply(&substitutions)),
                                SelfReferential {
                                    own_name: rec_lambda.own_name.clone(),
                                    lambda: Lambda {
                                        parameter: rec_lambda.lambda.parameter.clone(),
                                        body: tree.into(),
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
        if let Type::Arrow { domain, codomain } = &function_type {
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
            domain: argument
                .tree
                .type_info()
                .inferred_type
                .apply(&substitutions)
                .into(),
            codomain: return_ty.clone().into(),
        };

        let substitutions = expected_ty
            .apply(&substitutions)
            .unified_with(
                &function
                    .tree
                    .type_info()
                    .inferred_type
                    .apply(&substitutions),
                &self.types,
            )
            .map_err(|e| e.at(pi))?
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

                let inferred_type = Type::Arrow {
                    domain: domain.apply(&substitutions).into(),
                    codomain: codomain.apply(&substitutions).into(),
                };

                let body = body.apply(&substitutions);

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
    fn infer_binding(&mut self, pi: ParseInfo, binding: &phase::Binding<Named>) -> Typing {
        let typed_bound = self.infer_expr(&binding.bound)?;
        let ctx1 = self.apply(&typed_bound.substitutions);

        let bound_type = typed_bound.as_constrained_type().generalize(&ctx1);

        self.bind_term_and_then(binding.binder.clone(), bound_type.underlying, |ctx| {
            let typed_body = ctx.infer_expr(&binding.body)?;

            let substitutions = typed_bound.substitutions.compose(&typed_body.substitutions);

            let bound = typed_bound.tree.apply(&substitutions);
            let body = typed_body.tree.apply(&substitutions);
            let constraints = typed_bound
                .constraints
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
}

impl Literal {
    fn synthesize_type(&self) -> Type {
        Type::Base(match self {
            Self::Int(..) => BaseType::Int,
            Self::Text(..) => BaseType::Text,
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
        }
    }
}

// todo: move to pattern.rs
impl Denotation {
    // Instead of doing it this way, I could have used a denotation directed
    // universe creator
    fn covers(&self, pi: ParseInfo, scrutinee: &Type, ctx: &TypingContext) -> Typing<bool> {
        match self {
            Self::Structured(shape) => shape.covers(pi, scrutinee, ctx),

            Self::Universal => Ok(true),

            Self::Empty | Self::Finite(..) => Ok(false),
        }
    }
}

// todo: move to pattern.rs
impl Shape {
    fn covers(&self, pi: ParseInfo, scrutinee: &Type, ctx: &TypingContext) -> Typing<bool> {
        let scrutinee = ctx
            .expand_type_constructor(pi, scrutinee)?
            .unwrap_or_else(|| TypeStructure::Monotype(scrutinee.clone()));

        match (self, scrutinee) {
            (
                Self::Coproduct(denotations),
                TypeStructure::Monotype(Type::Coproduct(CoproductType(constructors))),
            ) => {
                let mut covers = true;

                'outer: for (constructor, arguments) in constructors {
                    if !denotations.contains_key(&constructor) {
                        covers = false;
                        break;
                    }

                    for (denotation, scrutinee) in denotations[&constructor].iter().zip(arguments) {
                        covers &= denotation.covers(pi, &scrutinee, ctx)?;
                        if !covers {
                            break 'outer;
                        }
                    }
                }

                Ok(covers)
            }

            (Self::Struct(denotations), TypeStructure::PolyRecord(record_type)) => {
                let mut covers = true;
                for (field, scrutinee) in record_type.fields() {
                    let scrutinee = scrutinee.instantiate();
                    covers &= denotations[field].covers(pi, &scrutinee.underlying, ctx)?;
                    if !covers {
                        break;
                    }
                }

                Ok(covers)
            }

            (Self::Tuple(denotations), TypeStructure::Monotype(Type::Tuple(TupleType(types)))) => {
                let mut covers = true;
                for (denotation, scrutinee) in denotations.iter().zip(types) {
                    //let scrutinee = ctx.expand_type_constructor(pi, &scrutinee)?;
                    covers &= denotation.covers(pi, &scrutinee, ctx)?;
                    if !covers {
                        break;
                    }
                }
                Ok(covers)
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
    pub fn is_exhaustive(
        &self,
        pi: ParseInfo,
        scrutinee: &Type,
        ctx: &TypingContext,
    ) -> Typing<bool> {
        self.covered.normalize().covers(pi, scrutinee, ctx)
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
        write!(f, "{parse_info}: {error}")
    }
}

impl fmt::Display for TypeInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            parse_info,
            inferred_type,
        } = self;
        write!(f, "{{{parse_info}:{inferred_type}}}")
    }
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Kind::Star => write!(f, "*"),
            Kind::Arrow(k1, k2) => write!(f, "{k1} -> {k2}"),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Variable(MetaVariable(p, k)) => write!(f, "${p}:{k}"),

            Self::Base(base_type) => write!(f, "{base_type}"),

            Self::Arrow { domain, codomain } => write!(f, "({domain} -> {codomain})"),

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

            Self::Constructor(name) => write!(f, "{name}"),

            Self::Apply {
                constructor,
                argument,
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
            Self::Text => write!(f, "Text"),
            Self::Bool => write!(f, "Bool"),
            Self::Unit => write!(f, "Unit"),
            Self::Char => write!(f, "Char"),
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
