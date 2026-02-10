use std::{
    collections::{BTreeSet, HashMap, HashSet},
    fmt,
    marker::PhantomData,
    ops::Deref,
    rc::Rc,
    slice::Iter,
    sync::atomic::{AtomicU32, Ordering},
    vec,
};

use thiserror::Error;
use tracing::{instrument, trace};

use crate::{
    ast::{
        self, ApplyTypeExpr, ArrowTypeExpr, Literal, ProductElement, Tree, TupleTypeExpr,
        annotation::Annotated,
        constraints::{Witness, WitnessIndex},
        namer::{
            self, DependencyMatrix, Identifier, QualifiedName, Symbol, SymbolName, SymbolTable,
            TermSymbol, TypeDefinition, TypeExpression, TypeSymbol,
        },
        pattern::{Denotation, Shape},
    },
    compiler::{Located, LocatedError},
    parser::{self, ParseInfo},
};

type UntypedExpr = namer::Expr;
pub type Expr = ast::Expr<TypeInfo, namer::Identifier>;
pub type TypedTree = Rc<Expr>;
pub type Apply = ast::Apply<TypeInfo, namer::Identifier>;
pub type SelfReferential = ast::SelfReferential<TypeInfo, namer::Identifier>;
pub type Lambda = ast::Lambda<TypeInfo, namer::Identifier>;
pub type Binding = ast::Binding<TypeInfo, namer::Identifier>;
pub type Tuple = ast::Tuple<TypeInfo, namer::Identifier>;
pub type Construct = ast::Construct<TypeInfo, namer::Identifier>;
pub type Record = ast::Record<TypeInfo, namer::Identifier>;
pub type Projection = ast::Projection<TypeInfo, namer::Identifier>;
pub type Sequence = ast::Sequence<TypeInfo, namer::Identifier>;
pub type Deconstruct = ast::Deconstruct<TypeInfo, namer::Identifier>;
pub type IfThenElse = ast::IfThenElse<TypeInfo, namer::Identifier>;
pub type Interpolate = ast::Interpolate<TypeInfo, namer::Identifier>;
pub type Segment = ast::Segment<TypeInfo, namer::Identifier>;
pub type MatchClause = ast::pattern::MatchClause<TypeInfo, namer::Identifier>;
pub type Pattern = ast::pattern::Pattern<TypeInfo, namer::Identifier>;
pub type ConstructorPattern = ast::pattern::ConstructorPattern<TypeInfo, namer::Identifier>;
pub type StructPattern = ast::pattern::StructPattern<TypeInfo, namer::Identifier>;
pub type TuplePattern = ast::pattern::TuplePattern<TypeInfo, namer::Identifier>;
pub type TypeAscription = ast::TypeAscription<TypeInfo, namer::Identifier>;

pub type RecordSymbol = namer::RecordSymbol<namer::QualifiedName>;
pub type CoproductSymbol = namer::CoproductSymbol<namer::QualifiedName>;

type TypedSymbol = namer::Symbol<TypeInfo, namer::QualifiedName, namer::Identifier>;
type TypedSymbolTable = namer::SymbolTable<TypeInfo, namer::QualifiedName, namer::Identifier>;

pub fn display_list<A>(sep: &str, xs: &[A]) -> String
where
    A: fmt::Display,
{
    xs.iter()
        .map(|x| x.to_string())
        .collect::<Vec<_>>()
        .join(sep)
}

impl<A> SymbolTable<A, namer::QualifiedName, namer::Identifier>
where
    A: fmt::Debug,
{
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
        for constraint_name in &self.constraints {
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

        matrix
    }
}

impl namer::TypeSignature {
    pub fn scheme(
        &self,
        type_param_map: &mut HashMap<parser::Identifier, TypeParameter>,
        ctx: &TypingContext,
    ) -> Typing<TypeScheme> {
        let type_params = self
            .universal_quantifiers
            .iter()
            .map(|id| (id.clone(), TypeParameter::fresh()))
            .collect::<Vec<_>>();

        let quantifiers = type_params.iter().map(|(_, p)| *p).collect();
        println!("scheme: quantifiers {:?}", quantifiers);

        *type_param_map = type_params.iter().cloned().collect::<HashMap<_, _>>();

        Ok(TypeScheme {
            quantifiers,
            underlying: self.body.synthesize_type(&type_param_map, ctx)?,
            constraints: ConstraintSet::default(),
        })
    }
}

impl namer::NamedSymbolTable {
    pub fn elaborate_compilation_unit(
        mut self,
        evaluation_order: Iter<&SymbolName>,
    ) -> Typing<TypedSymbolTable> {
        let mut symbols = HashMap::default();

        let mut ctx = self.elaborate_types(&mut symbols)?;
        self.elaborate_constraints(&mut ctx)?;
        self.elaborate_terms(evaluation_order, &mut symbols, ctx)?;

        Ok(SymbolTable {
            module_members: self.module_members,
            member_modules: self.member_modules,
            symbols,
            imports: self.imports,
            constraints: self.constraints,
            witnesses: self.witnesses,
        })
    }

    fn elaborate_terms(
        &self,
        evaluation_order: Iter<&SymbolName>,
        symbols: &mut HashMap<SymbolName, Symbol<TypeInfo, QualifiedName, Identifier>>,
        mut ctx: TypingContext,
    ) -> Typing<()> {
        let mut witness_index = WitnessIndex::default();

        let is_untyped = |id: &&&SymbolName| match id {
            // Some term symbols are already
            SymbolName::Type(name) => !ctx.types.bindings.contains_key(name),
            SymbolName::Term(name) => !ctx.terms.free.contains_key(name),
        };

        for (id, symbol) in evaluation_order
            .filter(is_untyped)
            .map(|&id| {
                self.symbols
                    .get(id)
                    .map(|symbol| (id, symbol))
                    // This is really an internal error
                    .ok_or_else(|| TypeError::UndefinedSymbol(id.clone()).at(ParseInfo::default()))
            })
            .collect::<Typing<Vec<_>>>()?
        {
            let symbol = match symbol {
                namer::Symbol::Term(symbol) => namer::Symbol::Term(self.elaborate_term(
                    symbol,
                    &mut witness_index,
                    &mut ctx,
                )?),
                namer::Symbol::Type(symbol) => namer::Symbol::Type(symbol.clone()),
            };

            symbols.insert(id.clone(), symbol);
        }

        Ok(())
    }

    fn elaborate_types(
        &self,
        // Wait -- types do not involve symbols?
        symbols: &mut HashMap<SymbolName, Symbol<TypeInfo, QualifiedName, Identifier>>,
    ) -> Typing<TypingContext> {
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

    fn elaborate_constraints(&mut self, ctx: &mut TypingContext) -> Typing<()> {
        self.insert_constraint_method_placeholders(ctx)?;
        Ok(())
    }

    fn insert_constraint_method_placeholders(&self, ctx: &mut TypingContext) -> Typing<()> {
        for c in &self.constraints {
            let type_constructor = ctx
                .types
                .lookup(c)
                .cloned()
                .expect("internal error: constraint name does not match type constructor.");

            let type_constructor = type_constructor.instantiate(ctx)?;
            let constraints = ConstraintSet::from(
                [Constraint::from_type_constructor(&type_constructor)].as_slice(),
            );

            if let Type::Record(RecordType(shape)) = type_constructor.structure()? {
                for (method_id, ty) in shape {
                    let scheme = Constrained {
                        constraints: constraints.clone(),
                        underlying: ty.clone(),
                    }
                    .generalize(ctx);

                    let name = QualifiedName::new(
                        type_constructor.defining_context().clone(),
                        method_id.as_str(),
                    );
                    println!("elaborate_constraints: bind {name} to {scheme}");
                    ctx.bind_free_term(name, scheme.underlying);
                }
            }
        }

        Ok(())
    }

    fn elaborate_term(
        &self,
        symbol: &TermSymbol<ParseInfo, namer::QualifiedName, Identifier>,
        witness_index: &mut WitnessIndex,
        ctx: &mut TypingContext,
    ) -> Typing<TermSymbol<TypeInfo, QualifiedName, Identifier>> {
        let mut expr = ctx.infer_expr(&symbol.body())?;
        let qualified_name = symbol.name.clone();

        expr = discharge_ground_constraints(&expr, witness_index, &ctx)?;

        let inferred_type = &expr.as_constrained_type();
        let scheme = inferred_type.generalize(&ctx);

        for c in scheme.underlying.constraints.iter() {
            expr.tree = add_constraint_parameter_slot(&expr.tree);
            expr.tree = add_constraint_projections(&expr.tree, c, &ctx)
                .map_err(|e| e.at(ParseInfo::default()))?;
        }

        ctx.bind_free_term(qualified_name.clone(), scheme.clone().underlying);

        if self.witnesses.contains(&qualified_name) {
            witness_index.insert(Witness {
                ty: scheme.underlying.underlying.clone(),
                dictionary: Expr::Variable(
                    expr.tree.type_info().clone(),
                    Identifier::Free(qualified_name.clone().into()),
                ),
            });
        }

        Ok(TermSymbol {
            name: symbol.name.clone(),
            type_signature: symbol.type_signature.clone(),
            body: expr.tree.into(),
        })
    }
}

fn discharge_ground_constraints(
    expr: &Typed,
    witness_index: &WitnessIndex,
    ctx: &TypingContext,
) -> Typing<Typed> {
    let (ground, non_ground) = expr
        .constraints
        .iter()
        .partition::<Vec<_>, _>(|c| c.is_ground());

    let mut evidence = Vec::with_capacity(ground.len());
    let pi = expr.tree.type_info().parse_info;

    for c in ground {
        let Some(witness) = witness_index.witness(c) else {
            Err(TypeError::NoWitness(c.clone())).map_err(|e| e.at(pi))?
        };

        evidence.push((c, witness));
    }

    let mut tree = expr.tree.clone();

    for (constraint, evidence) in evidence {
        let signature = constraint.signature(&ctx.types).map_err(|e| e.at(pi))?;

        tree = insert_witness(
            tree,
            &signature.shape,
            constraint,
            &evidence.dictionary,
            &ctx.terms,
        );
    }

    Ok(Typed::computed(
        expr.substitutions.clone(),
        ConstraintSet::from(non_ground.as_slice()),
        tree,
    ))
}

// A HashSet of parser::Identifier as members compared to a qualified name. Hmm.
fn insert_witness(
    tree: Expr,
    shape: &RecordShape,
    constraint: &Constraint,
    witness: &Expr,
    ctx: &TermEnvironment,
) -> Expr {
    tree.map(&|e| match e {
        Expr::Variable(a, Identifier::Free(m)) if shape.contains(m.member()) => Expr::Project(
            a,
            Projection {
                base: witness.clone().into(),
                // This must be the field index
                select: ProductElement::Ordinal(shape.index_of(&m.member()).unwrap()),
            },
        ),

        Expr::Variable(a, term_id @ Identifier::Free(..)) => {
            let scheme = ctx.lookup(&term_id).unwrap();
            println!(
                "insert_witness: {term_id} {constraint} constraints `{}`",
                scheme.constraints
            );
            if scheme
                .constraints
                .iter()
                .any(|c| c.name() == constraint.name())
            {
                Expr::Apply(
                    a.clone(),
                    Apply {
                        function: Expr::Variable(a, term_id).into(),
                        argument: witness.clone().into(),
                    },
                )
            } else {
                Expr::Variable(a, term_id)
            }
        }

        others => others.clone(),
    })
}

fn add_constraint_projections(
    tree: &Expr,
    constraint: &Constraint,
    ctx: &TypingContext,
) -> Result<Expr, TypeError> {
    let signature = constraint.signature(&ctx.types)?;

    let tree = tree.clone().map(&|e| match e {
        Expr::Variable(a, Identifier::Free(m)) if signature.shape.contains(m.member()) => {
            println!("add_constraint_projections: projecting {m} from #1");
            Expr::Project(
                a.clone(),
                Projection {
                    base: Expr::Variable(a.clone(), Identifier::Bound(1)).into(),
                    select: ProductElement::Ordinal(signature.shape.index_of(m.member()).unwrap()),
                },
            )
        }

        Expr::Variable(a, term_id @ Identifier::Free(..)) => {
            let scheme = ctx.terms.lookup(&term_id).unwrap();
            println!(
                "add_constraint_projections: {term_id} constraints {}, constraint {constraint}",
                scheme.constraints,
            );

            if scheme.constraints.contains(constraint) {
                println!("add_constraint_projections: applying #1 to {term_id}");
                Expr::Apply(
                    a.clone(),
                    Apply {
                        function: Expr::Variable(a.clone(), term_id).into(),
                        argument: Expr::Variable(a.clone(), Identifier::Bound(1)).into(),
                    },
                )
            } else {
                Expr::Variable(a, term_id)
            }
        }

        others => others.clone(),
    });

    Ok(tree)
}

fn add_constraint_parameter_slot(expr: &Expr) -> Expr {
    if let Expr::Ascription(a0, ascription) = expr
        && let Expr::RecursiveLambda(a1, rec) = &ascription.ascribed_tree.as_ref()
    {
        let lambda = rec.lambda.clone().prepend_parameter();

        Expr::Ascription(
            a0.clone(),
            TypeAscription {
                ascribed_tree: Expr::RecursiveLambda(
                    a1.clone(),
                    SelfReferential {
                        own_name: rec.own_name.clone(),
                        lambda: lambda.clone(),
                    },
                )
                .into(),
                type_signature: ascription.type_signature.clone(),
            },
        )
    } else {
        expr.clone()
    }
}

impl Lambda {
    fn prepend_parameter(self) -> Self {
        let Identifier::Bound(first_level) = self.parameter else {
            panic!("expected locally bound")
        };

        Lambda {
            parameter: Identifier::Bound(first_level),
            body: Expr::Lambda(
                self.body.type_info().clone(),
                Lambda {
                    parameter: Identifier::Bound(1 + first_level),
                    body: Rc::unwrap_or_clone(self.body)
                        .map(&|e| match e {
                            Expr::Variable(a, Identifier::Bound(l)) if l >= first_level => {
                                Expr::Variable(a.clone(), Identifier::Bound(1 + l))
                            }

                            Expr::Lambda(
                                a,
                                Lambda {
                                    parameter: Identifier::Bound(l),
                                    body,
                                },
                            ) if l >= first_level => Expr::Lambda(
                                a.clone(),
                                Lambda {
                                    parameter: Identifier::Bound(1 + l),
                                    body,
                                },
                            ),

                            Expr::Let(
                                a,
                                Binding {
                                    binder: Identifier::Bound(l),
                                    bound,
                                    body,
                                },
                            ) if l >= first_level => Expr::Let(
                                a.clone(),
                                Binding {
                                    binder: Identifier::Bound(1 + l),
                                    bound,
                                    body,
                                },
                            ),

                            Expr::Deconstruct(
                                a,
                                ast::Deconstruct {
                                    scrutinee,
                                    match_clauses,
                                },
                            ) => Expr::Deconstruct(
                                a,
                                ast::Deconstruct {
                                    scrutinee,
                                    match_clauses: match_clauses
                                        .into_iter()
                                        .map(|clause| MatchClause {
                                            pattern: clause.pattern.map_binders(&|id| match id {
                                                Identifier::Bound(l) => Identifier::Bound(1 + l),
                                                id => id,
                                            }),
                                            consequent: clause.consequent,
                                        })
                                        .collect(),
                                },
                            ),

                            e => e,
                        })
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
}

pub trait Substitutable {
    type Output;
    fn with_substitutions(&self, subs: &Substitutions) -> Self::Output;
}

impl<T> Substitutable for T
where
    T: Annotated<TypeInfo, TypeInfo, namer::Identifier, Output = T>,
{
    type Output = T::Output;
    fn with_substitutions(&self, subs: &Substitutions) -> Self::Output {
        self.map_annotation(&move |ti| ti.with_substitutions(subs))
    }
}

#[derive(Debug, Error)]
pub enum TypeError {
    #[error("cannot unify\n       left:  {lhs}\n       right: {rhs}")]
    UnificationImpossible { lhs: Type, rhs: Type },

    #[error("infinite type\ntype variable: {param}\noccurs in: {ty}")]
    InfiniteType { param: TypeParameter, ty: Type },

    #[error("bad projection\nfrom type: {projection}\nit does not have a member: {inferred_type}")]
    BadProjection {
        projection: namer::Projection,
        inferred_type: Type,
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
    UselessMatchClause { clause: MatchClause },

    #[error("all of {} is not covered", deconstruct.scrutinee)]
    MatchNotExhaustive { deconstruct: Deconstruct },

    #[error("Bad specialization: {0}")]
    BadSpecialization(Specialization),

    #[error("expected: {expected}; found: {found}")]
    ExpectedType { expected: Type, found: Type },

    #[error("undefined constraint signature {0}")]
    UndefinedSignature(QualifiedName),

    #[error("no witness found for constraint {0}")]
    NoWitness(Constraint),
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

    pub fn with_substitutions(&self, subs: &Substitutions) -> Self {
        Self {
            parse_info: self.parse_info,
            inferred_type: self.inferred_type.with_substitutions(subs),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Constrained<A> {
    constraints: ConstraintSet,
    underlying: A,
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
                quantifiers: quantifiers.iter().copied().collect(),
                underlying: self.underlying.clone(),
                constraints: ConstraintSet::from(quantified.as_slice()),
            },
        }
    }

    fn free_variables(&self, ctx: &TypingContext) -> HashSet<TypeParameter> {
        let ty_vars = self.underlying.variables();
        let ctx_bounds = ctx.free_variables();
        ty_vars.difference(&ctx_bounds).copied().collect()
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

    fn constrain(self, extra: ConstraintSet) -> Self {
        println!("constrain: {self:?} with {extra}");

        let extra = extra.with_substitutions(&self.substitutions);
        let constraints = self.constraints.union(extra);

        Self {
            substitutions: self.substitutions,
            constraints,
            tree: self.tree,
        }
    }

    fn with_substitutions(&self, subst: &Substitutions) -> Self {
        let substitutions = self.substitutions.compose(&subst);
        let constraints = self.constraints.with_substitutions(&substitutions);
        let tree = self.tree.with_substitutions(&substitutions);
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

    fn map_tree<F>(self, f: &F) -> Self
    where
        F: Fn(Expr) -> Expr,
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
    fn contains(&self, constraint: &Constraint) -> bool {
        self.0.contains(constraint)
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn with_substitutions(&self, subst: &Substitutions) -> Self {
        let Self(constraints) = self;
        Self(
            constraints
                .iter()
                .map(|c| c.with_substitutions(subst))
                .collect(),
        )
    }

    fn union(&self, ConstraintSet(rhs): ConstraintSet) -> ConstraintSet {
        let Self(lhs) = self;

        Self(lhs.union(&rhs).cloned().collect())
    }

    fn variables(&self) -> HashSet<TypeParameter> {
        self.iter().flat_map(|c| c.variables()).collect()
    }

    fn iter(&self) -> impl Iterator<Item = &Constraint> {
        self.0.iter()
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
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
    pub fn is_witness(&self, w: &Type) -> bool {
        &self.constraint_type == w
    }

    pub fn from_type_constructor(constructor: &TypeConstructor) -> Self {
        println!("from_type_constructor: {constructor}");
        Self {
            constraint_type: constructor.make_spine(),
        }
    }

    pub fn name(&self) -> &QualifiedName {
        self.constraint_type.applied_name()
    }

    fn with_substitutions(&self, subst: &Substitutions) -> Self {
        Self {
            constraint_type: self.constraint_type.with_substitutions(subst),
        }
    }

    fn variables(&self) -> HashSet<TypeParameter> {
        self.constraint_type.variables()
    }

    fn is_ground(&self) -> bool {
        self.variables().is_empty()
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

    fn with_substitutions(&self, subs: &Substitutions) -> Self {
        Self(
            self.0
                .iter()
                .map(|(id, t)| (id.clone(), t.with_substitutions(subs)))
                .collect(),
        )
    }

    fn arity(&self) -> usize {
        self.0.len()
    }

    fn fields(&self) -> &[(parser::Identifier, Type)] {
        &self.0
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

    fn with_substitutions(&self, subs: &Substitutions) -> Self {
        Self(
            self.0
                .iter()
                .map(|(id, signature)| {
                    (
                        id.clone(),
                        signature
                            .iter()
                            .map(|ty| ty.with_substitutions(subs))
                            .collect(),
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Type {
    Variable(TypeParameter),
    Base(BaseType),
    Arrow {
        domain: Box<Type>,
        codomain: Box<Type>,
    },
    Tuple(TupleType),
    Record(RecordType),
    Coproduct(CoproductType),
    Constructor(namer::QualifiedName),
    Apply {
        constructor: Box<Type>,
        argument: Box<Type>,
    },
}

impl Type {
    pub fn reify(&self, type_param_map: &[parser::Identifier]) -> parser::TypeExpression {
        let pi = ParseInfo::default();

        let reified_name = |qn: &QualifiedName| {
            parser::IdentifierPath::new(&qn.clone().into_identifier_path().tail[0])
        };

        match self {
            Self::Variable(TypeParameter(p)) => {
                parser::TypeExpression::Parameter(pi, type_param_map[*p as usize].clone())
            }
            Self::Base(BaseType::Int) => {
                parser::TypeExpression::Constructor(pi, parser::IdentifierPath::new("Int"))
            }
            Self::Base(BaseType::Text) => {
                parser::TypeExpression::Constructor(pi, parser::IdentifierPath::new("Text"))
            }
            Self::Base(BaseType::Bool) => {
                parser::TypeExpression::Constructor(pi, parser::IdentifierPath::new("Bool"))
            }
            Self::Base(BaseType::Unit) => {
                parser::TypeExpression::Constructor(pi, parser::IdentifierPath::new("Unit"))
            }
            Self::Arrow { domain, codomain } => parser::TypeExpression::Arrow(
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
                parser::TypeExpression::Constructor(pi, reified_name(qualified_name))
            }
            Self::Apply {
                constructor,
                argument,
            } => parser::TypeExpression::Apply(
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
        Self::Variable(TypeParameter::fresh())
    }

    pub fn is_base(&self) -> bool {
        matches!(self, Type::Base(..))
    }

    pub fn walk<F>(&self, f: &mut F)
    where
        F: FnMut(&Type),
    {
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

    pub fn variables(&self) -> HashSet<TypeParameter> {
        let mut vars = HashSet::default();
        self.walk(&mut |ty| {
            if let Type::Variable(tp) = ty {
                vars.insert(*tp);
            }
        });
        vars
    }

    //    #[instrument]
    pub fn with_substitutions(&self, subs: &Substitutions) -> Self {
        //trace!("{self} -- subs {subs}");

        match self {
            p @ Self::Variable(param) => subs
                .substitution(param)
                .map_or_else(
                    || p.clone(),
                    |t| {
                        if !matches!(t, Type::Variable(p2) if p2 == param) {
                            t.with_substitutions(subs)
                        } else {
                            t.clone()
                        }
                    },
                )
                .clone(),

            Self::Base(b) => Self::Base(*b),

            Self::Arrow { domain, codomain } => Self::Arrow {
                domain: domain.with_substitutions(subs).into(),
                codomain: codomain.with_substitutions(subs).into(),
            },

            Self::Tuple(tuple) => Self::Tuple(TupleType::from_signature(
                &tuple
                    .elements()
                    .iter()
                    .map(|ty| ty.with_substitutions(subs))
                    .collect::<Vec<_>>(),
            )),

            Self::Record(record) => Self::Record(record.with_substitutions(subs)),

            Self::Coproduct(coproduct) => Self::Coproduct(coproduct.with_substitutions(subs)),

            Self::Constructor(..) => self.clone(),

            Self::Apply {
                constructor,
                argument,
            } => Self::Apply {
                constructor: constructor.with_substitutions(subs).into(),
                argument: argument.with_substitutions(subs).into(),
            },
        }
    }

    pub fn unified_with(&self, rhs: &Self) -> Result<Substitutions, TypeError> {
        match (self, rhs) {
            (lhs, rhs) if lhs == rhs => Ok(Substitutions::default()),

            (Self::Variable(p), ty) | (ty, Self::Variable(p)) => {

                if matches!(ty, Type::Variable(q) if q == p) {
                    Ok(Substitutions::default())
                } else if ty.variables().contains(p) {
                    Err(TypeError::InfiniteType {
                        param: *p,
                        ty: ty.clone(),
                    })
                } else {
                    Ok(vec![(*p, ty.clone())].into())
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
                let domain = lhs_dom.unified_with(rhs_dom)?;
                let codomain = lhs_codom
                    .with_substitutions(&domain)
                    .unified_with(
                        &rhs_codom.with_substitutions(&domain)
                    )?;
                Ok(domain.compose(&codomain))
            }

            (Self::Tuple(lhs), Self::Tuple(rhs)) if lhs.arity() == rhs.arity() => {
                let mut subs = Substitutions::default();

                for (lhs, rhs) in lhs.elements().iter().zip(rhs.elements()) {
                    // compose_mut
                    subs = subs.compose(&lhs.with_substitutions(&subs).unified_with(&rhs.with_substitutions(&subs))?);
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
                    subs = subs.compose(&lhs.with_substitutions(&subs).unified_with(&rhs.with_substitutions(&subs))?);
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
                let constructor = lhs_con.unified_with(rhs_con)?;
                let argument = lhs_arg.with_substitutions(&constructor).unified_with(&rhs_arg.with_substitutions(&constructor))?;
                Ok(constructor.compose(&argument))
            }

            (lhs, rhs) => {
                //panic!("unification failed: lhs {lhs} rhs {rhs}");
                Err(TypeError::UnificationImpossible { lhs: lhs.clone(), rhs: rhs.clone() })
            },
        }
    }

    //    pub fn generalize(&self, ctx: &TypingContext) -> TypeScheme {
    //        let ty_vars = self.variables();
    //        let ctx_bounds = ctx.free_variables();
    //        let quantified = ty_vars.difference(&ctx_bounds);
    //
    //        TypeScheme {
    //            quantifiers: quantified.copied().collect(),
    //            underlying: self.clone(),
    //            constraints: ConstraintSet::default(),
    //        }
    //    }
}

const BUILTIN_BASE_TYPE_NAMES: [&str; 2] =
    [BaseType::Int.local_name(), BaseType::Text.local_name()];

#[derive(Copy, Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum BaseType {
    Int,
    Text,
    Bool,
    Unit,
}

impl BaseType {
    pub fn is_name(id: &str) -> bool {
        BUILTIN_BASE_TYPE_NAMES.contains(&id)
    }

    const fn local_name(&self) -> &str {
        match self {
            Self::Int => "Int",
            Self::Text => "Text",
            Self::Bool => "Bool",
            Self::Unit => "Unit",
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
}

impl RecordSymbol {
    fn synthesize_type(
        &self,
        type_params: &HashMap<parser::Identifier, TypeParameter>,
        ctx: &TypingContext,
    ) -> Typing<Type> {
        Ok(Type::Record(RecordType::from_fields(
            &self
                .fields
                .iter()
                .map(|field| {
                    field
                        .type_signature
                        .synthesize_type(type_params, ctx)
                        .map(|ty| (field.name.clone(), ty))
                })
                .collect::<Typing<Vec<_>>>()?,
        )))
    }
}

impl CoproductSymbol {
    pub fn synthesize_type(
        &self,
        type_params: &HashMap<parser::Identifier, TypeParameter>,
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

impl TypeExpression {
    fn synthesize_type(
        &self,
        type_params: &HashMap<parser::Identifier, TypeParameter>,
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
                .copied()
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
    pub structure: Type,
}

#[derive(Debug, Clone)]
pub struct TypeConstructorDefinition {
    pub name: namer::QualifiedName,
    pub instantiated_params: HashMap<parser::Identifier, TypeParameter>,
    pub defining_symbol: TypeSymbol<namer::QualifiedName>,
}

impl TypeConstructorDefinition {
    fn make_spine(&self) -> Type {
        self.defining_symbol.type_parameters().iter().fold(
            Type::Constructor(self.name.clone()),
            |constructor, param| Type::Apply {
                constructor: constructor.into(),
                argument: Type::Variable(self.instantiated_params[param]).into(),
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
pub enum TypeConstructor {
    Unelaborated(TypeConstructorDefinition),
    Elaborated(ElaboratedTypeConstructor),
}

impl TypeConstructor {
    fn quantifiers(&self) -> impl Iterator<Item = TypeParameter> {
        let instantiated = &self.definition().instantiated_params;
        self.definition()
            .defining_symbol
            .type_parameters()
            .iter()
            .map(|p| instantiated[p])
    }

    fn arity(&self) -> usize {
        self.definition().defining_symbol.arity
    }

    fn from_symbol(symbol: &TypeSymbol<namer::QualifiedName>) -> Self {
        if let TypeDefinition::Builtin(base_type) = &symbol.definition {
            Self::Elaborated(ElaboratedTypeConstructor {
                definition: TypeConstructorDefinition {
                    name: symbol.qualified_name(),
                    instantiated_params: HashMap::default(),
                    defining_symbol: symbol.clone(),
                },
                structure: Type::Base(*base_type),
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
            *self = Self::Elaborated(ElaboratedTypeConstructor {
                definition: constructor.clone(),
                structure: constructor
                    .defining_symbol
                    .definition
                    .synthesize_type(&constructor.instantiated_params, ctx)?,
            });
        }

        Ok(())
    }

    fn with_substitutions(&self, subs: &Substitutions) -> Self {
        if let Self::Elaborated(constructor) = self {
            Self::Elaborated(ElaboratedTypeConstructor {
                definition: constructor.definition.clone(),
                structure: constructor.structure.with_substitutions(subs),
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

    pub fn structure(&self) -> Typing<&Type> {
        if let Self::Elaborated(c) = self {
            Ok(&c.structure)
        } else {
            Err(
                TypeError::UnelaboratedConstructor(self.definition().name.clone())
                    .at(ParseInfo::default()),
            )
        }
    }

    // Move this to TypingContext?
    fn instantiate(&self, ctx: &TypingContext) -> Typing<Self> {
        let mut the = Self::from_symbol(&self.definition().defining_symbol);
        the.elaborate(ctx)?;
        Ok(the)
    }

    fn defining_context(&self) -> &parser::IdentifierPath {
        self.definition().name.module()
    }
}

fn fresh_type_parameters(
    symbol: &TypeSymbol<QualifiedName>,
) -> HashMap<parser::Identifier, TypeParameter> {
    symbol
        .type_parameters()
        .iter()
        .map(|tp| (tp.clone(), TypeParameter::fresh()))
        .collect()
}

impl TypeDefinition<QualifiedName> {
    pub fn synthesize_type(
        &self,
        type_param_map: &HashMap<parser::Identifier, TypeParameter>,
        ctx: &TypingContext,
    ) -> Typing<Type> {
        match self {
            Self::Record(record) => record.synthesize_type(type_param_map, ctx),
            Self::Coproduct(coproduct) => coproduct.synthesize_type(type_param_map, ctx),
            Self::Builtin(base_type) => Ok(Type::Base(*base_type)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeScheme {
    pub quantifiers: Vec<TypeParameter>,
    pub underlying: Type,
    pub constraints: ConstraintSet,
}

impl TypeScheme {
    pub fn with_substitutions(&self, subst: &Substitutions) -> Self {
        let mut subst = subst.clone();
        for q in &self.quantifiers {
            subst.remove(*q);
        }
        Self {
            quantifiers: self.quantifiers.clone(),
            underlying: self.underlying.with_substitutions(&subst),
            constraints: self.constraints.with_substitutions(&subst),
        }
    }

    fn instantiation_substitutions(&self) -> Substitutions {
        self.quantifiers
            .iter()
            .map(|tp| (*tp, Type::fresh()))
            .collect::<Vec<_>>()
            .into()
    }

    pub fn instantiate(&self) -> Constrained<Type> {
        let subst = self.instantiation_substitutions();
        Constrained {
            constraints: self.constraints.with_substitutions(&subst),
            underlying: self.underlying.with_substitutions(&subst),
        }
    }

    pub fn from_constant(ty: Type) -> TypeScheme {
        Self {
            quantifiers: vec![],
            underlying: ty,
            constraints: ConstraintSet::default(),
        }
    }

    pub fn free_variables(&self) -> HashSet<TypeParameter> {
        let mut vars = self.underlying.variables();
        for q in &self.quantifiers {
            vars.remove(q);
        }
        vars
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeParameter(u32);

static FRESH_TYPE_ID: AtomicU32 = AtomicU32::new(0);

impl TypeParameter {
    pub fn fresh() -> Self {
        Self(FRESH_TYPE_ID.fetch_add(1, Ordering::SeqCst))
    }

    pub fn new(p: u32) -> Self {
        Self(p)
    }
}

//pub struct Substitutions(Vec<(TypeParamter, Type)>);
#[derive(Debug, Default, Clone)]
pub struct Substitutions(Vec<(TypeParameter, Type)>);

impl Substitutions {
    pub fn substitution(&self, TypeParameter(rhs): &TypeParameter) -> Option<&Type> {
        self.iter()
            .rev()
            .find_map(|(TypeParameter(lhs), ty)| (lhs == rhs).then_some(ty))
    }

    fn compose(&self, rhs: &Self) -> Self {
        let mut out = Vec::new();

        for (param, ty) in rhs.iter() {
            out.push((*param, ty.with_substitutions(self)));
        }

        for (param, ty) in self.iter() {
            out.push((*param, ty.clone()));
        }

        Substitutions(out)
    }

    fn remove(&mut self, param: TypeParameter) {
        self.0.retain(|(tp, ..)| param != *tp);
    }

    fn domain(&self) -> Vec<&TypeParameter> {
        self.0.iter().map(|(t, _)| t).collect()
    }

    fn codomain(&self) -> Vec<&TypeParameter> {
        self.0
            .iter()
            .filter_map(|(_, u)| match u {
                Type::Variable(tp) => Some(tp),
                _ => None,
            })
            .collect()
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

impl From<Vec<(TypeParameter, Type)>> for Substitutions {
    fn from(value: Vec<(TypeParameter, Type)>) -> Self {
        Self(value)
    }
}

impl Deref for Substitutions {
    type Target = [(TypeParameter, Type)];

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
            namer::Identifier::Bound(index) => Some(&self.bound[*index]),
            namer::Identifier::Free(member) => self.free.get(member),
        }
    }

    pub fn free_variables(&self) -> HashSet<TypeParameter> {
        self.bound
            .iter()
            .flat_map(|ts| ts.free_variables())
            .chain(self.free.values().flat_map(|ts| ts.free_variables()))
            .collect()
    }
}

impl namer::StructPattern {
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
struct RecordShapeIndex(HashMap<RecordShape, Vec<namer::QualifiedName>>);

impl RecordShapeIndex {
    fn insert(&mut self, record_type: &RecordType, name: namer::QualifiedName) {
        self.0.entry(record_type.shape()).or_default().push(name);
    }

    fn matching(&self, image: &RecordShape) -> impl Iterator<Item = &namer::QualifiedName> {
        self.0.get(image).into_iter().flatten()
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

    fn query_record_type_constructor(&self, shape: &RecordShape) -> Vec<&TypeConstructor> {
        self.record_shapes
            .matching(shape)
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

    fn with_substitutions(&self, subs: &Substitutions) -> Self {
        Self {
            bindings: self
                .bindings
                .iter()
                .map(|(id, tc)| (id.clone(), tc.with_substitutions(subs)))
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
    pub fn normalize_type_application(&self, pi: ParseInfo, ty: &Type) -> Typing<Type> {
        if let Type::Constructor { .. } | Type::Apply { .. } = ty {
            self.reduce_applied_constructor(pi, ty, &mut vec![])
        } else {
            Ok(ty.clone())
        }
    }

    fn reduce_applied_constructor(
        &self,
        pi: ParseInfo,
        applied: &Type,
        arguments: &mut Vec<Type>,
    ) -> Typing<Type> {
        match applied {
            Type::Constructor(name) => {
                let constructor = self
                    .types
                    .lookup(name)
                    .ok_or_else(|| TypeError::UndefinedType(name.clone()).at(pi))?
                    .instantiate(&self)?;

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
                        .map(|p| {
                            definition
                                .instantiated_params
                                .get(p)
                                .expect(&format!("Unmapped type parameter: {p}"))
                        })
                        .copied()
                        .zip(arguments.drain(..))
                        .collect::<Vec<_>>(),
                );

                Ok(constructor.structure()?.with_substitutions(&subs))
            }

            Type::Apply {
                constructor,
                argument,
            } => {
                arguments.push(*argument.clone());
                self.reduce_applied_constructor(pi, constructor, arguments)
            }

            _ => Ok(applied.clone()),
        }
    }

    // Why isn't this fucker &mut self?
    pub fn with_substitutions(&self, subs: &Substitutions) -> Self {
        Self {
            types: self.types.with_substitutions(subs),
            terms: TermEnvironment {
                bound: Self::substitute_bound(&self.terms.bound, subs),
                free: Self::substitute_free(&self.terms.free, subs),
            },
        }
    }

    fn substitute_mut(&mut self, subs: &Substitutions) {
        let new_self = self.with_substitutions(&subs);
        *self = new_self;
    }

    fn substitute_bound(terms: &[TypeScheme], subs: &Substitutions) -> Vec<TypeScheme> {
        terms.iter().map(|ty| ty.with_substitutions(subs)).collect()
    }

    fn substitute_free(
        terms: &HashMap<namer::QualifiedName, TypeScheme>,
        subs: &Substitutions,
    ) -> HashMap<namer::QualifiedName, TypeScheme> {
        terms
            .iter()
            .map(|(k, v)| (k.clone(), v.with_substitutions(subs)))
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
                    Type::Record(shape) => self
                        .types
                        .record_shapes
                        .insert(shape, constructor.definition.name.clone()),

                    Type::Coproduct(coproduct) => {
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
                self.check_recursive_lambda(*pi, &expected_type, rec)
            }

            UntypedExpr::Lambda(pi, lambda) => self.check_lambda(*pi, &expected_type, lambda),

            UntypedExpr::Tuple(pi, tuple) => self.check_tuple(*pi, &expected_type, tuple),

            UntypedExpr::Construct(pi, construct) => {
                self.check_construct(*pi, &expected_type, construct)
            }

            UntypedExpr::Deconstruct(pi, deconstruct) => {
                self.check_deconstruction(*pi, &expected_type, deconstruct)
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
            .with_substitutions(&expr.substitutions);
        let rhs = expected_type.with_substitutions(&expr.substitutions);

        let s_unification = lhs
            .unified_with(&rhs)
            .map_err(|e| e.at(expr.tree.annotation().parse_info))?;

        let substitutions = expr.substitutions.compose(&s_unification);
        let constraints = expr.constraints.with_substitutions(&substitutions);

        self.substitute_mut(&substitutions);

        let expr = expr.tree.with_substitutions(&substitutions);
        Ok(Typed::computed(substitutions, constraints, expr))
    }

    #[instrument]
    fn check_construct(
        &mut self,
        pi: ParseInfo,
        expected_type: &Type,
        construct: &namer::Construct,
    ) -> Typing {
        let normalized_type = self.normalize_type_application(pi, expected_type)?;

        if let Type::Coproduct(coproduct) = &normalized_type {
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
                    .with_substitutions(&substitutions)
                    .union(typed_arg.constraints);
                typed_args.push(typed_arg.tree.into());
            }

            constraints = constraints.with_substitutions(&substitutions);
            let type_info = pi.with_inferred_type(expected_type.with_substitutions(&substitutions));
            Ok(Typed::computed(
                substitutions,
                constraints,
                Expr::Construct(
                    type_info,
                    Construct {
                        constructor: construct.constructor.clone(),
                        arguments: typed_args,
                    },
                ),
            ))
        } else {
            self.infer_coproduct_construct(pi, construct)
        }
    }

    #[instrument]
    fn check_recursive_lambda(
        &mut self,
        pi: ParseInfo,
        expected_type: &Type,
        rec: &namer::SelfReferential,
    ) -> Typing {
        let normalized_type = self.normalize_type_application(pi, &expected_type)?;
        if let Type::Arrow { domain, codomain } = &normalized_type {
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
                                expected_type
                                    .with_substitutions(&typed_body.substitutions)
                                    .clone(),
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
        lambda: &namer::Lambda,
    ) -> Typing {
        let normalized_type = self.normalize_type_application(pi, &expected_type)?;
        if let Type::Arrow { domain, codomain } = &normalized_type {
            self.bind_term_and_then(
                lambda.parameter.clone(),
                TypeScheme::from_constant(*domain.clone()),
                |ctx| {
                    let body = ctx.check_expr(codomain, &lambda.body)?;

                    let type_info = pi
                        .with_inferred_type(expected_type.with_substitutions(&body.substitutions));
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
            todo!()
        }
    }

    #[instrument]
    fn check_tuple(&mut self, pi: ParseInfo, expected_type: &Type, tuple: &namer::Tuple) -> Typing {
        let mut constraints = ConstraintSet::default();
        let normalized_type = self.normalize_type_application(pi, &expected_type)?;

        if let Type::Tuple(TupleType(elements)) = &normalized_type {
            let mut typed_elements = Vec::with_capacity(elements.len());
            let mut substitutions = Substitutions::default();

            for (expr, expected) in tuple.elements.iter().zip(elements) {
                let typed_element = self.check_expr(expected, expr)?;
                substitutions = substitutions.compose(&typed_element.substitutions);
                typed_elements.push(typed_element.tree.into());
                constraints = constraints
                    .with_substitutions(&substitutions)
                    .union(typed_element.constraints.with_substitutions(&substitutions))
            }

            let type_info = pi.with_inferred_type(expected_type.with_substitutions(&substitutions));
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
        } else {
            self.infer_tuple(pi, tuple)
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

            UntypedExpr::Construct(pi, constructor) => {
                self.infer_coproduct_construct(*pi, constructor)
            }

            UntypedExpr::Project(pi, projection) => self.infer_projection(*pi, projection),

            UntypedExpr::Sequence(_pi, sequence) => self.infer_sequence(sequence),

            UntypedExpr::Deconstruct(pi, deconstruct) => {
                self.infer_deconstruction(*pi, deconstruct)
            }

            UntypedExpr::If(pi, if_then_else) => self.infer_if_then_else(*pi, if_then_else),

            UntypedExpr::Interpolate(pi, ast::Interpolate(segments)) => {
                self.infer_interpolation(*pi, &segments)
            }

            UntypedExpr::Ascription(pi, ascription) => self.infer_ascription(*pi, ascription),
        }
    }

    #[instrument]
    fn infer_ascription(&mut self, pi: ParseInfo, ascription: &namer::TypeAscription) -> Typing {
        let ascribed_scheme = ascription
            .type_signature
            .scheme(&mut HashMap::default(), self)?;
        let ascribed_type = ascribed_scheme.instantiate();
        let ascribed_tree =
            self.check_expr(&ascribed_type.underlying, &ascription.ascribed_tree)?;

        Ok(ascribed_tree.map_tree(&|tree| {
            Expr::Ascription(
                tree.type_info().clone(),
                TypeAscription {
                    ascribed_tree: tree.into(),
                    type_signature: ascription.type_signature.map_annotation(&|pi| TypeInfo {
                        parse_info: *pi,
                        inferred_type: ascribed_type.underlying.clone(),
                    }),
                },
            )
        }))
    }

    #[instrument]
    fn infer_interpolation(&mut self, pi: ParseInfo, segments: &[namer::Segment]) -> Typing {
        let mut segs = vec![];
        let mut substitutions = Substitutions::default();
        let mut constraints = ConstraintSet::default();

        for segment in segments {
            match segment {
                ast::Segment::Literal(pi, literal) => segs.push(Segment::Literal(
                    (*pi).with_inferred_type(literal.synthesize_type()),
                    literal.clone(),
                )),
                ast::Segment::Expression(expr) => {
                    let typed_expr = self.infer_expr(&expr)?;
                    segs.push(ast::Segment::Expression(typed_expr.tree.into()));
                    substitutions = substitutions.compose(&typed_expr.substitutions);
                    constraints = constraints
                        .with_substitutions(&substitutions)
                        .union(typed_expr.constraints.with_substitutions(&substitutions))
                }
            }
        }

        let segs = segs
            .into_iter()
            .map(|s| match s {
                Segment::Expression(expr) => {
                    Segment::Expression(expr.with_substitutions(&substitutions))
                }
                lit => lit,
            })
            .collect();

        constraints = constraints.with_substitutions(&substitutions);
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
        deconstruct: &namer::Deconstruct,
    ) -> Typing {
        let Typed {
            mut substitutions,
            tree: scrutinee,
            mut constraints,
        } = self.infer_expr(&deconstruct.scrutinee)?;
        let scrutinee_type = &scrutinee.type_info().inferred_type;
        let mut typed_match_clauses = Vec::with_capacity(deconstruct.match_clauses.len());

        for clause in &deconstruct.match_clauses {
            let mut clause_ctx = self.clone();
            let mut bindings = Vec::default();
            let (s_pattern, pattern) = clause_ctx.check_pattern(
                &clause.pattern,
                &mut bindings,
                &scrutinee_type.with_substitutions(&substitutions),
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
                .with_substitutions(&substitutions)
                .union(consequent.with_substitutions(&substitutions).constraints);
            typed_match_clauses.push(MatchClause {
                pattern,
                consequent: consequent.tree.into(),
            });
        }

        let type_info = pi.with_inferred_type(expected_type.with_substitutions(&substitutions));
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

    #[instrument]
    // Rewrite this sucker
    fn infer_deconstruction(&mut self, pi: ParseInfo, deconstruct: &namer::Deconstruct) -> Typing {
        let Typed {
            mut substitutions,
            tree: scrutinee,
            mut constraints,
        } = self.infer_expr(&deconstruct.scrutinee)?;
        let scrutinee_type = &scrutinee.type_info().inferred_type;
        let mut match_clauses = deconstruct.match_clauses.iter();
        let mut typed_match_clauses = Vec::with_capacity(deconstruct.match_clauses.len());

        let mut clause_ctx = self.clone();
        if let Some(clause) = match_clauses.next() {
            let mut consequent_type = {
                let mut bindings = Vec::default();
                let (s_pattern, pattern) =
                    clause_ctx.check_pattern(&clause.pattern, &mut bindings, scrutinee_type)?;
                clause_ctx.substitute_mut(&s_pattern);
                for (binding, ty) in bindings {
                    clause_ctx.bind_term(binding, TypeScheme::from_constant(ty));
                }
                let typed_expr = clause_ctx.infer_expr(&clause.consequent)?;
                substitutions = substitutions
                    .compose(&typed_expr.substitutions)
                    .compose(&s_pattern);
                let consequent_type = typed_expr.tree.type_info().inferred_type.clone();
                typed_match_clauses.push(MatchClause {
                    pattern,
                    consequent: typed_expr.tree.into(),
                });
                constraints = constraints
                    .with_substitutions(&substitutions)
                    .union(typed_expr.constraints.with_substitutions(&substitutions));
                consequent_type
            };

            for clause in match_clauses {
                clause_ctx = self.clone();
                let mut bindings = Vec::default();
                let scrutinee_type = &scrutinee_type.with_substitutions(&substitutions);
                let (pattern_subs, pattern) =
                    clause_ctx.check_pattern(&clause.pattern, &mut bindings, scrutinee_type)?;
                clause_ctx.substitute_mut(&pattern_subs);
                for (binding, ty) in bindings {
                    clause_ctx.bind_term(binding, TypeScheme::from_constant(ty));
                }
                let typed_expr = clause_ctx.infer_expr(&clause.consequent)?;
                substitutions = substitutions
                    .compose(&pattern_subs)
                    .compose(&typed_expr.substitutions);

                let branch_subs = typed_expr
                    .tree
                    .type_info()
                    .inferred_type
                    .with_substitutions(&substitutions)
                    .unified_with(&consequent_type.with_substitutions(&substitutions))
                    .map_err(|e| e.at(*&typed_expr.tree.annotation().parse_info))?;

                substitutions = substitutions.compose(&branch_subs);
                consequent_type = consequent_type.with_substitutions(&branch_subs);
                clause_ctx.substitute_mut(&substitutions);
                typed_match_clauses.push(MatchClause {
                    pattern,
                    consequent: typed_expr.tree.into(),
                });

                constraints = constraints
                    .with_substitutions(&substitutions)
                    .union(typed_expr.constraints.with_substitutions(&substitutions));
            }

            let mut match_space = MatchSpace::default();

            for clause in &typed_match_clauses {
                if !match_space.join(&clause.pattern) {
                    Err(TypeError::UselessMatchClause {
                        clause: clause.clone(),
                    }
                    .at(clause.pattern.annotation().parse_info))?;
                }
            }

            let deconstruct = Deconstruct {
                scrutinee: scrutinee.clone().into(),
                match_clauses: typed_match_clauses,
            };

            if !match_space.is_exhaustive(
                pi,
                &scrutinee_type.with_substitutions(&substitutions),
                self,
            )? {
                Err(TypeError::MatchNotExhaustive {
                    deconstruct: deconstruct.clone(),
                }
                .at(pi))?;
            }

            Ok(Typed::computed(
                substitutions,
                constraints,
                Expr::Deconstruct(pi.with_inferred_type(consequent_type), deconstruct),
            ))
        } else {
            panic!("Now wtf?")
        }
    }

    #[instrument]
    fn infer_scrutinee(
        &mut self,
        pattern: &namer::Pattern,
        bindings: &mut Vec<(namer::Identifier, Type)>,
        scrutinee: TypeParameter,
    ) -> Typing<(Substitutions, Pattern)> {
        match pattern {
            namer::Pattern::Coproduct(pi, coproduct) => {
                let constructor = coproduct
                    .constructor
                    .try_as_free()
                    .expect("expected Free identifier");

                let inferred = self
                    .types
                    .query_coproduct_type_constructors(&constructor)?
                    .first()
                    .ok_or_else(|| {
                        TypeError::NoSuchCoproductConstructor(constructor.clone()).at(*pi)
                    })?
                    .instantiate(&self)?
                    .make_spine();

                let substitutions = Substitutions::from(vec![(scrutinee, inferred.clone())]);

                self.substitute_mut(&substitutions);

                let (s_pattern, pattern) = self.check_pattern(pattern, bindings, &inferred)?;
                Ok((s_pattern.compose(&substitutions), pattern))
            }

            namer::Pattern::Struct(pi, record) => {
                let shape = record.shape();
                let inferred = self
                    .types
                    .query_record_type_constructor(&shape)
                    .first()
                    .ok_or_else(|| TypeError::NoRecordTypWithShape(shape))
                    .map_err(|e| e.at(*pi))?
                    .instantiate(&self)?
                    .make_spine();

                let substitutions = Substitutions::from(vec![(scrutinee, inferred.clone())]);

                self.substitute_mut(&substitutions);

                let (s_pattern, pattern) = self.check_pattern(pattern, bindings, &inferred)?;
                Ok((s_pattern.compose(&substitutions), pattern))
            }

            namer::Pattern::Tuple(pi, tuple) => {
                let tuple = Type::Tuple(TupleType(
                    tuple.elements.iter().map(|_| Type::fresh()).collect(),
                ));
                let unification = tuple
                    .unified_with(&Type::Variable(scrutinee))
                    .map_err(|e| e.at(*pi))?;

                self.substitute_mut(&unification);

                let (s_pattern, pattern) = self.check_pattern(pattern, bindings, &tuple)?;

                Ok((s_pattern.compose(&unification), pattern))
            }

            namer::Pattern::Literally(pi, pattern) => {
                let scrutinee = Type::Variable(scrutinee);
                let inferred = pattern.synthesize_type();
                let s_pattern = inferred.unified_with(&scrutinee).map_err(|e| e.at(*pi))?;

                Ok((
                    s_pattern,
                    Pattern::Literally((*pi).with_inferred_type(inferred), pattern.clone()),
                ))
            }

            namer::Pattern::Bind(pi, pattern) => {
                let scrutinee = Type::Variable(scrutinee);
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
        pattern: &namer::Pattern,
        bindings: &mut Vec<(namer::Identifier, Type)>,
        scrutinee: &Type,
    ) -> Typing<(Substitutions, Pattern)> {
        let pi = *pattern.annotation();
        let normalized_scrutinee = self.normalize_type_application(pi, &scrutinee)?;

        match (pattern, &normalized_scrutinee) {
            (_, Type::Variable(p)) => self.infer_scrutinee(pattern, bindings, *p),

            (namer::Pattern::Coproduct(pi, pattern), Type::Coproduct(coproduct)) => {
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
                            &scrutinee.with_substitutions(&substitutions),
                        )?;
                        self.substitute_mut(&subs);
                        arguments.push(argument.with_substitutions(&substitutions));
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

            (namer::Pattern::Tuple(pi, pattern), Type::Tuple(tuple))
                if pattern.elements.len() == tuple.arity() =>
            {
                let mut elements = Vec::with_capacity(tuple.arity());
                let mut substitutions = Substitutions::default();

                for (pattern, scrutinee) in pattern.elements.iter().zip(tuple.elements()) {
                    let (subs, element) = self.check_pattern(pattern, bindings, scrutinee)?;
                    elements.push(element);
                    substitutions = substitutions.compose(&subs);
                }

                Ok((
                    substitutions,
                    Pattern::Tuple(
                        (*pi).with_inferred_type(scrutinee.clone()),
                        TuplePattern { elements },
                    ),
                ))
            }

            (namer::Pattern::Struct(pi, pattern), Type::Record(record))
                if pattern.fields.len() == record.arity() =>
            {
                let mut arguments = Vec::with_capacity(record.arity());
                let mut substitutions = Substitutions::default();

                for ((pattern_field, pattern), (scrutinee_field, scrutinee)) in
                    (&pattern.fields).iter().zip(record.fields().iter())
                {
                    if pattern_field != scrutinee_field {
                        Err(TypeError::BadRecordPatternField {
                            record_type: scrutinee.clone(),
                            field: pattern_field.clone(),
                        }
                        .at(*pi))?;
                    }

                    let (subs, pattern) = self.check_pattern(pattern, bindings, scrutinee)?;
                    arguments.push((pattern_field.clone(), pattern));
                    substitutions = substitutions.compose(&subs);
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
            (namer::Pattern::Literally(pi, pattern), ..) => {
                let inferred = pattern.synthesize_type();
                let subs = inferred.unified_with(&scrutinee).map_err(|e| e.at(*pi))?;

                Ok((
                    subs,
                    Pattern::Literally((*pi).with_inferred_type(inferred), pattern.clone()),
                ))
            }

            (namer::Pattern::Bind(pi, pattern), ..) => {
                bindings.push((pattern.clone(), scrutinee.clone()));
                Ok((
                    Substitutions::default(),
                    Pattern::Bind((*pi).with_inferred_type(scrutinee.clone()), pattern.clone()),
                ))
            }

            (pattern, ty) => panic!("Type error. Illegal pattern. `{pattern}` `{ty}`"),
        }
    }

    #[instrument]
    fn infer_coproduct_construct(&mut self, pi: ParseInfo, construct: &namer::Construct) -> Typing {
        let (substitutions, constraints, typed_arguments, argument_types) =
            self.infer_several(&construct.arguments)?;

        let candidates = self
            .types
            .query_coproduct_type_constructors(&construct.constructor)?;

        let type_constructor = candidates
            // It could go for the first constructor that unifies
            // but it is probably better to crash here and ask
            // the user to qualify the name with a <Coproduct name>.<Constructor name>
            // type of deal
            .first()
            .ok_or_else(|| {
                TypeError::NoSuchCoproductConstructor(construct.constructor.clone()).at(pi)
            })?;

        let type_constructor = type_constructor.instantiate(self)?;

        let subs = if let Type::Coproduct(coproduct) = type_constructor.structure()? {
            let signature = coproduct.signature(&construct.constructor).ok_or_else(|| {
                TypeError::NoSuchCoproductConstructor(construct.constructor.clone()).at(pi)
            })?;
            Type::Tuple(TupleType::from_signature(signature))
                .unified_with(&Type::Tuple(TupleType::from_signature(&argument_types)))
                .map_err(|e| e.at(pi))?
        } else {
            Err(TypeError::InternalAssertion(format!("Expected ")).at(pi))?
        };

        let constraints = constraints.with_substitutions(&substitutions);

        Ok(Typed::computed(
            substitutions,
            constraints,
            Expr::Construct(
                pi.with_inferred_type(type_constructor.make_spine().with_substitutions(&subs)),
                Construct {
                    constructor: construct.constructor.clone(),
                    arguments: typed_arguments,
                },
            ),
        ))
    }

    #[instrument]
    fn infer_record(&mut self, pi: ParseInfo, record: &namer::Record) -> Typing {
        let mut substitutions = Substitutions::default();
        let mut fields = Vec::with_capacity(record.fields.len());
        let mut constraints = ConstraintSet::default();

        for (label, initializer) in &record.fields {
            let typed_field = self.infer_expr(initializer)?;
            fields.push((label, typed_field.tree));
            substitutions = substitutions.compose(&typed_field.substitutions);
            constraints = constraints
                .with_substitutions(&substitutions)
                .union(typed_field.constraints.with_substitutions(&substitutions));
        }

        let fields = fields
            .iter()
            .map(|(label, e)| {
                (
                    (*label).clone(),
                    e.with_substitutions(&substitutions).into(),
                )
            })
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

        let type_constructors = self
            .types
            .query_record_type_constructor(&record_type.shape());

        let type_constructor = type_constructors
            .first()
            .ok_or_else(|| TypeError::NoSuchRecordType(record_type.clone()).at(pi))?;

        // This is needed for coproducts too
        let type_constructor = type_constructor.instantiate(self)?;

        let subs = type_constructor
            .structure()?
            .unified_with(&Type::Record(record_type))
            .map_err(|e| e.at(pi))?;

        let substitutions = substitutions.compose(&subs);
        let constraints = constraints.with_substitutions(&substitutions);
        let type_info = pi.with_inferred_type(
            type_constructor
                .make_spine()
                .with_substitutions(&substitutions),
        );
        Ok(Typed::computed(
            substitutions,
            constraints,
            Expr::Record(type_info, Record { fields }),
        ))
    }

    #[instrument]
    fn infer_projection(&mut self, pi: ParseInfo, projection: &namer::Projection) -> Typing {
        let Typed {
            substitutions,
            tree: base,
            constraints,
        } = self.infer_expr(&projection.base)?;
        let base_type = &base.type_info().inferred_type;
        let normalized_base_type = self.normalize_type_application(pi, base_type)?;

        match &projection.select {
            ProductElement::Name(field) => {
                if let Type::Record(record) = &normalized_base_type {
                    if let Some((field_index, (_, field_type))) = record
                        .0
                        .iter()
                        .enumerate()
                        .find(|(_, (label, _))| label == field)
                    {
                        Ok(Typed::computed(
                            substitutions,
                            constraints,
                            Expr::Project(
                                pi.with_inferred_type(field_type.clone()),
                                Projection {
                                    base: base.into(),
                                    select: ProductElement::Ordinal(field_index),
                                },
                            ),
                        ))
                    } else {
                        Err(TypeError::BadProjection {
                            projection: projection.clone(),
                            inferred_type: base_type.clone(),
                        }
                        .at(pi))
                    }
                } else {
                    panic!("{base_type}")
                }
            }

            ProductElement::Ordinal(ordinal) => match normalized_base_type {
                Type::Tuple(tuple) => {
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

                Type::Variable(..) => {
                    let mut elems = Vec::with_capacity(ordinal + 1);
                    for _ in 0..=*ordinal {
                        elems.push(Type::fresh());
                    }
                    let tuple_ty = Type::Tuple(TupleType::from_signature(&elems));
                    let subs = base_type.unified_with(&tuple_ty).map_err(|e| e.at(pi))?;
                    let projected_ty = match tuple_ty.with_substitutions(&subs) {
                        Type::Tuple(tuple) => tuple.elements()[*ordinal].clone(),
                        _ => unreachable!(),
                    };
                    let substitutions = substitutions.compose(&subs);
                    let constraints = constraints.with_substitutions(&substitutions);
                    Ok(Typed::computed(
                        substitutions.compose(&subs),
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
                    inferred_type: base.type_info().inferred_type.clone(),
                }
                .at(pi)),
            },
        }
    }

    #[instrument]
    fn infer_tuple(&mut self, pi: ParseInfo, tuple: &namer::Tuple) -> Typing {
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
            constraints = constraints.union(typed.constraints.with_substitutions(&substitutions));
        }

        let typed_elements = typed_elements
            .iter()
            .map(|e| e.with_substitutions(&substitutions).into())
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
        rec_lambda: &namer::SelfReferential,
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
                            .unified_with(&codomain.with_substitutions(&typed.substitutions))
                            .map_err(|e| e.at(pi))?;

                        let substitutions = typed.substitutions.compose(&s_codomain);

                        ctx.substitute_mut(&substitutions);

                        Ok(Typed::computed(
                            substitutions.clone(),
                            typed.constraints.with_substitutions(&substitutions),
                            Expr::RecursiveLambda(
                                pi.with_inferred_type(own_ty.with_substitutions(&substitutions)),
                                SelfReferential {
                                    own_name: rec_lambda.own_name.clone(),
                                    lambda: Lambda {
                                        parameter: rec_lambda.lambda.parameter.clone(),
                                        body: typed.tree.into(),
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
    fn infer_apply2(
        &mut self,
        pi: ParseInfo,
        function: &namer::Expr,
        argument: &namer::Expr,
    ) -> Typing {
        let mut function = self.infer_expr(function)?;
        let function_type = &function.tree.type_info().inferred_type;

        if let Type::Variable(..) = function_type {
            println!("infer_apply2: unknown function");
            let domain = Type::fresh();
            let codomain = Type::fresh();
            let unification = Type::Arrow {
                domain: domain.into(),
                codomain: codomain.into(),
            }
            .unified_with(&function_type)
            .map_err(|e| e.at(pi))?;

            let s_function = function.substitutions.compose(&unification);
            function = function.with_substitutions(&s_function);
            self.substitute_mut(&s_function);
        }

        let function_type = &function.tree.type_info().inferred_type;
        if let Type::Arrow { domain, codomain } = &function_type {
            let argument = self.check_expr(
                &domain.with_substitutions(&function.substitutions),
                argument,
            )?;

            let substitutions = function.substitutions.compose(&argument.substitutions);
            let codomain = codomain.with_substitutions(&substitutions);
            let argument = argument.with_substitutions(&substitutions);

            let constraints = function
                .constraints
                .with_substitutions(&substitutions)
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
        function: &namer::Expr,
        argument: &namer::Expr,
    ) -> Typing {
        let function = self.infer_expr(function)?;
        let mut ctx = self.with_substitutions(&function.substitutions);
        let mut constraints = function.constraints;

        let argument = ctx.infer_expr(argument)?;
        constraints = constraints
            .with_substitutions(&argument.substitutions)
            .union(
                argument
                    .constraints
                    .with_substitutions(&function.substitutions),
            );
        let return_ty = Type::fresh();

        let substitutions = function.substitutions.compose(&argument.substitutions);

        let expected_ty = Type::Arrow {
            domain: argument
                .tree
                .type_info()
                .inferred_type
                .with_substitutions(&substitutions)
                .into(),
            codomain: return_ty.clone().into(),
        };

        let substitutions = expected_ty
            .with_substitutions(&substitutions)
            .unified_with(
                &function
                    .tree
                    .type_info()
                    .inferred_type
                    .with_substitutions(&substitutions),
            )
            .map_err(|e| e.at(pi))?
            .compose(&substitutions);

        let apply = Apply {
            function: function.tree.with_substitutions(&substitutions).into(),
            argument: argument.tree.with_substitutions(&substitutions).into(),
        };

        let inferred_type = return_ty.with_substitutions(&substitutions);
        constraints = constraints.with_substitutions(&substitutions);

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
        lambda: &namer::Lambda,
    ) -> Typing<(Substitutions, ConstraintSet, TypeInfo, Lambda)> {
        let domain = Type::fresh();
        let codomain = Type::fresh();

        trace!("lambda-domain {domain}, codomain {codomain}");
        self.bind_term_and_then(
            lambda.parameter.clone(),
            TypeScheme::from_constant(domain.clone()),
            |ctx| {
                let Typed {
                    mut substitutions,
                    tree: body,
                    constraints,
                } = ctx.infer_expr(&lambda.body)?;

                let body_type = body
                    .type_info()
                    .inferred_type
                    .with_substitutions(&substitutions);

                let unify_subs = body_type
                    .unified_with(&codomain.with_substitutions(&substitutions))
                    .map_err(|e| e.at(pi))?;

                substitutions = substitutions.compose(&unify_subs);

                let inferred_type = Type::Arrow {
                    domain: domain.with_substitutions(&substitutions).into(),
                    codomain: codomain.with_substitutions(&substitutions).into(),
                };

                let body = body.with_substitutions(&substitutions);

                let constraints = constraints.with_substitutions(&substitutions);
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
    fn infer_binding(&mut self, pi: ParseInfo, binding: &namer::Binding) -> Typing {
        let typed_bound = self.infer_expr(&binding.bound)?;
        let ctx1 = self.with_substitutions(&typed_bound.substitutions);

        let bound_type = typed_bound.as_constrained_type().generalize(&ctx1);

        self.bind_term_and_then(binding.binder.clone(), bound_type.underlying, |ctx| {
            let typed_body = ctx.infer_expr(&binding.body)?;

            let substitutions = typed_bound.substitutions.compose(&typed_body.substitutions);

            let bound = typed_bound.tree.with_substitutions(&substitutions);
            let body = typed_body.tree.with_substitutions(&substitutions);
            let constraints = typed_bound
                .constraints
                .with_substitutions(&substitutions)
                .union(typed_body.constraints.with_substitutions(&substitutions));

            Ok(Typed::computed(
                substitutions,
                constraints,
                Expr::Let(
                    pi.with_inferred_type(body.type_info().inferred_type.clone()),
                    Binding {
                        binder: binding.binder.clone(),
                        bound: bound.into(),
                        body: body.into(),
                    },
                ),
            ))
        })
    }

    #[instrument]
    fn infer_sequence(&mut self, sequence: &namer::Sequence) -> Typing {
        let this = self.infer_expr(&sequence.this)?;
        self.substitute_mut(&this.substitutions);
        let and_then = self.infer_expr(&sequence.and_then)?;
        let substitutions = this.substitutions.compose(&and_then.substitutions);
        let constraints = this
            .constraints
            .with_substitutions(&substitutions)
            .union(and_then.constraints.with_substitutions(&substitutions));
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
    fn infer_if_then_else(&mut self, pi: ParseInfo, if_then_else: &namer::IfThenElse) -> Typing {
        let predicate = self.infer_expr(&if_then_else.predicate)?;
        let s_bool_predicate = predicate
            .tree
            .type_info()
            .inferred_type
            .unified_with(&Type::Base(BaseType::Bool))
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
            .with_substitutions(&s_branches)
            .type_info()
            .inferred_type
            .clone();

        let substitutions = consequent_type
            .unified_with(
                &alternate
                    .tree
                    .with_substitutions(&s_branches)
                    .type_info()
                    .inferred_type,
            )
            .map_err(|e| e.at(pi))?;

        let substitutions = s_branches.compose(&substitutions);

        let predicate = predicate.with_substitutions(&substitutions);
        let consequent = consequent.with_substitutions(&substitutions);
        let alternate = alternate.with_substitutions(&substitutions);

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

    fn free_variables(&self) -> HashSet<TypeParameter> {
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
        })
    }
}

impl ParseInfo {
    fn with_inferred_type(self, inferred_type: Type) -> TypeInfo {
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
            Self::Structured(shape) => shape.covers(pi, &scrutinee, ctx),

            Self::Universal => Ok(true),

            Self::Empty | Self::Finite(..) => Ok(false),
        }
    }
}

// todo: move to pattern.rs
impl Shape {
    fn covers(&self, pi: ParseInfo, scrutinee: &Type, ctx: &TypingContext) -> Typing<bool> {
        let scrutinee = ctx.normalize_type_application(pi, scrutinee)?;
        match (self, scrutinee) {
            (Self::Coproduct(denotations), Type::Coproduct(CoproductType(constructors))) => {
                let mut covers = true;

                'outer: for (constructor, arguments) in constructors {
                    if !denotations.contains_key(&constructor) {
                        covers = false;
                        break;
                    }

                    for (denotation, scrutinee) in denotations[&constructor].iter().zip(arguments) {
                        let scrutinee = ctx.normalize_type_application(pi, &scrutinee)?;
                        covers &= denotation.covers(pi, &scrutinee, ctx)?;
                        if !covers {
                            break 'outer;
                        }
                    }
                }

                Ok(covers)
            }

            (Self::Struct(denotations), Type::Record(RecordType(fields))) => {
                let mut covers = true;
                for (field, scrutinee) in &fields {
                    let scrutinee = ctx.normalize_type_application(pi, &scrutinee)?;
                    covers &= denotations[field].covers(pi, &scrutinee, ctx)?;
                    if !covers {
                        break;
                    }
                }

                Ok(covers)
            }

            (Self::Tuple(denotations), Type::Tuple(TupleType(types))) => {
                let mut covers = true;
                for (denotation, scrutinee) in denotations.iter().zip(types) {
                    let scrutinee = ctx.normalize_type_application(pi, &scrutinee)?;
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
impl Pattern {
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

    pub fn join(&mut self, p: &Pattern) -> bool {
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

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Variable(TypeParameter(p)) => write!(f, "${p}"),

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

impl fmt::Display for TypeParameter {
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
