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

use crate::{
    ast::{
        self, Literal, ProductElement, Tree, TupleTypeExpr,
        annotation::Annotated,
        namer::{
            self, CompilationContext, DependencyMatrix, Identifier, QualifiedName, Symbol,
            SymbolName, TermSymbol, TypeDefinition, TypeExpression, TypeSymbol,
        },
    },
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
pub type MatchClause = ast::pattern::MatchClause<TypeInfo, namer::Identifier>;
pub type Pattern = ast::pattern::Pattern<TypeInfo, namer::Identifier>;
pub type ConstructorPattern = ast::pattern::ConstructorPattern<TypeInfo, namer::Identifier>;

pub type RecordSymbol = namer::RecordSymbol<namer::QualifiedName>;
pub type CoproductSymbol = namer::CoproductSymbol<namer::QualifiedName>;

type TypedSymbol = namer::Symbol<TypeInfo, namer::QualifiedName, namer::Identifier>;
type TypedCompilationContext =
    namer::CompilationContext<TypeInfo, namer::QualifiedName, namer::Identifier>;

fn display_list<A>(sep: &str, xs: &[A]) -> String
where
    A: fmt::Display,
{
    xs.iter()
        .map(|x| x.to_string())
        .collect::<Vec<_>>()
        .join(sep)
}

impl<A> CompilationContext<A, namer::QualifiedName, namer::Identifier>
where
    A: fmt::Debug,
{
    pub fn terms(
        &self,
        order: Iter<&namer::TermName>,
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
        order: Iter<&namer::TermName>,
    ) -> Vec<&namer::TypeSymbol<namer::QualifiedName>> {
        self.extract_symbols(order, |sym| {
            if let namer::Symbol::Type(sym) = sym {
                Some(sym)
            } else {
                None
            }
        })
    }

    fn extract_symbols<F, Sym>(&self, terms: Iter<&namer::TermName>, select: F) -> Vec<&Sym>
    where
        F: Fn(&namer::Symbol<A, namer::QualifiedName, namer::Identifier>) -> Option<&Sym>,
    {
        terms
            .filter_map(|&id| self.symbols.get(id))
            .filter_map(select)
            .collect()
    }

    pub fn dependency_matrix(
        &self,
    ) -> DependencyMatrix<SymbolName<namer::QualifiedName, namer::Identifier>> {
        let mut matrix = DependencyMatrix::default();

        // This function is incredibly inefficient.
        for (id, symbol) in &self.symbols {
            matrix.add_edge(id.clone(), symbol.dependencies().into_iter().collect());
        }

        matrix
    }
}

impl namer::NamedCompilationContext {
    pub fn compute_types(
        self,
        evaluation_order: Iter<&namer::TermName>,
    ) -> Typing<TypedCompilationContext> {
        let mut ctx = TypingContext::default();
        let mut symbols = HashMap::with_capacity(self.symbols.len());

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

        for (id, symbol) in evaluation_order
            .map(|&id| {
                self.symbols
                    .get(id)
                    .map(|symbol| (id, symbol))
                    .ok_or_else(|| TypeError::UndefinedTerm(id.clone()))
            })
            .collect::<Typing<Vec<_>>>()?
        {
            let symbol = match symbol {
                namer::Symbol::Term(symbol) => Self::compute_term_symbol(symbol, &mut ctx)?,
                namer::Symbol::Type(symbol) => namer::Symbol::Type(symbol.clone()),
            };

            symbols.insert(id.clone(), symbol);
        }

        Ok(CompilationContext {
            modules: self.modules,
            symbols,
            phase: PhantomData,
        })
    }

    fn compute_term_symbol(
        symbol: &TermSymbol<ParseInfo, namer::QualifiedName, Identifier>,
        ctx: &mut TypingContext,
    ) -> Typing<TypedSymbol> {
        let (subs, body) = ctx.infer_expr(&symbol.body())?;

        let qualified_name = &symbol.name;
        let inferred_type = &body.type_info().inferred_type;

        println!("{qualified_name} => {inferred_type}");

        ctx.bind_free_term(
            qualified_name.clone(),
            inferred_type.generalize(&ctx.with_substitutions(&subs)),
        );

        Ok(namer::Symbol::Term(TermSymbol {
            name: symbol.name.clone(),
            type_signature: symbol.type_signature.clone(),
            body: body.into(),
        }))
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

#[derive(Debug)]
pub enum TypeError {
    Unification {
        lhs: Type,
        rhs: Type,
    },
    InfiniteType {
        param: TypeParameter,
        ty: Type,
    },
    BadProjection {
        projection: namer::Projection,
        inferred_type: Type,
    },
    UndefinedName(Identifier),
    UndefinedType(namer::QualifiedName),
    UndefinedTerm(SymbolName<namer::QualifiedName, namer::Identifier>),
    NoSuchRecordType(RecordType),
    UnquantifiedTypeParameter(parser::Identifier),
    WrongArity {
        constructor: namer::QualifiedName,
        was: Vec<Type>,
        expected: usize,
    },
    UnelaboratedConstructor(namer::QualifiedName),
    InternalAssertion(String),
    NoSuchCoproductConstructor(namer::QualifiedName),
    ExpectedTuple,
    TupleOrdinalOutOfBounds {
        base: ast::Expr<ParseInfo, Identifier>,
        select: ProductElement,
    },
}

pub type Typing<A = (Substitutions, Expr)> = Result<A, TypeError>;

#[derive(Debug, Clone)]
pub struct TypeInfo {
    pub parse_info: ParseInfo,
    pub inferred_type: Type,
}

impl TypeInfo {
    pub fn with_substitutions(&self, subs: &Substitutions) -> Self {
        Self {
            parse_info: self.parse_info,
            inferred_type: self.inferred_type.with_substitutions(subs),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeInference {
    pub inferred_type: Type,
    pub substitutions: Substitutions,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecordType(Vec<(parser::Identifier, Type)>);

impl RecordType {
    fn from_fields(fields: &[(parser::Identifier, Type)]) -> Self {
        let mut fields = fields.to_vec();
        fields.sort_by(|(t, _), (u, _)| t.cmp(u));

        Self(fields)
    }

    fn with_substitutions(self, subs: &Substitutions) -> Self {
        Self(
            self.0
                .into_iter()
                .map(|(id, t)| (id, t.with_substitutions(subs)))
                .collect(),
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    pub fn fresh() -> Self {
        Self::Variable(TypeParameter::fresh())
    }

    pub fn is_base(&self) -> bool {
        matches!(self, Type::Base(..))
    }

    pub fn variables(&self) -> HashSet<TypeParameter> {
        match self {
            Self::Variable(param) => [*param].into(),

            Self::Base(..) => [].into(),

            Self::Arrow { domain, codomain } => {
                let mut variables = domain.variables();
                variables.extend(codomain.variables());
                variables
            }

            Self::Tuple(tuple) => tuple
                .elements()
                .iter()
                .flat_map(|ty| ty.variables())
                .collect(),

            Self::Record(record) => record.0.iter().flat_map(|(_, ty)| ty.variables()).collect(),

            Self::Coproduct(coproduct) => coproduct
                .0
                .iter()
                .flat_map(|(_, ty)| ty.iter().flat_map(|ty| ty.variables()))
                .collect(),

            Self::Constructor(..) => [].into(),

            Self::Apply {
                constructor,
                argument,
            } => {
                let mut variables = constructor.variables();
                variables.extend(argument.variables());
                variables
            }
        }
    }

    pub fn with_substitutions(&self, subs: &Substitutions) -> Self {
        match self {
            p @ Self::Variable(param) => subs
                .substitution(param)
                .map_or_else(|| p.clone(), |t| t.with_substitutions(subs))
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

            Self::Record(record) => Self::Record(record.clone().with_substitutions(subs)),

            Self::Coproduct(coproduct) => {
                Self::Coproduct(coproduct.clone().with_substitutions(subs))
            }

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

    pub fn unifed_with(&self, rhs: &Self) -> Typing<Substitutions> {
        match (self, rhs) {
                (Self::Variable(p), ty) | (ty, Self::Variable(p)) => {
                    if ty.variables().contains(p) {
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
                    let domain = lhs_dom.unifed_with(rhs_dom)?;
                    let codomain = lhs_codom.unifed_with(rhs_codom)?;
                    Ok(domain.compose(&codomain))
                }

                (Self::Tuple(lhs), Self::Tuple(rhs)) if lhs.arity() == rhs.arity() => {
                    let mut subs = Substitutions::default();

                    println!("unifed_with: {} ~ {}", display_list("; ", lhs.elements()), display_list("; ", rhs.elements()));

                    for (lhs, rhs) in lhs.elements().iter().zip(rhs.elements()) {
                        // compose_mut
                        subs = subs.compose(&lhs.unifed_with(rhs)?);
                    }

                    println!("unified_with: substitutions {subs}");

                    Ok(subs)
                }

                (Self::Record(lhs), Self::Record(rhs)) if lhs.0.len() == rhs.0.len() => {
                    let mut subs = Substitutions::default();

                    println!("unify_with: {lhs:?} {rhs:?}");
                    // Sort first?
                    for ((lhs_label, lhs), (rhs_label, rhs)) in lhs.0.iter().zip(&rhs.0) {
                        if lhs_label != rhs_label {
                            panic!("{lhs_label} != {rhs_label}");
                        }

                        // compose_mut
                        subs = subs.compose(&lhs.unifed_with(rhs)?);
                    }

                    Ok(subs)
                }

                (Self::Coproduct(lhs), Self::Coproduct(rhs))
                    if lhs.cardinality() == rhs.cardinality() /*&& {
                        let rhs_names = rhs.constructor_names().collect::<HashSet<_>>();
                        lhs.constructor_names().all(|lhs| rhs_names.contains(lhs))
                    }*/ =>
                {
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
                    let constructor = lhs_con.unifed_with(rhs_con)?;
                    let argument = lhs_arg.unifed_with(rhs_arg)?;
                    Ok(constructor.compose(&argument))
                }

                (lhs, rhs) if lhs == rhs => Ok(Substitutions::default()),

                otherwise => panic!("{otherwise:?}"),
            }
    }

    pub fn generalize(&self, ctx: &TypingContext) -> TypeScheme {
        let ty_vars = self.variables();
        let ctx_bounds = ctx.free_variables();
        let quantified = ty_vars.difference(&ctx_bounds);

        TypeScheme {
            quantifiers: quantified.copied().collect(),
            underlying: self.clone(),
        }
    }
}

const BUILTIN_BASE_TYPE_NAMES: [&str; 2] =
    [BaseType::Int.local_name(), BaseType::Text.local_name()];

#[derive(Copy, Debug, Clone, PartialEq, Eq, Hash)]
pub enum BaseType {
    Int,
    Text,
}

impl BaseType {
    pub fn is_name(id: &str) -> bool {
        BUILTIN_BASE_TYPE_NAMES.contains(&id)
    }

    const fn local_name(&self) -> &str {
        match self {
            Self::Int => "Int",
            Self::Text => "Text",
        }
    }

    pub fn qualified_name(&self) -> namer::QualifiedName {
        match self {
            Self::Int => namer::QualifiedName::builtin("Int"),
            Self::Text => namer::QualifiedName::builtin("Text"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
            Self::Constructor(_, name) => {
                let constructor = ctx
                    .types
                    .lookup(name)
                    .ok_or_else(|| TypeError::UndefinedType(name.clone()))?;

                Ok(constructor
                    .definition()
                    .as_base_type()
                    .unwrap_or_else(|| constructor.definition().head()))
            }

            Self::Parameter(_, p) => type_params
                .get(p)
                .copied()
                .map(Type::Variable)
                .ok_or_else(|| TypeError::UnquantifiedTypeParameter(p.clone())),

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
            todo!()
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

    fn structure(&self) -> Typing<&Type> {
        if let Self::Elaborated(c) = self {
            Ok(&c.structure)
        } else {
            Err(TypeError::UnelaboratedConstructor(
                self.definition().name.clone(),
            ))
        }
    }

    // Move this to TypingContext?
    fn instantiate(&self, ctx: &TypingContext) -> Typing<Self> {
        let mut the = Self::from_symbol(&self.definition().defining_symbol);
        the.elaborate(ctx)?;
        Ok(the)
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
}

impl TypeScheme {
    pub fn with_substitutions(&self, subs: &Substitutions) -> Self {
        let mut subs = subs.clone();
        for q in &self.quantifiers {
            subs.remove(*q);
        }
        Self {
            quantifiers: self.quantifiers.clone(),
            underlying: self.underlying.with_substitutions(&subs),
        }
    }

    pub fn instantiate(&self) -> Type {
        let substitutions = self
            .quantifiers
            .iter()
            .map(|tp| (*tp, Type::fresh()))
            .collect::<Vec<_>>()
            .into();

        self.underlying.with_substitutions(&substitutions)
    }

    fn from_constant(ty: Type) -> TypeScheme {
        Self {
            quantifiers: vec![],
            underlying: ty,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeParameter(u32);

static FRESH_TYPE_ID: AtomicU32 = AtomicU32::new(0);

impl TypeParameter {
    fn fresh() -> Self {
        Self(FRESH_TYPE_ID.fetch_add(1, Ordering::SeqCst))
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
        let mut composed = self
            .iter()
            .map(|(param, ty)| (*param, ty.with_substitutions(rhs)))
            .collect::<Vec<_>>();

        composed.extend(rhs.iter().map(|(param, ty)| (*param, ty.clone())));

        Substitutions(composed)
    }

    fn remove(&mut self, param: TypeParameter) {
        self.0.retain(|(tp, ..)| param != *tp);
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

pub type Term = namer::SymbolName<namer::QualifiedName, namer::Identifier>;

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RecordShape(Vec<parser::Identifier>);

impl RecordShape {
    fn from_record_type(record: &RecordType) -> Self {
        Self(
            record
                .0
                .iter()
                .map(|(id, _)| id.clone())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>(),
        )
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
        self.0
            .entry(RecordShape::from_record_type(record_type))
            .or_default()
            .push(name);
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

    fn lookup(&self, name: &namer::QualifiedName) -> Option<&TypeConstructor> {
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
    pub fn normalize_type_application(&self, ty: &Type) -> Typing<Type> {
        if let Type::Constructor(..) | Type::Apply { .. } = ty {
            self.reduce_applied_constructor(ty, &mut vec![])
        } else {
            Ok(ty.clone())
        }
    }

    fn reduce_applied_constructor(
        &self,
        applied: &Type,
        arguments: &mut Vec<Type>,
    ) -> Typing<Type> {
        match applied {
            Type::Constructor(name) => {
                let constructor = self
                    .types
                    .lookup(name)
                    .ok_or_else(|| TypeError::UndefinedType(name.clone()))?;

                if constructor.arity() != arguments.len() {
                    Err(TypeError::WrongArity {
                        constructor: constructor.definition().name.clone(),
                        was: arguments.clone(),
                        expected: constructor.arity(),
                    })?;
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
                self.reduce_applied_constructor(constructor, arguments)
            }

            _ => Ok(applied.clone()),
        }
    }

    pub fn with_substitutions(&self, subs: &Substitutions) -> Self {
        Self {
            types: self.types.with_substitutions(subs),
            terms: TermEnvironment {
                bound: Self::substitute_bound(&self.terms.bound, subs),
                free: Self::substitute_free(&self.terms.free, subs),
            },
        }
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
                if let Type::Record(image) = &constructor.structure {
                    println!(
                        "elaborate_type_constructors: {image} -> {}",
                        constructor.definition.name
                    );
                    self.types
                        .record_shapes
                        .insert(image, constructor.definition.name.clone());
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
            // How in the f is this supposed to work?
            // Just push and hope they get the correct DeBruijn index?
            // Assertion here that  self.terms.bound.len() == id?
            Identifier::Bound(id) => {
                println!(
                    "bind_term: {id} -> {scheme}, pushed at {}",
                    self.terms.bound.len()
                );
                self.terms.bound.push(scheme)
            }
            Identifier::Free(name) => self.bind_free_term(name, scheme),
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
                    panic!("Bad medicine")
                }
                self.terms.bound.push(scheme);
                let v = block(self);
                self.terms.bound.pop();
                v
            }

            namer::Identifier::Free(id) => {
                let previous = self.terms.free.insert(id.clone(), scheme);
                let v = block(self);
                if let Some(previous) = previous {
                    self.terms.free.insert(id, previous);
                } else {
                    self.terms.free.remove(&id);
                }
                v
            }
        }
    }

    //    pub fn check_expr(&mut self, expected_type: TypeScheme, expr: &UntypedExpr) -> Typing<()> {
    //        match expr {
    //            UntypedExpr::Variable(_, _) => todo!(),
    //            UntypedExpr::Constant(_, literal) => todo!(),
    //            UntypedExpr::RecursiveLambda(_, self_referential) => todo!(),
    //            UntypedExpr::Lambda(_, lambda) => {
    //                let expected_type = expected_type.instantiate();
    //                todo!()
    //            }
    //            UntypedExpr::Apply(_, apply) => todo!(),
    //            UntypedExpr::Let(_, binding) => todo!(),
    //            UntypedExpr::Tuple(_, tuple) => todo!(),
    //            UntypedExpr::Record(_, record) => todo!(),
    //            UntypedExpr::Project(_, projection) => todo!(),
    //            UntypedExpr::Sequence(_, sequence) => todo!(),
    //        }
    //    }

    pub fn infer_expr(&mut self, expr: &UntypedExpr) -> Typing {
        //        println!("infer_expr: {expr}");

        match expr {
            UntypedExpr::Variable(pi, name) => Ok((
                Substitutions::default(),
                Expr::Variable(
                    TypeInfo {
                        parse_info: *pi,
                        inferred_type: self
                            .terms
                            .lookup(name)
                            .ok_or_else(|| TypeError::UndefinedName(name.clone()))?
                            .instantiate(),
                    },
                    name.clone(),
                ),
            )),

            UntypedExpr::Constant(pi, literal) => Ok((
                Substitutions::default(),
                Expr::Constant(
                    TypeInfo {
                        parse_info: *pi,
                        inferred_type: literal.synthesize_type(),
                    },
                    literal.clone(),
                ),
            )),

            UntypedExpr::RecursiveLambda(pi, rec_lambda) => {
                self.infer_recursive_lambda(pi, rec_lambda)
            }

            UntypedExpr::Lambda(pi, lambda) => {
                let (substitutions, typing_info, lambda) = self.infer_lambda(pi, lambda)?;
                Ok((substitutions, Expr::Lambda(typing_info, lambda)))
            }

            UntypedExpr::Apply(pi, ast::Apply { function, argument }) => {
                self.infer_apply(pi, function, argument)
            }

            UntypedExpr::Let(pi, binding) => self.infer_binding(pi, binding),

            UntypedExpr::Record(pi, record) => self.infer_record(pi, record),

            UntypedExpr::Tuple(pi, tuple) => self.infer_tuple(pi, tuple),

            UntypedExpr::Construct(pi, constructor) => {
                self.infer_coproduct_construct(pi, constructor)
            }

            UntypedExpr::Project(pi, projection) => self.infer_projection(pi, projection),

            UntypedExpr::Sequence(_pi, sequence) => self.infer_sequence(sequence),

            UntypedExpr::Deconstruct(pi, deconstruct) => {
                self.infer_deconstruction(*pi, deconstruct)
            }
        }
    }

    fn infer_deconstruction(&mut self, pi: ParseInfo, deconstruct: &namer::Deconstruct) -> Typing {
        let (mut substitutions, scrutinee) = self.infer_expr(&deconstruct.scrutinee)?;
        let scrutinee_type = &scrutinee.type_info().inferred_type;
        let mut alternates = deconstruct.alternates.iter();
        let mut typed_alternates = Vec::with_capacity(deconstruct.alternates.len());

        if let Some(clause) = alternates.next() {
            let mut consequent_type = {
                let mut clause_ctx = self.clone();
                let mut bindings = HashMap::default();
                let (subs1, pattern) =
                    clause_ctx.infer_pattern(&clause.pattern, &mut bindings, scrutinee_type)?;
                let mut clause_ctx = clause_ctx.with_substitutions(&subs1);
                for (binding, ty) in bindings {
                    clause_ctx.bind_term(binding, TypeScheme::from_constant(ty));
                }
                let (subs, expr) = clause_ctx.infer_expr(&clause.consequent)?;
                substitutions = substitutions.compose(&subs).compose(&subs1);
                let consequent_type = expr
                    .type_info()
                    .inferred_type
                    .with_substitutions(&substitutions);
                typed_alternates.push(MatchClause {
                    pattern,
                    consequent: expr.into(),
                });
                consequent_type
            };

            for clause in alternates {
                let mut clause_ctx = self.clone();
                let mut bindings = HashMap::default();
                let (subs1, pattern) =
                    clause_ctx.infer_pattern(&clause.pattern, &mut bindings, scrutinee_type)?;
                let mut clause_ctx = clause_ctx.with_substitutions(&subs1);
                for (binding, ty) in bindings {
                    clause_ctx.bind_term(binding, TypeScheme::from_constant(ty));
                }
                let (subs, expr) = clause_ctx.infer_expr(&clause.consequent)?;
                substitutions = substitutions.compose(&subs).compose(&subs1);
                let subs = expr
                    .type_info()
                    .inferred_type
                    .with_substitutions(&substitutions)
                    .unifed_with(&consequent_type)?;
                consequent_type = consequent_type.with_substitutions(&subs);
                typed_alternates.push(MatchClause {
                    pattern,
                    consequent: expr.into(),
                });
            }

            Ok((
                substitutions,
                Expr::Deconstruct(
                    TypeInfo {
                        parse_info: pi,
                        inferred_type: consequent_type,
                    },
                    Deconstruct {
                        scrutinee: scrutinee.clone().into(),
                        alternates: typed_alternates,
                    },
                ),
            ))
        } else {
            panic!("Now wtf?")
        }
    }

    fn infer_pattern(
        &mut self,
        pattern: &namer::Pattern,
        bindings: &mut HashMap<namer::Identifier, Type>,
        scrutinee: &Type,
    ) -> Typing<(Substitutions, Pattern)> {
        let normalized_scrutinee = self.normalize_type_application(&scrutinee)?;

        match (pattern, &normalized_scrutinee) {
            (namer::Pattern::Coproduct(pi, pattern), Type::Coproduct(coproduct)) => {
                if let namer::Identifier::Free(constructor) = &pattern.constructor
                    && let Some(signature) = coproduct.signature(constructor)
                    && pattern.arguments.len() == signature.len()
                {
                    // I want to do something here to make sure that the signature
                    // and the patterns match in count.

                    let (substitutions, arguments) = signature
                        .iter()
                        .zip(&pattern.arguments)
                        .map(|(scrutinee, pattern)| {
                            self.infer_pattern(pattern, bindings, scrutinee)
                        })
                        .collect::<Typing<Vec<_>>>()?
                        .into_iter()
                        .fold(
                            (Substitutions::default(), vec![]),
                            |(substitutions, mut arguments), (sub, argument)| {
                                (substitutions.compose(&sub), {
                                    arguments.push(argument);
                                    arguments
                                })
                            },
                        );

                    Ok((
                        substitutions,
                        Pattern::Coproduct(
                            TypeInfo {
                                parse_info: *pi,
                                inferred_type: scrutinee.clone(),
                            },
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

            (namer::Pattern::Tuple(_pi, _pattern), _ty) => todo!(),

            (namer::Pattern::Struct(_pi, _pattern), _ty) => todo!(),

            // Check pattern at ty
            (namer::Pattern::Literally(pi, pattern), ..) => {
                let inferred = pattern.synthesize_type();
                let subs = inferred.unifed_with(&scrutinee)?;

                Ok((
                    subs,
                    Pattern::Literally(
                        TypeInfo {
                            parse_info: *pi,
                            inferred_type: inferred,
                        },
                        pattern.clone(),
                    ),
                ))
            }

            (namer::Pattern::Bind(pi, pattern), ..) => {
                bindings.insert(pattern.clone(), scrutinee.clone());
                Ok((
                    Substitutions::default(),
                    Pattern::Bind(
                        TypeInfo {
                            parse_info: *pi,
                            inferred_type: scrutinee.clone(),
                        },
                        pattern.clone(),
                    ),
                ))
            }

            (pattern, ty) => panic!("Type error. Illegal pattern."),
        }
    }

    fn infer_coproduct_construct(
        &mut self,
        pi: &ParseInfo,
        construct: &namer::Construct,
    ) -> Typing {
        let (substitutions, typed_arguments, argument_types) =
            self.infer_several(&construct.arguments)?;

        for ty in &typed_arguments {
            println!("infer_coproduct_construct: typed argument {}", ty);
        }

        for x in &argument_types {
            println!("infer_coproduct_construct: argument type {}", x);
        }

        // Does it try more than one alternative if there are more? Pick the one
        // with the best type? I could encode the name of the type constructor
        // as a type of prefix to the constructor

        // TODO: namer::Identifier is a shit type for this purpose
        let constructor_name = construct.constructor.try_as_free().ok_or_else(|| {
            TypeError::InternalAssertion(format!(
                "expected Identifier::Free, was: {}",
                construct.constructor
            ))
        })?;

        let candidates = self
            .types
            .query_coproduct_type_constructors(constructor_name)?;

        let type_constructor = candidates
            // It could go for the first constructor that unifies
            // but it is probably better to crash here and ask
            // the user to qualify the name with a <Coproduct name>.<Constructor name>
            // type of deal
            .first()
            .ok_or_else(|| TypeError::NoSuchCoproductConstructor(constructor_name.clone()))?;

        let type_constructor = type_constructor.instantiate(self)?;

        let subs = if let Type::Coproduct(coproduct) = type_constructor.structure()? {
            println!(
                "infer_coproduct_construct: coproduct {coproduct:?}, argument typrs {argument_types:?}"
            );
            let signature = coproduct
                .signature(constructor_name)
                .ok_or_else(|| TypeError::NoSuchCoproductConstructor(constructor_name.clone()))?;
            Type::Tuple(TupleType::from_signature(signature))
                .unifed_with(&Type::Tuple(TupleType::from_signature(&argument_types)))?
        } else {
            Err(TypeError::InternalAssertion(format!("Expected ")))?
        };

        Ok((
            substitutions.compose(&subs),
            Expr::Construct(
                // ParseInfo::with_inferred_type(self, ...) in typer.rs
                TypeInfo {
                    parse_info: *pi,
                    // I think this is incorrect - this must become
                    // a TypeScheme with the correct quantification
                    inferred_type: type_constructor.make_spine().with_substitutions(&subs),
                },
                Construct {
                    constructor: construct.constructor.clone(),

                    // Pick out the Type::Product so that its
                    // elements can be put here
                    arguments: typed_arguments,
                },
            ),
        ))
    }

    fn infer_record(&mut self, pi: &ParseInfo, record: &namer::Record) -> Typing {
        let mut substitutions = Substitutions::default();
        let mut fields = Vec::with_capacity(record.fields.len());

        for (label, initializer) in &record.fields {
            let (subs, field) = self.infer_expr(initializer)?;
            fields.push((label, field));
            substitutions = substitutions.compose(&subs);
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
            .query_record_type_constructor(&RecordShape::from_record_type(&record_type));

        let type_constructor = type_constructors
            .first()
            .ok_or_else(|| TypeError::NoSuchRecordType(record_type.clone()))?;

        // This is needed for coproducts too
        let type_constructor = type_constructor.instantiate(self)?;

        let subs = type_constructor
            .structure()?
            .unifed_with(&Type::Record(record_type))?;

        Ok((
            substitutions.compose(&subs),
            Expr::Record(
                TypeInfo {
                    parse_info: *pi,
                    // I think this is incorrect - this must become
                    // a TypeScheme with the correct quantification
                    inferred_type: type_constructor.make_spine().with_substitutions(&subs),
                },
                Record { fields },
            ),
        ))
    }

    fn infer_projection(&mut self, pi: &ParseInfo, projection: &namer::Projection) -> Typing {
        let (substitutions, base) = self.infer_expr(&projection.base)?;
        let base_type = &base.type_info().inferred_type;
        let normalized_base_type = self.normalize_type_application(base_type)?;

        println!("infer_projection: {normalized_base_type}");

        match &projection.select {
            ProductElement::Name(field) => {
                if let Type::Record(record) = &normalized_base_type {
                    if let Some((field_index, (_, field_type))) = record
                        .0
                        .iter()
                        .enumerate()
                        .find(|(_, (label, _))| label == field)
                    {
                        Ok((
                            substitutions,
                            Expr::Project(
                                TypeInfo {
                                    parse_info: *pi,
                                    inferred_type: field_type.clone(),
                                },
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
                        })
                    }
                } else {
                    panic!("{base_type}")
                }
            }

            ProductElement::Ordinal(ordinal) => match normalized_base_type {
                Type::Tuple(tuple) => {
                    if let Some(element) = tuple.elements().get(*ordinal) {
                        Ok((
                            substitutions,
                            Expr::Project(
                                TypeInfo {
                                    parse_info: *pi,
                                    inferred_type: element.clone(),
                                },
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
                        })?
                    }
                }

                Type::Variable(..) => {
                    println!("infer_projection: Am i audible?");
                    let mut elems = Vec::with_capacity(ordinal + 1);
                    for _ in 0..=*ordinal {
                        elems.push(Type::fresh());
                    }
                    let tuple_ty = Type::Tuple(TupleType::from_signature(&elems));
                    let subs = base_type.unifed_with(&tuple_ty)?;
                    let projected_ty = match tuple_ty.with_substitutions(&subs) {
                        Type::Tuple(tuple) => tuple.elements()[*ordinal].clone(),
                        _ => unreachable!(),
                    };
                    Ok((
                        substitutions.compose(&subs),
                        Expr::Project(
                            TypeInfo {
                                parse_info: *pi,
                                inferred_type: projected_ty,
                            },
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
                }),
            },
        }
    }

    fn infer_tuple(&mut self, parse_info: &ParseInfo, tuple: &namer::Tuple) -> Typing {
        let (substitutions, elements, element_types) = self.infer_several(&tuple.elements)?;

        Ok((
            substitutions,
            Expr::Tuple(
                TypeInfo {
                    parse_info: *parse_info,
                    inferred_type: Type::Tuple(TupleType::from_signature(&element_types)),
                },
                Tuple { elements },
            ),
        ))
    }

    fn infer_several(
        &mut self,
        elements: &Vec<Tree<ParseInfo, Identifier>>,
    ) -> Typing<(Substitutions, Vec<Tree<TypeInfo, Identifier>>, Vec<Type>)> {
        let mut substitutions = Substitutions::default();
        let mut typed_elements = Vec::with_capacity(elements.len());

        for element in elements {
            let (subs, element) = self.infer_expr(element)?;
            typed_elements.push(element);
            // compose_mut?
            substitutions = substitutions.compose(&subs);
            *self = self.with_substitutions(&substitutions);
        }

        let typed_elements = typed_elements
            .iter()
            .map(|e| e.with_substitutions(&substitutions).into())
            .collect::<Vec<_>>();

        let element_types = typed_elements
            .iter()
            .map(|e: &Tree<TypeInfo, namer::Identifier>| e.type_info().inferred_type.clone())
            .collect();

        Ok((substitutions, typed_elements, element_types))
    }

    fn infer_recursive_lambda(
        &mut self,
        parse_info: &ParseInfo,
        rec_lambda: &namer::SelfReferential,
    ) -> Typing {
        let own_ty = Type::fresh();
        self.bind_term_and_then(
            rec_lambda.own_name.clone(),
            TypeScheme::from_constant(own_ty.clone()),
            |ctx| {
                ctx.bind_term_and_then(
                    rec_lambda.lambda.parameter.clone(),
                    TypeScheme::from_constant(Type::fresh()),
                    |ctx| {
                        let (substitutions, type_info, lambda) =
                            ctx.infer_lambda(parse_info, &rec_lambda.lambda)?;

                        let own_ty = own_ty.with_substitutions(&substitutions);
                        let substitutions = type_info
                            .inferred_type
                            .unifed_with(&own_ty)?
                            .compose(&substitutions);

                        let underlying = lambda.with_substitutions(&substitutions);

                        let typing_info = TypeInfo {
                            inferred_type: own_ty.with_substitutions(&substitutions),
                            ..type_info
                        };
                        Ok((
                            substitutions,
                            Expr::RecursiveLambda(
                                typing_info,
                                SelfReferential {
                                    own_name: rec_lambda.own_name.clone(),
                                    lambda: underlying,
                                },
                            ),
                        ))
                    },
                )
            },
        )
    }

    fn infer_apply(
        &mut self,
        parse_info: &ParseInfo,
        function: &namer::Expr,
        argument: &namer::Expr,
    ) -> Typing {
        let (function_subs, function) = self.infer_expr(function)?;
        let mut ctx = self.with_substitutions(&function_subs);

        let (argument_subs, argument) = ctx.infer_expr(argument)?;
        let return_ty = Type::fresh();

        let expected_ty = Type::Arrow {
            domain: argument.type_info().inferred_type.clone().into(),
            codomain: return_ty.clone().into(),
        };

        let substitutions = function_subs.compose(&argument_subs);

        let substitutions = expected_ty
            .with_substitutions(&substitutions)
            .unifed_with(&function.type_info().inferred_type)?
            .compose(&substitutions);

        let apply = Apply {
            function: function.with_substitutions(&substitutions).into(),
            argument: argument.with_substitutions(&substitutions).into(),
        };

        let inferred_type = return_ty.with_substitutions(&substitutions);

        Ok((
            substitutions,
            Expr::Apply(
                TypeInfo {
                    parse_info: *parse_info,
                    inferred_type,
                },
                apply,
            ),
        ))
    }

    fn infer_lambda(
        &mut self,
        parse_info: &ParseInfo,
        lambda: &namer::Lambda,
    ) -> Typing<(Substitutions, TypeInfo, Lambda)> {
        let domain = Type::fresh();
        self.bind_term_and_then(
            lambda.parameter.clone(),
            TypeScheme::from_constant(domain.clone()),
            |ctx| {
                let (substitutions, body) = ctx.infer_expr(&lambda.body)?;
                let inferred_type = Type::Arrow {
                    domain: domain.with_substitutions(&substitutions).into(),
                    codomain: body
                        .type_info()
                        .inferred_type
                        .with_substitutions(&substitutions)
                        .into(),
                };
                let body = body.with_substitutions(&substitutions);
                Ok((
                    substitutions,
                    TypeInfo {
                        parse_info: *parse_info,
                        inferred_type,
                    },
                    Lambda {
                        parameter: lambda.parameter.clone(),
                        body: body.into(),
                    },
                ))
            },
        )
    }

    fn infer_binding(&mut self, parse_info: &ParseInfo, binding: &namer::Binding) -> Typing {
        let (bound_subs, bound) = self.infer_expr(&binding.bound)?;
        let bound_type = bound
            .type_info()
            .inferred_type
            .generalize(&self.with_substitutions(&bound_subs));

        self.bind_term_and_then(binding.binder.clone(), bound_type, |ctx| {
            let (body_subs, body) = ctx.infer_expr(&binding.body)?;
            let substitutions = bound_subs.compose(&body_subs);

            let bound = bound.with_substitutions(&substitutions);
            let body = body.with_substitutions(&substitutions);

            Ok((
                substitutions,
                Expr::Let(
                    TypeInfo {
                        parse_info: *parse_info,
                        inferred_type: body.type_info().inferred_type.clone(),
                    },
                    Binding {
                        binder: binding.binder.clone(),
                        bound: bound.into(),
                        body: body.into(),
                    },
                ),
            ))
        })
    }

    fn infer_sequence(&mut self, sequence: &namer::Sequence) -> Typing {
        // Is it this simple?
        self.infer_expr(&sequence.this)?;
        self.infer_expr(&sequence.and_then)
    }

    fn free_variables(&self) -> HashSet<TypeParameter> {
        self.terms.free_variables()
    }
}

impl Literal {
    fn synthesize_type(&self) -> Type {
        Type::Base(match self {
            ast::Literal::Int(..) => BaseType::Int,
            ast::Literal::Text(..) => BaseType::Text,
        })
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

impl fmt::Display for BaseType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int => write!(f, "Int"),
            Self::Text => write!(f, "Text"),
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
            write!(f, ". ",)?;
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
