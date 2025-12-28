use std::{
    collections::{BTreeSet, HashMap, HashSet},
    fmt,
    marker::PhantomData,
    ops::Deref,
    slice::Iter,
    sync::atomic::{AtomicU32, Ordering},
    vec,
};

use crate::{
    ast::{
        self, ProductElement, Tree,
        annotation::Annotated,
        namer::{
            self, CompilationContext, DependencyMatrix, Identifier, Symbol, SymbolName, TermSymbol,
            TypeDefinition, TypeExpression, TypeSymbol,
        },
    },
    parser::{self, ParseInfo},
};

type UntypedExpr = namer::Expr;
pub type Expr = ast::Expr<TypeInfo, namer::Identifier>;
pub type Apply = ast::Apply<TypeInfo, namer::Identifier>;
pub type RecursiveLambda = ast::SelfReferential<TypeInfo, namer::Identifier>;
pub type Lambda = ast::Lambda<TypeInfo, namer::Identifier>;
pub type Binding = ast::Binding<TypeInfo, namer::Identifier>;
pub type Tuple = ast::Tuple<TypeInfo, namer::Identifier>;
pub type Record = ast::Record<TypeInfo, namer::Identifier>;
pub type Projection = ast::Projection<TypeInfo, namer::Identifier>;

pub type RecordSymbol = namer::RecordSymbol<namer::QualifiedName>;

type TypedSymbol = namer::Symbol<TypeInfo, namer::QualifiedName, namer::Identifier>;
type TypedCompilationContext =
    namer::CompilationContext<TypeInfo, namer::QualifiedName, namer::Identifier>;

impl<A> CompilationContext<A, namer::QualifiedName, namer::Identifier>
where
    A: fmt::Debug,
{
    pub fn static_values(
        &self,
        order: Iter<&namer::TermId>,
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
        order: Iter<&namer::TermId>,
    ) -> Vec<&namer::TypeSymbol<namer::QualifiedName>> {
        self.extract_symbols(order, |sym| {
            if let namer::Symbol::Type(sym) = sym {
                Some(sym)
            } else {
                None
            }
        })
    }

    fn extract_symbols<F, Sym>(&self, terms: Iter<&namer::TermId>, select: F) -> Vec<&Sym>
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
        evaluation_order: Iter<&namer::TermId>,
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
        let (_, body) = ctx.infer_expr(&symbol.body)?;

        let qualified_name = &symbol.name;
        let inferred_type = &body.type_info().inferred_type;

        println!("{qualified_name}::{inferred_type}");

        ctx.bind_term(
            qualified_name.clone(),
            TypeScheme::from_constant(inferred_type.clone()),
        );

        Ok(namer::Symbol::Term(TermSymbol {
            name: symbol.name.clone(),
            type_signature: symbol.type_signature.clone(),
            body,
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
        self.map_annotation(move |ti| ti.with_substitutions(subs))
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
        was: usize,
        expected: usize,
    },
    UnelaboratedConstructor(namer::QualifiedName),
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
        fields.sort_by(|(p, ..), (q, ..)| p.cmp(q));
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Variable(TypeParameter),
    Base(BaseType),
    Arrow {
        domain: Box<Type>,
        codomain: Box<Type>,
    },
    Tuple(Vec<Type>),
    Record(RecordType),
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
            Self::Tuple(elements) => elements.iter().flat_map(|el| el.variables()).collect(),
            Self::Record(record) => record.0.iter().flat_map(|(_, e)| e.variables()).collect(),
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
            Self::Base(b) => Self::Base(b.clone()),
            Self::Arrow { domain, codomain } => Self::Arrow {
                domain: domain.with_substitutions(subs).into(),
                codomain: codomain.with_substitutions(subs).into(),
            },
            Self::Tuple(elements) => Self::Tuple(
                elements
                    .iter()
                    .map(|ty| ty.with_substitutions(subs))
                    .collect(),
            ),
            Self::Record(record) => Self::Record(record.clone().with_substitutions(subs)),
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

            (Self::Tuple(lhs), Self::Tuple(rhs)) if lhs.len() == rhs.len() => {
                let mut subs = Substitutions::default();

                println!("unify_with: {lhs:?} {rhs:?}");

                for (lhs, rhs) in lhs.iter().zip(rhs) {
                    // compose_mut
                    subs = subs.compose(&lhs.unifed_with(rhs)?);
                }

                Ok(subs)
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
        BUILTIN_BASE_TYPE_NAMES.iter().any(|&n| n == id)
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
                    .header()
                    .as_base_type()
                    .unwrap_or_else(|| constructor.type_apply_spine()))
            }

            Self::Parameter(_, p) => type_params
                .get(p)
                .copied()
                .map(Type::Variable)
                .ok_or_else(|| TypeError::UnquantifiedTypeParameter(p.clone())),

            Self::Apply(_, apply) => Ok(Type::Apply {
                constructor: apply.function.synthesize_type(type_params, ctx)?.into(),
                argument: apply.argument.synthesize_type(type_params, ctx)?.into(),
            }),

            Self::Arrow(_, arrow) => Ok(Type::Arrow {
                domain: arrow.domain.synthesize_type(type_params, ctx)?.into(),
                codomain: arrow.codomain.synthesize_type(type_params, ctx)?.into(),
            }),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ElaboratedConstructor {
    pub header: ConstructorHeader,
    pub structure: Type,
}

#[derive(Debug, Clone)]
pub struct ConstructorHeader {
    pub name: namer::QualifiedName,
    pub type_param_map: HashMap<parser::Identifier, TypeParameter>,
    pub symbol: TypeSymbol<namer::QualifiedName>,
}

impl ConstructorHeader {
    fn apply(&self) -> Type {
        self.type_param_map.iter().fold(
            Type::Constructor(self.name.clone()),
            |constructor, (_, at)| Type::Apply {
                constructor: constructor.into(),
                argument: Type::Variable(*at).into(),
            },
        )
    }

    fn as_base_type(&self) -> Option<Type> {
        if let TypeDefinition::Builtin(base_type) = self.symbol.definition {
            Some(Type::Base(base_type))
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub enum TypeConstructor {
    Unelaborated(ConstructorHeader),
    Elaborated(ElaboratedConstructor),
}

impl TypeConstructor {
    fn arity(&self) -> usize {
        self.header().symbol.arity
    }

    fn from_symbol(symbol: &TypeSymbol<namer::QualifiedName>) -> Self {
        if let TypeDefinition::Builtin(base_type) = &symbol.definition {
            Self::Elaborated(ElaboratedConstructor {
                header: ConstructorHeader {
                    name: symbol.qualified_name(),
                    type_param_map: HashMap::default(),
                    symbol: symbol.clone(),
                },
                structure: Type::Base(*base_type),
            })
        } else {
            Self::Unelaborated(ConstructorHeader {
                name: symbol.qualified_name(),
                type_param_map: symbol
                    .type_parameters()
                    .iter()
                    .map(|tp| (tp.clone(), TypeParameter::fresh()))
                    .collect(),
                symbol: symbol.clone(),
            })
        }
    }

    fn elaborate(&mut self, ctx: &TypingContext) -> Typing<()> {
        if let Self::Unelaborated(constructor) = self {
            let structure = match &constructor.symbol.definition {
                TypeDefinition::Record(record) => {
                    record.synthesize_type(&constructor.type_param_map, ctx)?
                }
                TypeDefinition::Coproduct(..) => todo!(),
                TypeDefinition::Builtin(base_type) => Type::Base(base_type.clone()),
            };

            *self = Self::Elaborated(ElaboratedConstructor {
                header: constructor.clone(),
                structure,
            });
        }

        Ok(())
    }

    fn with_substitutions(&self, subs: &Substitutions) -> Self {
        if let Self::Elaborated(constructor) = self {
            Self::Elaborated(ElaboratedConstructor {
                header: constructor.header.clone(),
                structure: constructor.structure.with_substitutions(subs),
            })
        } else {
            todo!()
        }
    }

    fn type_apply_spine(&self) -> Type {
        match self {
            Self::Unelaborated(header) => header.apply(),
            Self::Elaborated(constructor) => constructor.header.apply(),
        }
    }

    fn header(&self) -> &ConstructorHeader {
        match self {
            Self::Unelaborated(header) => header,
            Self::Elaborated(constructor) => &constructor.header,
        }
    }

    fn structure(&self) -> Option<&Type> {
        if let Self::Elaborated(c) = self {
            Some(&c.structure)
        } else {
            None
        }
    }
}

impl fmt::Display for TypeConstructor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unelaborated(header) => write!(f, "Suspended {}", header.symbol.qualified_name()),
            Self::Elaborated(constructor) => {
                write!(f, "{}", constructor.header.name)?;

                for (_, p) in &constructor.header.type_param_map {
                    write!(f, " {p}")?;
                }

                write!(f, " ::= {}", constructor.structure)
            }
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
        self.0.retain(|(tp, ..)| param == *tp);
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
pub struct TermSpace {
    bound: Vec<TypeScheme>,
    free: HashMap<namer::QualifiedName, TypeScheme>,
}

impl TermSpace {
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
struct RecordImage(Vec<parser::Identifier>);

impl RecordImage {
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

impl fmt::Display for RecordImage {
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
struct RecordTypeIndex(HashMap<RecordImage, Vec<namer::QualifiedName>>);

impl RecordTypeIndex {
    fn insert(&mut self, record_type: &RecordType, name: namer::QualifiedName) {
        self.0
            .entry(RecordImage::from_record_type(record_type))
            .or_default()
            .push(name);
    }

    fn matching(&self, image: &RecordImage) -> impl Iterator<Item = &namer::QualifiedName> {
        for (image, names) in &self.0 {
            for name in names {
                println!("matching: {image} -> {name}");
            }
        }

        self.0.get(image).into_iter().flatten()
    }
}

#[derive(Debug, Clone, Default)]
pub struct TypeSpace {
    bindings: HashMap<namer::QualifiedName, TypeConstructor>,
    // Is this the best datatype for this?
    record_type_index: RecordTypeIndex,
}

impl TypeSpace {
    fn bind(&mut self, name: namer::QualifiedName, tc: TypeConstructor) {
        self.bindings.insert(name, tc);
    }

    fn lookup(&self, name: &namer::QualifiedName) -> Option<&TypeConstructor> {
        self.bindings.get(name)
    }

    fn infer_record_type_constructor(&self, image: &RecordImage) -> Vec<&TypeConstructor> {
        self.record_type_index
            .matching(&image)
            .flat_map(|name| self.lookup(name))
            .collect()
    }

    fn with_substitutions(&self, subs: &Substitutions) -> Self {
        Self {
            bindings: self
                .bindings
                .iter()
                .map(|(id, tc)| (id.clone(), tc.with_substitutions(subs)))
                .collect(),
            record_type_index: self.record_type_index.clone(),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct TypingContext {
    types: TypeSpace,
    terms: TermSpace,
}

impl TypingContext {
    pub fn reduce_applied(&self, ty: Type) -> Typing<Type> {
        if let Type::Constructor(..) | Type::Apply { .. } = ty {
            self.reduce_applied_constructor(ty, &mut vec![])
        } else {
            Ok(ty)
        }
    }

    fn reduce_applied_constructor(&self, applied: Type, arguments: &mut Vec<Type>) -> Typing<Type> {
        match applied {
            Type::Constructor(name) => {
                let constructor = self
                    .types
                    .lookup(&name)
                    .ok_or_else(|| TypeError::UndefinedType(name.clone()))?;

                if constructor.arity() != arguments.len() {
                    Err(TypeError::WrongArity {
                        was: arguments.len(),
                        expected: constructor.arity(),
                    })?;
                }

                // Given (((f a) b) c), the recursion sees the outer
                // Apply node first.
                arguments.reverse();

                let header = constructor.header();
                let subs = Substitutions::from(
                    header
                        .symbol
                        .type_parameters()
                        .iter()
                        .map(|p| {
                            header
                                .type_param_map
                                .get(p)
                                .expect(&format!("Unmapped type parameter: {p}"))
                        })
                        .copied()
                        .into_iter()
                        .zip(arguments.drain(..))
                        .collect::<Vec<_>>(),
                );

                let structure = constructor
                    .structure()
                    .ok_or_else(|| TypeError::UnelaboratedConstructor(name.clone()))?;

                Ok(structure.with_substitutions(&subs))
            }

            Type::Apply {
                constructor,
                argument,
            } => {
                arguments.push(*argument);
                self.reduce_applied_constructor(*constructor, arguments)
            }

            _ => Ok(applied),
        }
    }

    pub fn with_substitutions(&self, subs: &Substitutions) -> Self {
        Self {
            types: self.types.with_substitutions(subs),
            terms: TermSpace {
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
                if let Type::Record(image) = &constructor.structure {
                    println!(
                        "elaborate_type_constructors: {image} -> {}",
                        constructor.header.name
                    );
                    self.types
                        .record_type_index
                        .insert(image, constructor.header.name.clone());
                }
            }
        }

        Ok(())
    }

    pub fn bind_type(&mut self, name: namer::QualifiedName, constructor: TypeConstructor) {
        self.types.bind(name, constructor);
    }

    pub fn bind_term(&mut self, name: namer::QualifiedName, scheme: TypeScheme) {
        self.terms.free.insert(name, scheme);
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
        match expr {
            UntypedExpr::Variable(parse_info, name) => Ok((
                Substitutions::default(),
                Expr::Variable(
                    TypeInfo {
                        parse_info: *parse_info,
                        inferred_type: self
                            .terms
                            .lookup(name)
                            .ok_or_else(|| TypeError::UndefinedName(name.clone()))?
                            .instantiate(),
                    },
                    name.clone(),
                ),
            )),

            UntypedExpr::Constant(parse_info, x) => Ok((
                Substitutions::default(),
                Expr::Constant(
                    TypeInfo {
                        parse_info: *parse_info,
                        inferred_type: Type::Base(match x {
                            ast::Literal::Int(..) => BaseType::Int,
                            ast::Literal::Text(..) => BaseType::Text,
                        }),
                    },
                    x.clone(),
                ),
            )),

            UntypedExpr::RecursiveLambda(parse_info, rec_lambda) => {
                self.infer_recursive_lambda(parse_info, rec_lambda)
            }

            UntypedExpr::Lambda(parse_info, lambda) => {
                let (substitutions, typing_info, lambda) = self.infer_lambda(parse_info, lambda)?;
                Ok((substitutions, Expr::Lambda(typing_info, lambda)))
            }

            UntypedExpr::Apply(parse_info, ast::Apply { function, argument }) => {
                self.infer_apply(parse_info, function, argument)
            }

            UntypedExpr::Let(parse_info, binding) => self.infer_binding(parse_info, binding),

            UntypedExpr::Record(parse_info, record) => self.infer_record(parse_info, record),

            UntypedExpr::Tuple(parse_info, tuple) => self.infer_tuple(parse_info, tuple),

            UntypedExpr::Project(parse_info, projection) => {
                self.infer_projection(parse_info, projection)
            }

            UntypedExpr::Sequence(_parse_info, sequence) => self.infer_sequence(sequence),
        }
    }

    fn infer_record(&mut self, parse_info: &ParseInfo, record: &namer::Record) -> Typing {
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
            .infer_record_type_constructor(&RecordImage::from_record_type(&record_type));
        let type_constructor = type_constructors
            .first()
            .ok_or_else(|| TypeError::NoSuchRecordType(record_type))?;

        Ok((
            substitutions,
            Expr::Record(
                TypeInfo {
                    parse_info: *parse_info,
                    inferred_type: type_constructor.type_apply_spine(),
                },
                Record { fields },
            ),
        ))
    }

    fn infer_projection(
        &mut self,
        parse_info: &ParseInfo,
        projection: &ast::Projection<ParseInfo, namer::Identifier>,
    ) -> Typing {
        let (substitutions, base) = self.infer_expr(&projection.base)?;
        match (&base.type_info().inferred_type, &projection.select) {
            (Type::Record(record), ProductElement::Name(field)) => {
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
                                parse_info: *parse_info,
                                inferred_type: field_type.clone(),
                            },
                            Projection {
                                base: base.into(),
                                select: ProductElement::Ordinal(field_index),
                            },
                        ),
                    ))
                } else {
                    let inferred_type = base.type_info().inferred_type.clone();
                    Err(TypeError::BadProjection {
                        projection: projection.clone(),
                        inferred_type,
                    })
                }
            }
            (ty, el) => panic!("{el:?} is not a member of {ty:?}"),
        }
    }

    fn infer_tuple(&mut self, parse_info: &ParseInfo, tuple: &namer::Tuple) -> Typing {
        let mut substitutions = Substitutions::default();
        let mut elements = Vec::with_capacity(tuple.elements.len());

        for element in &tuple.elements {
            let (subs, element) = self.infer_expr(element)?;
            elements.push(element);
            // compose_mut?
            substitutions = substitutions.compose(&subs);
        }

        let elements = elements
            .iter()
            .map(|e| e.with_substitutions(&substitutions).into())
            .collect::<Vec<_>>();

        let inferred_type = Type::Tuple(
            elements
                .iter()
                .map(|e: &Tree<TypeInfo, namer::Identifier>| e.type_info().inferred_type.clone())
                .collect(),
        );

        Ok((
            substitutions,
            Expr::Tuple(
                TypeInfo {
                    parse_info: *parse_info,
                    inferred_type,
                },
                Tuple { elements },
            ),
        ))
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
                                RecursiveLambda {
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
        let bound_type = bound.type_info().inferred_type.generalize(self);

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

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Variable(TypeParameter(p)) => write!(f, "${p}"),
            Self::Base(base_type) => write!(f, "{base_type}"),
            Self::Arrow { domain, codomain } => write!(f, "({domain} -> {codomain})"),
            Self::Tuple(items) => {
                let tuple_rendering = items
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
