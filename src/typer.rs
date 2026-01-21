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
        namer::{
            self, DependencyMatrix, Identifier, QualifiedName, Symbol, SymbolName, SymbolTable,
            TermSymbol, TypeDefinition, TypeExpression, TypeSymbol,
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
pub type IfThenElse = ast::IfThenElse<TypeInfo, namer::Identifier>;
pub type Interpolate = ast::Interpolate<TypeInfo, namer::Identifier>;
pub type Segment = ast::Segment<TypeInfo, namer::Identifier>;
pub type MatchClause = ast::pattern::MatchClause<TypeInfo, namer::Identifier>;
pub type Pattern = ast::pattern::Pattern<TypeInfo, namer::Identifier>;
pub type ConstructorPattern = ast::pattern::ConstructorPattern<TypeInfo, namer::Identifier>;
pub type StructPattern = ast::pattern::StructPattern<TypeInfo, namer::Identifier>;
pub type TuplePattern = ast::pattern::TuplePattern<TypeInfo, namer::Identifier>;

pub type RecordSymbol = namer::RecordSymbol<namer::QualifiedName>;
pub type CoproductSymbol = namer::CoproductSymbol<namer::QualifiedName>;

type TypedSymbol = namer::Symbol<TypeInfo, namer::QualifiedName, namer::Identifier>;
type TypedSymbolTable = namer::SymbolTable<TypeInfo, namer::QualifiedName, namer::Identifier>;

fn display_list<A>(sep: &str, xs: &[A]) -> String
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
            println!(
                "dependency_matrix: {id} depends on [{:?}]",
                symbol.dependencies()
            );
            matrix.add_edge(id.clone(), symbol.dependencies().into_iter().collect());
        }

        matrix
    }
}

impl namer::TypeSignature {
    pub fn scheme(&self, ctx: &TypingContext) -> Typing<TypeScheme> {
        let type_params = self
            .universal_quantifiers
            .iter()
            .map(|id| (id.clone(), TypeParameter::fresh()))
            .collect::<HashMap<_, _>>();

        Ok(TypeScheme {
            quantifiers: type_params.values().cloned().collect(),
            underlying: self.body.synthesize_type(&type_params, ctx)?,
        })
    }
}

impl namer::NamedSymbolTable {
    pub fn compute_types(self, evaluation_order: Iter<&SymbolName>) -> Typing<TypedSymbolTable> {
        let mut ctx = TypingContext::default();
        let mut symbols = HashMap::with_capacity(self.symbols.len());

        // Enter types
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

        // Enter terms
        for (id, symbol) in evaluation_order
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
                namer::Symbol::Term(symbol) => Self::compute_term_symbol(symbol, &mut ctx)?,
                namer::Symbol::Type(symbol) => namer::Symbol::Type(symbol.clone()),
            };

            symbols.insert(id.clone(), symbol);
        }

        Ok(SymbolTable {
            module_members: self.module_members,
            member_modules: self.member_modules,
            symbols,
            imports: self.imports,
        })
    }

    fn compute_term_symbol(
        symbol: &TermSymbol<ParseInfo, namer::QualifiedName, Identifier>,
        ctx: &mut TypingContext,
    ) -> Typing<TypedSymbol> {
        let body = if let Some(type_signature) = &symbol.type_signature {
            let (subs, body) = ctx.infer_expr(symbol.body())?;

            ctx.substitute_mut(&subs);

            let inferred_type = body.type_info().inferred_type.with_substitutions(&subs);
            let inferred_scheme = inferred_type.generalize(ctx);

            let type_scheme = type_signature.scheme(ctx)?;

            type_scheme
                .instantiate()
                .check_instance_of(body.type_info().parse_info, &inferred_scheme)?;

            let qualified_name = symbol.name.clone();
            println!("typer: {qualified_name} => {inferred_scheme}, <== {type_scheme}");

            ctx.bind_free_term(qualified_name, type_scheme);
            body
        } else {
            let (_, body) = ctx.infer_expr(&symbol.body())?;

            let qualified_name = symbol.name.clone();
            let inferred_type = &body.type_info().inferred_type;
            let scheme = inferred_type.generalize(&ctx);
            println!("typer: {qualified_name} => {scheme}");

            ctx.bind_free_term(qualified_name, scheme);
            body
        };

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
}

impl TypeError {
    pub fn at(self, pi: ParseInfo) -> Located<Self> {
        Located {
            parse_info: pi,
            error: self,
        }
    }
}

pub type Typing<A = (Substitutions, Expr)> = Result<A, Located<TypeError>>;

#[derive(Debug, Error)]
pub struct Located<E>
where
    E: fmt::Debug,
{
    pub parse_info: ParseInfo,
    pub error: E,
}

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

    fn arity(&self) -> usize {
        self.0.len()
    }

    fn fields(&self) -> &[(parser::Identifier, Type)] {
        &self.0
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

    pub fn check_instance_of(&self, pi: ParseInfo, scheme: &TypeScheme) -> Typing<()> {
        let instantiated_signature = scheme.instantiate();

        let subs = instantiated_signature
            .unified_with(self)
            .map_err(|e| e.at(pi))?;

        println!("check_instance_of: scheme {instantiated_signature}, self {self}, subs {subs}");

        Ok(())
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

                println!("unifed_with: {} ~ {}", display_list("; ", lhs.elements()), display_list("; ", rhs.elements()));

                for (lhs, rhs) in lhs.elements().iter().zip(rhs.elements()) {
                    // compose_mut
                    subs = subs.compose(&lhs.with_substitutions(&subs).unified_with(&rhs.with_substitutions(&subs))?);
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

            (lhs, rhs) => Err(TypeError::UnificationImpossible { lhs: lhs.clone(), rhs: rhs.clone() }),
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

    fn structure(&self) -> Result<&Type, TypeError> {
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

    pub fn from_constant(ty: Type) -> TypeScheme {
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
    pub fn normalize_type_application(&self, pi: ParseInfo, ty: &Type) -> Typing<Type> {
        if let Type::Constructor(..) | Type::Apply { .. } = ty {
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
                    .ok_or_else(|| TypeError::UndefinedType(name.clone()).at(pi))?;

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

                Ok(constructor
                    .structure()
                    .map_err(|e| e.at(pi))?
                    .with_substitutions(&subs))
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
            Identifier::Bound(..) => self.terms.bound.push(scheme),
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

    fn check_expr(&mut self, expected_type: &Type, expr: &UntypedExpr) -> Typing<Expr> {
        println!("check_expr: expected {expected_type} for {expr}");

        match expr {
            UntypedExpr::Lambda(pi, lambda) => {
                let normalized_type = self.normalize_type_application(*pi, expected_type)?;
                if let Type::Arrow { domain, codomain } = normalized_type {
                    self.bind_term_and_then(
                        lambda.parameter.clone(),
                        TypeScheme::from_constant(*domain.clone()),
                        |ctx| {
                            let body = ctx.check_expr(&codomain, &lambda.body)?;

                            let inferred_type = Type::Arrow {
                                domain: domain.into(),
                                codomain: codomain.into(),
                            };

                            Ok(Expr::Lambda(
                                TypeInfo {
                                    parse_info: *pi,
                                    inferred_type: inferred_type,
                                },
                                Lambda {
                                    parameter: lambda.parameter.clone(),
                                    body: body.into(),
                                },
                            ))
                        },
                    )
                } else {
                    Err(TypeError::UnificationImpossible {
                        lhs: normalized_type.clone(),
                        rhs: Type::fresh(),
                    }
                    .at(*pi))?
                }
            }

            otherwise => {
                println!("check_expr: infer {expr}");
                let (subs1, expr) = self.infer_expr(expr)?;

                let lhs = expr.type_info().inferred_type.with_substitutions(&subs1);
                let rhs = expected_type.with_substitutions(&subs1);

                let subs2 = lhs
                    .unified_with(&rhs)
                    .map_err(|e| e.at(*otherwise.annotation()))?;

                let subs = subs1.compose(&subs2);

                self.substitute_mut(&subs);

                Ok(expr.with_substitutions(&subs))
            }
        }
    }

    #[instrument]
    pub fn infer_expr(&mut self, expr: &UntypedExpr) -> Typing {
        match expr {
            UntypedExpr::Variable(pi, name) => Ok((
                Substitutions::default(),
                Expr::Variable(
                    TypeInfo {
                        parse_info: *pi,
                        inferred_type: self
                            .terms
                            .lookup(name)
                            .ok_or_else(|| {
                                TypeError::UndefinedName {
                                    parse_info: *pi,
                                    name: name.clone(),
                                }
                                .at(*pi)
                            })?
                            .instantiate(),
                    },
                    name.clone(),
                ),
            )),

            UntypedExpr::InvokeBridge(pi, bridge) => Ok((
                Substitutions::default(),
                Expr::InvokeBridge(
                    TypeInfo {
                        parse_info: *pi,
                        inferred_type: bridge.external.type_scheme().instantiate(),
                    },
                    bridge.clone(),
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
                self.infer_recursive_lambda(*pi, rec_lambda)
            }

            UntypedExpr::Lambda(pi, lambda) => {
                let (substitutions, typing_info, lambda) = self.infer_lambda(*pi, lambda)?;
                Ok((substitutions, Expr::Lambda(typing_info, lambda)))
            }

            UntypedExpr::Apply(pi, ast::Apply { function, argument }) => {
                self.infer_apply(*pi, function, argument)
            }

            UntypedExpr::Let(pi, binding) => self.infer_binding(pi, binding),

            UntypedExpr::Record(pi, record) => self.infer_record(*pi, record),

            UntypedExpr::Tuple(pi, tuple) => self.infer_tuple(pi, tuple),

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
        }
    }

    #[instrument]
    fn infer_interpolation(&mut self, pi: ParseInfo, segments: &[namer::Segment]) -> Typing {
        let mut segs = vec![];
        let mut substitutions = Substitutions::default();

        for segment in segments {
            match segment {
                ast::Segment::Literal(pi, literal) => segs.push(Segment::Literal(
                    TypeInfo {
                        parse_info: *pi,
                        inferred_type: literal.synthesize_type(),
                    },
                    literal.clone(),
                )),
                ast::Segment::Expression(expr) => {
                    let (subs, expr) = self.infer_expr(&expr)?;
                    segs.push(ast::Segment::Expression(expr.into()));
                    substitutions = substitutions.compose(&subs);
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

        Ok((
            substitutions,
            Expr::Interpolate(
                TypeInfo {
                    parse_info: pi,
                    inferred_type: Type::Base(BaseType::Text),
                },
                ast::Interpolate(segs),
            ),
        ))
    }

    #[instrument]
    fn infer_deconstruction(&mut self, pi: ParseInfo, deconstruct: &namer::Deconstruct) -> Typing {
        let (mut substitutions, scrutinee) = self.infer_expr(&deconstruct.scrutinee)?;
        let scrutinee_type = &scrutinee.type_info().inferred_type;
        let mut match_clauses = deconstruct.match_clauses.iter();
        let mut typed_match_clauses = Vec::with_capacity(deconstruct.match_clauses.len());

        let mut clause_ctx = self.clone();
        if let Some(clause) = match_clauses.next() {
            let mut consequent_type = {
                let mut bindings = Vec::default();
                let (subs1, pattern) =
                    clause_ctx.infer_pattern(&clause.pattern, &mut bindings, scrutinee_type)?;
                clause_ctx.substitute_mut(&subs1);
                for (binding, ty) in bindings {
                    clause_ctx.bind_term(binding, TypeScheme::from_constant(ty));
                }
                let (subs, expr) = clause_ctx.infer_expr(&clause.consequent)?;
                substitutions = substitutions.compose(&subs).compose(&subs1);
                let consequent_type = expr.type_info().inferred_type.clone();
                typed_match_clauses.push(MatchClause {
                    pattern,
                    consequent: expr.into(),
                });
                consequent_type
            };

            for clause in match_clauses {
                clause_ctx = self.clone();
                let mut bindings = Vec::default();
                let scrutinee_type = &scrutinee_type.with_substitutions(&substitutions);
                let (pattern_subs, pattern) =
                    clause_ctx.infer_pattern(&clause.pattern, &mut bindings, scrutinee_type)?;
                clause_ctx.substitute_mut(&pattern_subs);
                for (binding, ty) in bindings {
                    clause_ctx.bind_term(binding, TypeScheme::from_constant(ty));
                }
                let (consequent_subs, expr) = clause_ctx.infer_expr(&clause.consequent)?;
                substitutions = substitutions
                    .compose(&pattern_subs)
                    .compose(&consequent_subs);

                let branch_subs = expr
                    .type_info()
                    .inferred_type
                    .with_substitutions(&substitutions)
                    .unified_with(&consequent_type.with_substitutions(&substitutions))
                    .map_err(|e| e.at(*&expr.annotation().parse_info))?;
                substitutions = substitutions.compose(&branch_subs);
                consequent_type = consequent_type.with_substitutions(&branch_subs);
                clause_ctx.substitute_mut(&substitutions);
                typed_match_clauses.push(MatchClause {
                    pattern,
                    consequent: expr.into(),
                });
            }

            trace!("substitutions: {substitutions}");

            Ok((
                substitutions,
                Expr::Deconstruct(
                    TypeInfo {
                        parse_info: pi,
                        inferred_type: consequent_type,
                    },
                    Deconstruct {
                        scrutinee: scrutinee.clone().into(),
                        match_clauses: typed_match_clauses,
                    },
                ),
            ))
        } else {
            panic!("Now wtf?")
        }
    }

    #[instrument]
    fn infer_pattern(
        &mut self,
        pattern: &namer::Pattern,
        bindings: &mut Vec<(namer::Identifier, Type)>,
        scrutinee: &Type,
    ) -> Typing<(Substitutions, Pattern)> {
        let pi = *pattern.annotation();
        let normalized_scrutinee = self.normalize_type_application(pi, &scrutinee)?;

        match (pattern, &normalized_scrutinee) {
            (namer::Pattern::Coproduct(_, coproduct_pattern), Type::Variable(p)) => {
                if let namer::Identifier::Free(constructor) = &coproduct_pattern.constructor {
                    let inferred = self
                        .types
                        .query_coproduct_type_constructors(&constructor)?
                        .first()
                        .ok_or_else(|| {
                            TypeError::NoSuchCoproductConstructor(constructor.clone()).at(pi)
                        })?
                        .instantiate(&self)?
                        .make_spine();

                    let substitutions = Substitutions::from(vec![(*p, inferred.clone())]);
                    println!("infer_pattern: subs {substitutions}");

                    self.substitute_mut(&substitutions);

                    println!("infer_pattern: calling with resolved {p} into {inferred}");
                    let (subs, pattern) = self.infer_pattern(pattern, bindings, &inferred)?;
                    Ok((subs.compose(&substitutions), pattern))
                } else {
                    todo!()
                }
            }

            (namer::Pattern::Coproduct(pi, pattern), Type::Coproduct(coproduct)) => {
                if let namer::Identifier::Free(constructor) = &pattern.constructor
                    && let Some(signature) = coproduct.signature(constructor)
                    && pattern.arguments.len() == signature.len()
                {
                    let mut arguments = Vec::with_capacity(signature.len());
                    let mut substitutions = Substitutions::default();

                    for (scrutinee, pattern) in signature.iter().zip(&pattern.arguments) {
                        let (subs, argument) = self.infer_pattern(pattern, bindings, scrutinee)?;
                        arguments.push(argument);
                        substitutions = substitutions.compose(&subs);
                    }

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

            (namer::Pattern::Tuple(pi, pattern), Type::Tuple(tuple))
                if pattern.elements.len() == tuple.arity() =>
            {
                let mut elements = Vec::with_capacity(tuple.arity());
                let mut substitutions = Substitutions::default();

                for (pattern, scrutinee) in pattern.elements.iter().zip(tuple.elements()) {
                    let (subs, element) = self.infer_pattern(pattern, bindings, scrutinee)?;
                    elements.push(element);
                    substitutions = substitutions.compose(&subs);
                }

                Ok((
                    substitutions,
                    Pattern::Tuple(
                        TypeInfo {
                            parse_info: *pi,
                            inferred_type: scrutinee.clone(),
                        },
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

                    let (subs, pattern) = self.infer_pattern(pattern, bindings, scrutinee)?;
                    arguments.push((pattern_field.clone(), pattern));
                    substitutions = substitutions.compose(&subs);
                }

                Ok((
                    substitutions,
                    Pattern::Struct(
                        TypeInfo {
                            parse_info: *pi,
                            inferred_type: scrutinee.clone(),
                        },
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
                bindings.push((pattern.clone(), scrutinee.clone()));
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

            (pattern, ty) => panic!("Type error. Illegal pattern. `{pattern}` `{ty}`"),
        }
    }

    #[instrument]
    fn infer_coproduct_construct(&mut self, pi: ParseInfo, construct: &namer::Construct) -> Typing {
        let (substitutions, typed_arguments, argument_types) =
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

        let subs = if let Type::Coproduct(coproduct) =
            type_constructor.structure().map_err(|e| e.at(pi))?
        {
            let signature = coproduct.signature(&construct.constructor).ok_or_else(|| {
                TypeError::NoSuchCoproductConstructor(construct.constructor.clone()).at(pi)
            })?;
            Type::Tuple(TupleType::from_signature(signature))
                .unified_with(&Type::Tuple(TupleType::from_signature(&argument_types)))
                .map_err(|e| e.at(pi))?
        } else {
            Err(TypeError::InternalAssertion(format!("Expected ")).at(pi))?
        };

        Ok((
            substitutions.compose(&subs),
            Expr::Construct(
                // ParseInfo::with_inferred_type(self, ...) in typer.rs
                TypeInfo {
                    parse_info: pi,
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

    #[instrument]
    fn infer_record(&mut self, pi: ParseInfo, record: &namer::Record) -> Typing {
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
            .ok_or_else(|| TypeError::NoSuchRecordType(record_type.clone()).at(pi))?;

        // This is needed for coproducts too
        let type_constructor = type_constructor.instantiate(self)?;

        let subs = type_constructor
            .structure()
            .map_err(|e| e.at(pi))?
            .unified_with(&Type::Record(record_type))
            .map_err(|e| e.at(pi))?;

        Ok((
            substitutions.compose(&subs),
            Expr::Record(
                TypeInfo {
                    parse_info: pi,
                    // I think this is incorrect - this must become
                    // a TypeScheme with the correct quantification
                    inferred_type: type_constructor.make_spine().with_substitutions(&subs),
                },
                Record { fields },
            ),
        ))
    }

    #[instrument]
    fn infer_projection(&mut self, pi: ParseInfo, projection: &namer::Projection) -> Typing {
        let (substitutions, base) = self.infer_expr(&projection.base)?;
        let base_type = &base.type_info().inferred_type;
        let normalized_base_type = self.normalize_type_application(pi, base_type)?;

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
                                    parse_info: pi,
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
                        Ok((
                            substitutions,
                            Expr::Project(
                                TypeInfo {
                                    parse_info: pi,
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
                        }
                        .at(pi))?
                    }
                }

                Type::Variable(..) => {
                    println!("infer_projection: Am i audible?");
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
                    Ok((
                        substitutions.compose(&subs),
                        Expr::Project(
                            TypeInfo {
                                parse_info: pi,
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
                }
                .at(pi)),
            },
        }
    }

    #[instrument]
    fn infer_tuple(&mut self, pi: &ParseInfo, tuple: &namer::Tuple) -> Typing {
        let (substitutions, elements, element_types) = self.infer_several(&tuple.elements)?;

        Ok((
            substitutions,
            Expr::Tuple(
                TypeInfo {
                    parse_info: *pi,
                    inferred_type: Type::Tuple(TupleType::from_signature(&element_types)),
                },
                Tuple { elements },
            ),
        ))
    }

    #[instrument]
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
            //            *self = self.with_substitutions(&substitutions);
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
                        let (substitutions, body) = ctx.infer_expr(&rec_lambda.lambda.body)?;
                        let subs2 = body
                            .type_info()
                            .inferred_type
                            .unified_with(&codomain.with_substitutions(&substitutions))
                            .map_err(|e| e.at(pi))?;
                        let substitutions = substitutions.compose(&subs2);

                        ctx.substitute_mut(&substitutions);

                        Ok((
                            substitutions.clone(),
                            Expr::RecursiveLambda(
                                TypeInfo {
                                    parse_info: pi,
                                    inferred_type: own_ty.with_substitutions(&substitutions),
                                },
                                SelfReferential {
                                    own_name: rec_lambda.own_name.clone(),
                                    lambda: Lambda {
                                        parameter: rec_lambda.lambda.parameter.clone(),
                                        body: body.into(),
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
    fn infer_apply(
        &mut self,
        pi: ParseInfo,
        function: &namer::Expr,
        argument: &namer::Expr,
    ) -> Typing {
        let (function_subs, function) = self.infer_expr(function)?;
        let mut ctx = self.with_substitutions(&function_subs);

        let (argument_subs, argument) = ctx.infer_expr(argument)?;
        let return_ty = Type::fresh();

        let substitutions = function_subs.compose(&argument_subs);

        let expected_ty = Type::Arrow {
            domain: argument
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
                    .type_info()
                    .inferred_type
                    .with_substitutions(&substitutions),
            )
            .map_err(|e| e.at(pi))?
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
                    parse_info: pi,
                    inferred_type,
                },
                apply,
            ),
        ))
    }

    #[instrument]
    fn infer_lambda(
        &mut self,
        pi: ParseInfo,
        lambda: &namer::Lambda,
    ) -> Typing<(Substitutions, TypeInfo, Lambda)> {
        let domain = Type::fresh();
        let codomain = Type::fresh();

        trace!("lambda-domain {domain}, codomain {codomain}");
        self.bind_term_and_then(
            lambda.parameter.clone(),
            TypeScheme::from_constant(domain.clone()),
            |ctx| {
                let (mut substitutions, body) = ctx.infer_expr(&lambda.body)?;

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

                Ok((
                    substitutions,
                    TypeInfo {
                        parse_info: pi,
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

    #[instrument]
    fn infer_binding(&mut self, pi: &ParseInfo, binding: &namer::Binding) -> Typing {
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
                        parse_info: *pi,
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

    #[instrument]
    fn infer_sequence(&mut self, sequence: &namer::Sequence) -> Typing {
        let (subs1, this) = self.infer_expr(&sequence.this)?;
        self.substitute_mut(&subs1);
        let (subs2, and_then) = self.infer_expr(&sequence.and_then)?;
        let substitutions = subs1.compose(&subs2);

        Ok((
            substitutions,
            Expr::Sequence(
                and_then.type_info().clone(),
                Sequence {
                    this: this.into(),
                    and_then: and_then.into(),
                },
            ),
        ))
    }

    #[instrument]
    fn infer_if_then_else(&mut self, pi: ParseInfo, if_then_else: &namer::IfThenElse) -> Typing {
        let (p_subs, predicate) = self.infer_expr(&if_then_else.predicate)?;
        let subs = predicate
            .type_info()
            .inferred_type
            .unified_with(&Type::Base(BaseType::Bool))
            .map_err(|e| e.at(pi))?;
        let p_subs = p_subs.compose(&subs);

        self.substitute_mut(&p_subs);
        let (c_subs, consequent) = self.infer_expr(&if_then_else.consequent)?;
        self.substitute_mut(&c_subs);
        let (a_subs, alternate) = self.infer_expr(&if_then_else.alternate)?;

        let subs = p_subs.compose(&c_subs).compose(&a_subs);

        let consequent_type = consequent
            .with_substitutions(&subs)
            .type_info()
            .inferred_type
            .clone();

        let substitutions = consequent_type
            .unified_with(
                &alternate
                    .with_substitutions(&subs)
                    .type_info()
                    .inferred_type,
            )
            .map_err(|e| e.at(pi))?;

        let substitutions = subs.compose(&substitutions);

        let predicate = predicate.with_substitutions(&substitutions);
        let consequent = consequent.with_substitutions(&substitutions);
        let alternate = alternate.with_substitutions(&substitutions);

        Ok((
            substitutions,
            Expr::If(
                TypeInfo {
                    parse_info: pi,
                    inferred_type: consequent_type,
                },
                IfThenElse {
                    predicate: predicate.into(),
                    consequent: consequent.into(),
                    alternate: alternate.into(),
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
            ast::Literal::Int(..) => BaseType::Int,
            ast::Literal::Text(..) => BaseType::Text,
            ast::Literal::Bool(..) => BaseType::Bool,
            ast::Literal::Unit => BaseType::Unit,
        })
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
