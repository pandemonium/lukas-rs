use std::{
    collections::{HashMap, HashSet},
    fmt,
    ops::Deref,
    sync::atomic::{AtomicU32, Ordering},
    vec,
};

use crate::{
    ast::{
        self, ProductElement, Tree,
        annotation::Annotated,
        namer::{self, Identifier},
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
// How does this handle parser::Identifier -> namer::Identifier for fields?
pub type Projection = ast::Projection<TypeInfo, namer::Identifier>;

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

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Variable(TypeParameter),
    Base(BaseType),
    Arrow {
        domain: Box<Type>,
        codomain: Box<Type>,
    },
    Tuple(Vec<Type>),
    Struct(Vec<(parser::Identifier, Type)>),
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
            Self::Struct(items) => {
                let struct_rendering = items
                    .iter()
                    .map(|(label, ty)| format!("{label} : {ty}"))
                    .collect::<Vec<_>>()
                    .join("; ");
                write!(f, "{{ {struct_rendering} }}")
            }
        }
    }
}

impl Type {
    pub fn fresh() -> Self {
        Self::Variable(TypeParameter::fresh())
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
            Self::Struct(items) => items.iter().flat_map(|(_, e)| e.variables()).collect(),
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
            Self::Struct(items) => Self::Struct(
                items
                    .iter()
                    .map(|(field, ty)| (field.clone(), ty.with_substitutions(subs)))
                    .collect(),
            ),
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

            (lhs, rhs) if lhs == rhs => Ok(Substitutions::default()),

            otherwise => panic!("{otherwise:?}"),
        }
    }

    pub fn generalize(&self, ctx: &TypingContext) -> TypeScheme {
        let ty_vars = self.variables();
        let ctx_bounds = ctx.free_variables();
        let quantified = ty_vars.difference(&ctx_bounds);

        TypeScheme {
            quantified: quantified.copied().collect(),
            underlying: self.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum BaseType {
    Int,
    Text,
}

impl fmt::Display for BaseType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int => write!(f, "Int"),
            Self::Text => write!(f, "Text"),
        }
    }
}

// This could contain more information, really. I would love to
// be able to go between some normalized form and a type constructor
// form easily
#[derive(Debug)]
pub struct TypeScheme {
    pub quantified: Vec<TypeParameter>,
    pub underlying: Type,
}

impl TypeScheme {
    pub fn with_substitutions(&self, subs: &Substitutions) -> Self {
        let mut subs = subs.clone();
        for q in &self.quantified {
            subs.remove(*q);
        }
        Self {
            quantified: self.quantified.clone(),
            underlying: self.underlying.with_substitutions(&subs),
        }
    }

    pub fn instantiate(&self) -> Type {
        let substitutions = self
            .quantified
            .iter()
            .map(|tp| (*tp, Type::fresh()))
            .collect::<Vec<_>>()
            .into();

        self.underlying.with_substitutions(&substitutions)
    }

    fn from_constant(ty: Type) -> TypeScheme {
        Self {
            quantified: vec![],
            underlying: ty,
        }
    }

    pub fn free_variables(&self) -> HashSet<TypeParameter> {
        let mut vars = self.underlying.variables();
        for q in &self.quantified {
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

#[derive(Debug)]
pub enum Term {
    Type(namer::Identifier),
    Value(namer::Identifier),
}

#[derive(Debug, Default)]
pub struct TermSpace {
    bound: Vec<TypeScheme>,
    free: HashMap<parser::Identifier, TypeScheme>,
}

impl TermSpace {
    pub fn lookup(&self, term: &namer::Identifier) -> Option<&TypeScheme> {
        match term {
            namer::Identifier::Bound(index) => Some(&self.bound[*index]),
            namer::Identifier::Free(identifier) => self.free.get(&identifier),
        }
    }
}

#[derive(Debug, Default)]
pub struct TypingContext {
    types: TermSpace,
    values: TermSpace,
}

impl TypingContext {
    pub fn with_substitutions(&self, subs: &Substitutions) -> Self {
        Self {
            types: TermSpace {
                bound: Self::substitute_bound(&self.types.bound, subs),
                free: Self::substitute_free(&self.types.free, subs),
            },
            values: TermSpace {
                bound: Self::substitute_bound(&self.values.bound, subs),
                free: Self::substitute_free(&self.values.free, subs),
            },
        }
    }

    fn substitute_bound(terms: &[TypeScheme], subs: &Substitutions) -> Vec<TypeScheme> {
        terms.iter().map(|ty| ty.with_substitutions(subs)).collect()
    }

    fn substitute_free(
        terms: &HashMap<parser::Identifier, TypeScheme>,
        subs: &Substitutions,
    ) -> HashMap<parser::Identifier, TypeScheme> {
        terms
            .iter()
            .map(|(k, v)| (k.clone(), v.with_substitutions(subs)))
            .collect()
    }

    pub fn lookup(&self, term: &Term) -> Option<&TypeScheme> {
        match term {
            Term::Type(name) => self.types.lookup(name),
            Term::Value(name) => self.values.lookup(name),
        }
    }

    pub fn bind<F, A>(&mut self, term: Term, scheme: TypeScheme, block: F) -> A
    where
        F: FnOnce(&mut TypingContext) -> A,
    {
        self.bindings(&term).push(scheme);
        let v = block(self);
        self.bindings(&term).pop();
        v
    }

    fn bindings(&mut self, term: &Term) -> &mut Vec<TypeScheme> {
        match *term {
            Term::Type(..) => &mut self.types.bound,
            Term::Value(..) => &mut self.values.bound,
        }
    }

    pub fn infer_type(&mut self, expr: &UntypedExpr) -> Typing {
        match expr {
            UntypedExpr::Variable(parse_info, name) => Ok((
                Substitutions::default(),
                Expr::Variable(
                    TypeInfo {
                        parse_info: *parse_info,
                        inferred_type: self
                            .values
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

            UntypedExpr::Tuple(parse_info, tuple) => self.infer_tuple(parse_info, tuple),

            UntypedExpr::Project(parse_info, projection) => {
                self.infer_projection(parse_info, projection)
            }
        }
    }

    fn infer_projection(
        &mut self,
        parse_info: &ParseInfo,
        projection: &ast::Projection<ParseInfo, namer::Identifier>,
    ) -> Typing {
        let (substitutions, base) = self.infer_type(&projection.base)?;
        match (&base.type_info().inferred_type, &projection.select) {
            (Type::Struct(items), ProductElement::Name(field)) => {
                if let Some((field_index, (_, field_type))) = items
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
            let (subs, element) = self.infer_type(element)?;
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
        self.bind(
            Term::Value(rec_lambda.own_name.clone()),
            TypeScheme::from_constant(own_ty.clone()),
            |ctx| {
                ctx.bind(
                    Term::Value(rec_lambda.underlying.parameter.clone()),
                    TypeScheme::from_constant(Type::fresh()),
                    |ctx| {
                        let (substitutions, type_info, lambda) =
                            ctx.infer_lambda(parse_info, &rec_lambda.underlying)?;

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
                                    underlying,
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
        let (function_subs, function) = self.infer_type(function)?;
        let mut ctx = self.with_substitutions(&function_subs);

        let (argument_subs, argument) = ctx.infer_type(argument)?;
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
        self.bind(
            Term::Value(lambda.parameter.clone()),
            TypeScheme::from_constant(domain.clone()),
            |ctx| {
                let (substitutions, body) = ctx.infer_type(&lambda.body)?;
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
        let (bound_subs, bound) = self.infer_type(&binding.bound)?;
        let bound_type = bound.type_info().inferred_type.generalize(self);

        // Term::Xxx is... not good.
        self.bind(Term::Value(binding.binder.clone()), bound_type, |ctx| {
            let (body_subs, body) = ctx.infer_type(&binding.body)?;
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

    fn free_variables(&self) -> HashSet<TypeParameter> {
        self.types
            .bound
            .iter()
            .flat_map(|ts| ts.free_variables())
            .chain(self.values.bound.iter().flat_map(|ts| ts.free_variables()))
            .collect()
    }
}
