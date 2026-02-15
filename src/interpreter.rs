use std::{cell::RefCell, fmt, rc::Rc};

use thiserror::Error;

use crate::{
    ast::{
        self, Erased, Interpolate, ProductElement,
        namer::{self, Identifier},
        pattern::Pattern,
    },
    interpreter::cek::{Closure, Val, VariantVal},
    typer,
};

pub mod cek;

pub type Expr = ast::Expr<Erased, namer::Identifier>;
pub type Tree = Rc<Expr>;

// Erasing the annotation is not really done for a good reason here
impl Expr {
    pub fn reduce(self: &Tree, env: &Environment) -> Interpretation {
        // Plenty of clone calls here.
        match self.as_ref() {
            Self::Variable(_, the) => {
                let value = match the {
                    namer::Identifier::Bound(index) => env.local(*index),
                    namer::Identifier::Free(name) => env.global(name).cloned(),
                };
                value.ok_or_else(|| RuntimeError::NoSuchSymbol(the.clone()))
            }

            Self::InvokeBridge(_, bridge) => Ok(Val::PartiallyAppliedBridge {
                bridge: bridge.clone().into(),
                arguments: vec![],
            }),

            Self::Constant(_, the) => Ok(Val::Constant(the.clone().into())),

            Self::RecursiveLambda(_, the) => {
                let closure = Closure::capture(env, &the.lambda.body);
                closure.borrow().provide_argument(Val::RecursiveClosure {
                    name: the.own_name.clone().into(),
                    inner: Rc::downgrade(&closure),
                });
                Ok(Val::Closure(Rc::clone(&closure)))
            }

            Self::Lambda(_, the) => Ok(Val::Closure(Closure::capture(env, &the.body))),

            Self::Apply(_, the) => match the.function.reduce(env)? {
                Val::Closure(closure) => apply_closure(closure, the.argument.reduce(env)?),

                Val::RecursiveClosure { name, inner } => {
                    let closure = inner
                        .upgrade()
                        .ok_or_else(|| RuntimeError::ExpiredSelfReferential(format!("{name}")))?;
                    apply_closure(closure, the.argument.reduce(env)?)
                }

                Val::PartiallyAppliedBridge {
                    bridge,
                    mut arguments,
                } => {
                    arguments.push(the.argument.reduce(env)?);

                    if arguments.len() < bridge.external.arity() {
                        Ok(Val::PartiallyAppliedBridge { bridge, arguments })
                    } else {
                        Ok(bridge.external.invoke(&arguments)?)
                    }
                }

                otherwise => Err(RuntimeError::ExpectedClosure(otherwise)),
            },

            Self::Let(_, the) => {
                env.bind_and_then(the.bound.reduce(env)?, |env| the.body.reduce(env))
            }

            Self::Record(_, the) => Ok(Val::Product(
                the.fields
                    .iter()
                    .map(|(_, e)| e.reduce(env))
                    .collect::<Interpretation<_>>()?,
            )),

            Self::Tuple(_, the) => Ok(Val::Product(
                the.elements
                    .iter()
                    .map(|e| e.reduce(env))
                    .collect::<Interpretation<_>>()?,
            )),

            Self::Inject(_, the) => Ok(Val::Variant(
                VariantVal {
                    constructor: the.constructor.clone().into(),
                    arguments: the
                        .arguments
                        .iter()
                        .map(|e| e.reduce(env))
                        .collect::<Interpretation<Vec<_>>>()?,
                }
                .into(),
            )),

            Self::Project(_, the) => match (the.base.reduce(env)?, &the.select) {
                (Val::Product(values), ProductElement::Ordinal(index)) => {
                    Ok(values[*index].clone())
                }
                (base, select) => panic!("projection off of {base:?} with {select:?}"),
            },

            Self::Sequence(_, the) => {
                the.this.reduce(env)?;
                the.and_then.reduce(env)
            }

            Self::Deconstruct(_, the) => {
                let scrutinee = the.scrutinee.reduce(env)?;
                let (extraction, consequent) = the
                    .match_clauses
                    .iter()
                    .find_map(|match_clause| {
                        match_clause
                            .pattern
                            .deconstruct(&scrutinee)
                            .map(|bindings| (bindings, Rc::clone(&match_clause.consequent)))
                    })
                    .ok_or_else(|| RuntimeError::ExpectedMatch)?;
                env.bind_several_and_then(extraction.iter().map(|(_, v)| v.clone()), |env| {
                    consequent.reduce(env)
                })
            }

            Self::If(_, the) => {
                let predicate = the.predicate.reduce(env)?;

                if let Val::Constant(Literal::Bool(predicate)) = predicate {
                    if predicate {
                        the.consequent.reduce(env)
                    } else {
                        the.alternate.reduce(env)
                    }
                } else {
                    Err(RuntimeError::ExpectedType(typer::Type::Base(
                        typer::BaseType::Bool,
                    )))
                }
            }

            Self::Interpolate(_, the) => {
                use std::fmt::Write as _;
                let Interpolate(segments) = the;
                let mut rendering = String::new();

                for segment in segments {
                    match segment {
                        ast::Segment::Literal(_, literal) => {
                            let _ = write!(rendering, "{literal}");
                        }
                        ast::Segment::Expression(expr) => {
                            let value = expr.reduce(env)?;
                            let _ = write!(rendering, "{value}");
                        }
                    }
                }

                Ok(Val::Constant(Literal::Text(rendering)))
            }

            Self::Ascription(_, the) => {
                // TODO: The typer could remove these on successful checks
                the.ascribed_tree.reduce(env)
            }
        }
    }
}

impl Pattern<Erased, namer::Identifier> {
    fn deconstruct(&self, scrutinee: &Val) -> Option<Vec<(Identifier, Val)>> {
        match (self, scrutinee) {
            (Self::Coproduct(_, pattern), Val::Variant(variant))
                if &pattern.constructor == &namer::Identifier::Free(variant.constructor.clone().into())  // W T F,
                && variant.arguments.len() == pattern.arguments.len() =>
            {
                let mut bindings = Vec::with_capacity(variant.arguments.len());

                for (pattern, scrutinee) in pattern.arguments.iter().zip(&variant.arguments) {
                    bindings.extend(pattern.deconstruct(&scrutinee)?);
                }

                Some(bindings)
            }

            (Self::Tuple(_, pattern), Val::Product(elements))
                if pattern.elements.len() == elements.len() =>
            {
                let mut bindings = Vec::with_capacity(elements.len());

                for (pattern, scrutinee) in pattern.elements.iter().zip(elements) {
                    bindings.extend(pattern.deconstruct(scrutinee)?);
                }

                Some(bindings)
            }

            (Self::Struct(_, pattern), Val::Product(field_values))
                if pattern.fields.len() == field_values.len() =>
            {
                let mut bindings = Vec::with_capacity(field_values.len());

                for (pattern, scrutinee) in pattern
                    .fields
                    .iter()
                    .map(|(_, pattern)| pattern)
                    .zip(field_values)
                {
                    bindings.extend(pattern.deconstruct(scrutinee)?);
                }

                Some(bindings)
            }

            (Self::Literally(_, lhs), Val::Constant(rhs)) => {
                (&Literal::from(lhs.clone()) == rhs).then_some(vec![])
            }

            (Self::Bind(_, binder), x) => Some(vec![(binder.clone(), x.clone())]),

            _otherwise => None,
        }
    }
}

fn apply_closure(closure: Rc<RefCell<Closure>>, argument: Val) -> Interpretation {
    let closure = closure.borrow();
    let env = closure.capture.disjoint();
    env.bind_and_then(argument, |env| closure.body.reduce(env))
}

#[derive(Debug, Error)]
pub enum RuntimeError {
    #[error("no such symbol: {0}")]
    NoSuchSymbol(Identifier),

    #[error("expected closure, found: {0}")]
    ExpectedClosure(Val),

    #[error("expected tuple, found: {0}")]
    ExpectedTuple(Val),

    #[error("{select} does not project {base}")]
    BadProjection { base: Val, select: ProductElement },

    #[error("expected at least one match")]
    ExpectedMatch,

    #[error("expired self referential: {0}")]
    ExpiredSelfReferential(String),

    #[error("function not applicable to {a} {b}")]
    NotApplicable2 { a: Val, b: Val },

    #[error("expected type {0}")]
    ExpectedType(typer::Type),

    #[error("late attempt at defining {of} to be {to}")]
    ForbiddenDefinition { of: namer::QualifiedName, to: Val },
}

pub type Interpretation<A = Val> = Result<A, RuntimeError>;

pub type Environment = cek::Env;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    Int(i64),
    Text(String),
    Bool(bool),
    Unit,
}

impl From<ast::Literal> for Literal {
    fn from(value: ast::Literal) -> Self {
        match value {
            ast::Literal::Int(x) => Self::Int(x),
            ast::Literal::Text(x) => Self::Text(x),
            ast::Literal::Bool(x) => Self::Bool(x),
            ast::Literal::Unit => Self::Unit,
        }
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(x) => write!(f, "{x}"),
            Self::Text(x) => write!(f, "{x}"),
            Self::Bool(x) => write!(f, "{x}"),
            Self::Unit => write!(f, "()"),
        }
    }
}

impl fmt::Display for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(x) => write!(f, "{x}"),

            Self::Closure(x) => write!(f, "`{}`", x.borrow()),

            Self::RecursiveClosure { name, inner } => {
                if let Some(inner) = inner.upgrade() {
                    write!(f, "/{name}/ {}", inner.borrow())
                } else {
                    write!(f, "/{name}/ {{ Val since dropped }}")
                }
            }

            Self::PartiallyAppliedBridge { bridge, arguments } => {
                write!(f, "{} {:?}", bridge.qualified_name(), arguments)
            }

            Self::Product(elements) => {
                let elements = elements
                    .iter()
                    .map(|el| el.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{elements}")
            }

            Self::Variant(variant) => {
                write!(
                    f,
                    "({}{})",
                    variant.constructor,
                    variant
                        .arguments
                        .iter()
                        .map(|v| format!(" {v}"))
                        .collect::<Vec<_>>()
                        .join("")
                )
            }
        }
    }
}
