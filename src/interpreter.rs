use std::{
    cell::RefCell,
    collections::HashMap,
    fmt,
    rc::{Rc, Weak},
};

use thiserror::Error;

use crate::{
    ast::{
        self, Expr, Interpolate, ProductElement, Tree,
        namer::{self, Identifier},
        pattern::Pattern,
    },
    bridge::Bridge,
    typer,
};

// Erasing the annotation is not really done for a good reason here
impl Expr<(), namer::Identifier> {
    pub fn reduce(self: &Tree<(), namer::Identifier>, env: &Environment) -> Interpretation {
        // Plenty of clone calls here.
        match self.as_ref() {
            Self::Variable(_, the) => env
                .get(the)
                .ok_or_else(|| RuntimeError::NoSuchSymbol(the.clone())),

            Self::InvokeBridge(_, bridge) => Ok(Value::PartiallyAppliedBridge {
                bridge: bridge.clone(),
                arguments: vec![],
            }),

            Self::Constant(_, the) => Ok(Value::Constant(the.clone().into())),

            Self::RecursiveLambda(_, the) => {
                let closure = Closure::capture(env, &the.lambda.body);
                closure.borrow_mut().capture.put(Value::RecursiveClosure {
                    name: the.own_name.clone(),
                    inner: Rc::downgrade(&closure),
                });
                Ok(Value::Closure(Rc::clone(&closure)))
            }

            Self::Lambda(_, the) => Ok(Value::Closure(Closure::capture(env, &the.body))),

            Self::Apply(_, the) => match the.function.reduce(env)? {
                Value::Closure(closure) => apply_closure(closure, the.argument.reduce(env)?),

                Value::RecursiveClosure { name, inner } => {
                    let closure = inner
                        .upgrade()
                        .ok_or_else(|| RuntimeError::ExpiredSelfReferential(format!("{name}")))?;
                    apply_closure(closure, the.argument.reduce(env)?)
                }

                Value::PartiallyAppliedBridge {
                    bridge,
                    mut arguments,
                } => {
                    arguments.push(the.argument.reduce(env)?);

                    if arguments.len() < bridge.external.arity() {
                        Ok(Value::PartiallyAppliedBridge { bridge, arguments })
                    } else {
                        Ok(bridge.external.invoke(&arguments)?)
                    }
                }

                otherwise => Err(RuntimeError::ExpectedClosure(otherwise)),
            },

            Self::Let(_, the) => {
                env.bind_and_then(the.bound.reduce(env)?, |env| the.body.reduce(env))
            }

            Self::Record(_, the) => Ok(Value::Product(
                the.fields
                    .iter()
                    .map(|(_, e)| e.reduce(env))
                    .collect::<Interpretation<_>>()?,
            )),

            Self::Tuple(_, the) => Ok(Value::Product(
                the.elements
                    .iter()
                    .map(|e| e.reduce(env))
                    .collect::<Interpretation<_>>()?,
            )),

            Self::Construct(_, the) => Ok(Value::Variant {
                coproduct: the.constructor.clone(),
                constructor: the.constructor.clone(),
                arguments: the
                    .arguments
                    .iter()
                    .map(|e| e.reduce(env))
                    .collect::<Interpretation<Vec<_>>>()?,
            }),

            Self::Project(_, the) => match (the.base.reduce(env)?, &the.select) {
                (Value::Product(values), ProductElement::Ordinal(index)) => {
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

                if let Value::Constant(Literal::Bool(predicate)) = predicate {
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

                Ok(Value::Constant(Literal::Text(rendering)))
            }

            Self::Annotation(_, the) => {
                // TODO: The typer could remove these on successful checks
                the.tree.reduce(env)
            }
        }
    }
}

impl Pattern<(), namer::Identifier> {
    fn deconstruct(&self, scrutinee: &Value) -> Option<Vec<(Identifier, Value)>> {
        match (self, scrutinee) {
            (
                Self::Coproduct(_, pattern),
                Value::Variant {
                    constructor,
                    arguments,
                    ..
                },
            ) if &pattern.constructor == &namer::Identifier::Free(constructor.clone())  // W T F,
                && arguments.len() == pattern.arguments.len() =>
            {
                let mut bindings = Vec::with_capacity(arguments.len());

                for (pattern, scrutinee) in pattern.arguments.iter().zip(arguments) {
                    bindings.extend(pattern.deconstruct(scrutinee)?);
                }

                Some(bindings)
            }

            (Self::Tuple(_, pattern), Value::Product(elements))
                if pattern.elements.len() == elements.len() =>
            {
                let mut bindings = Vec::with_capacity(elements.len());

                for (pattern, scrutinee) in pattern.elements.iter().zip(elements) {
                    bindings.extend(pattern.deconstruct(scrutinee)?);
                }

                Some(bindings)
            }

            (Self::Struct(_, pattern), Value::Product(field_values))
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

            (Self::Literally(_, lhs), Value::Constant(rhs)) => {
                (&Literal::from(lhs.clone()) == rhs).then_some(vec![])
            }

            (Self::Bind(_, binder), x) => Some(vec![(binder.clone(), x.clone())]),

            _otherwise => None,
        }
    }
}

fn apply_closure(closure: Rc<RefCell<Closure>>, argument: Value) -> Interpretation {
    let closure = closure.borrow();
    let env = closure.capture.clone();
    env.bind_and_then(argument, |env| closure.body.reduce(env))
}

#[derive(Debug, Error)]
pub enum RuntimeError {
    #[error("no such symbol: {0}")]
    NoSuchSymbol(Identifier),

    #[error("expected closure, found: {0}")]
    ExpectedClosure(Value),

    #[error("expected at least one match")]
    ExpectedMatch,

    #[error("expired self referential: {0}")]
    ExpiredSelfReferential(String),

    #[error("function not applicable to {a} {b}")]
    NotApplicable2 { a: Value, b: Value },

    #[error("expected type {0}")]
    ExpectedType(typer::Type),
}

pub type Interpretation<A = Value> = Result<A, RuntimeError>;

#[derive(Debug, Default, Clone)]
pub struct Environment {
    // initialize this structure from the compilation unit
    // namer:: here?
    inner: RefCell<EnvironmentInner>,
}

#[derive(Debug, Default, Clone)]
struct EnvironmentInner {
    globals: HashMap<namer::QualifiedName, Value>,
    locals: Vec<Value>,
}

impl Environment {
    pub fn call(
        &self,
        symbol_name: &namer::QualifiedName,
        argument: ast::Literal,
    ) -> Interpretation {
        let symbol = self
            .get_global(symbol_name)
            .ok_or_else(|| RuntimeError::NoSuchSymbol(Identifier::Free(symbol_name.clone())))?;

        match symbol {
            Value::Closure(closure) => apply_closure(closure, Value::Constant(argument.into())),
            Value::RecursiveClosure { inner, .. } => {
                let closure = inner.upgrade().ok_or_else(|| {
                    RuntimeError::ExpiredSelfReferential(format!("{symbol_name}"))
                })?;
                apply_closure(closure, Value::Constant(argument.into()))
            }
            otherwise => Err(RuntimeError::ExpectedClosure(otherwise)),
        }
    }

    fn bind_and_then<F, A>(&self, x: Value, mut block: F) -> A
    where
        F: FnMut(&Self) -> A,
    {
        {
            self.inner.borrow_mut().locals.push(x);
        }

        let v = block(self);

        {
            self.inner.borrow_mut().locals.pop();
        }

        v
    }

    fn bind_several_and_then<F, A>(&self, xs: impl Iterator<Item = Value>, mut block: F) -> A
    where
        F: FnMut(&Self) -> A,
    {
        let count = {
            let values = &mut self.inner.borrow_mut().locals;
            let baseline = values.len();
            values.extend(xs);
            values.len() - baseline
        };

        let v = block(self);

        {
            let values = &mut self.inner.borrow_mut().locals;
            values.truncate(values.len() - count);
        }

        v
    }

    fn put(&self, v: Value) {
        self.inner.borrow_mut().locals.push(v);
    }

    pub fn get(&self, id: &Identifier) -> Option<Value> {
        match id {
            Identifier::Bound(ix) => self.inner.borrow().locals.get(*ix).cloned(),
            Identifier::Free(id) => self.inner.borrow().globals.get(id).cloned(),
        }
    }

    fn get_global(&self, id: &namer::QualifiedName) -> Option<Value> {
        self.inner.borrow().globals.get(id).cloned()
    }

    pub fn define_global(&mut self, id: &namer::QualifiedName, value: Value) {
        self.inner.borrow_mut().globals.insert(id.clone(), value);
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Constant(Literal),

    // Weird that both Closure and SelfReferential have to
    // have this structure
    Closure(Rc<RefCell<Closure>>),

    RecursiveClosure {
        name: namer::Identifier,
        inner: Weak<RefCell<Closure>>,
    },

    PartiallyAppliedBridge {
        bridge: Bridge,
        arguments: Vec<Value>,
    },

    // Is this problem free?
    Product(Vec<Value>),

    Variant {
        // Work out what this ought to be
        coproduct: namer::QualifiedName,
        constructor: namer::QualifiedName,
        arguments: Vec<Value>,
    },
}

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

#[derive(Debug, Clone)]
pub struct Closure {
    capture: Environment,
    body: Tree<(), namer::Identifier>,
}

impl Closure {
    fn capture(capture: &Environment, body: &Tree<(), namer::Identifier>) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            capture: capture.clone(),
            body: Rc::clone(body),
        }))
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

impl fmt::Display for Closure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { capture, body } = self;
        write!(f, "[ {capture} ]: {body}")
    }
}

impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let env = self.inner.borrow();

        let local_prefix = env
            .locals
            .iter()
            .take(5)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(", ");

        let static_prefix = env
            .globals
            .iter()
            .take(5)
            .map(|(path, value)| format!("{path}: {value}"))
            .collect::<Vec<_>>()
            .join(",");

        write!(f, "static: {static_prefix}; bound: {local_prefix}")?;

        if env.locals.len() > 5 {
            write!(f, ", ...")
        } else {
            Ok(())
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(x) => write!(f, "{x}"),

            Self::Closure(x) => write!(f, "`{}`", x.borrow()),

            Self::RecursiveClosure { name, inner } => {
                if let Some(inner) = inner.upgrade() {
                    write!(f, "/{name}/ {}", inner.borrow())
                } else {
                    write!(f, "/{name}/ {{ value since dropped }}")
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

            Self::Variant {
                constructor,
                arguments,
                ..
            } => {
                write!(
                    f,
                    "({constructor}{})",
                    arguments
                        .iter()
                        .map(|v| format!(" {v}"))
                        .collect::<Vec<_>>()
                        .join("")
                )
            }
        }
    }
}
