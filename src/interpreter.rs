use std::{
    cell::RefCell,
    fmt,
    rc::{Rc, Weak},
};

use crate::ast::{
    self, Expr, ProductElement, Tree,
    namer::{self, Identifier},
};

impl Expr<(), namer::Identifier> {
    pub fn reduce(self: &Tree<(), namer::Identifier>, env: &Environment) -> Interpretation {
        // Plenty of clone calls here.
        match self.as_ref() {
            Self::Variable(_, the) => env
                .get(the)
                .ok_or_else(|| RuntimeError::NoSuchSymbol(the.clone())),
            Self::Constant(_, the) => Ok(Value::Constant(the.clone().into())),
            Self::RecursiveLambda(_, the) => {
                let closure = Closure::capture(env, &the.underlying.body);
                closure.borrow_mut().capture.put(Value::SelfReferential {
                    name: the.own_name.clone(),
                    inner: Rc::downgrade(&closure),
                });
                Ok(Value::Closure(Rc::clone(&closure)))
            }
            Self::Lambda(_, the) => Ok(Value::Closure(Closure::capture(env, &the.body))),
            Self::Apply(_, the) => {
                let argument = the.argument.reduce(env)?;
                let closure = the.function.reduce(env)?;

                if let Value::Closure(closure) = closure {
                    let closure = closure.borrow();
                    closure
                        .capture
                        .with_binding(argument, |env| closure.body.reduce(env))
                } else {
                    Err(RuntimeError::ExpectedClosure(closure))
                }
            }
            Self::Let(_, binding) => {
                env.with_binding(binding.bound.reduce(env)?, |env| binding.body.reduce(env))
            }
            Self::Tuple(_, the) => Ok(Value::Product(
                the.elements
                    .iter()
                    .map(|e| e.reduce(env))
                    .collect::<Interpretation<_>>()?,
            )),
            Self::Project(_, the) => match (the.base.reduce(env)?, &the.select) {
                (Value::Product(values), ProductElement::Ordinal(index)) => {
                    Ok(values[*index].clone())
                }
                (base, select) => panic!("projection off of {base:?} with {select:?}"),
            },
        }
    }
}

#[derive(Debug)]
pub enum RuntimeError {
    NoSuchSymbol(Identifier),
    ExpectedClosure(Value),
}

pub type Interpretation<A = Value> = Result<A, RuntimeError>;

#[derive(Debug, Default, Clone)]
pub struct Environment {
    // It should be static_values or somesuch.
    stack: RefCell<Vec<Value>>,
}

impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { stack } = self;
        let stack = stack.borrow();
        let stack_prefix = stack
            .iter()
            .take(5)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "{stack_prefix}")?;
        if stack.len() > 5 {
            write!(f, ", ...")
        } else {
            Ok(())
        }
    }
}

impl Environment {
    fn with_binding<F, A>(&self, x: Value, mut f: F) -> A
    where
        F: FnMut(&Self) -> A,
    {
        {
            self.stack.borrow_mut().push(x);
        }

        let v = f(self);

        {
            self.stack.borrow_mut().pop();
        }

        v
    }

    fn put(&self, v: Value) {
        self.stack.borrow_mut().push(v);
    }

    fn get(&self, id: &Identifier) -> Option<Value> {
        match id {
            Identifier::Bound(ix) => self.stack.borrow().get(*ix).cloned(),
            Identifier::Free(..) => todo!(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Constant(Literal),

    // Weird that both Closure and SelfReferential have to
    // have this structure
    Closure(Rc<RefCell<Closure>>),
    SelfReferential {
        name: namer::Identifier,
        inner: Weak<RefCell<Closure>>,
    },
    Product(Vec<Value>),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(x) => write!(f, "{x}"),
            Self::Closure(x) => write!(f, "`{}`", x.borrow()),
            Self::SelfReferential { name, inner } => {
                if let Some(inner) = inner.upgrade() {
                    write!(f, "/{name}/ {}", inner.borrow())
                } else {
                    write!(f, "/{name}/ {{ value since dropped }}")
                }
            }
            Self::Product(elements) => {
                let elements = elements
                    .iter()
                    .map(|el| el.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{elements}")
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum Literal {
    Int(i32),
    Text(String),
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(x) => write!(f, "{x}"),
            Self::Text(x) => write!(f, "{x}"),
        }
    }
}

impl From<ast::Literal> for Literal {
    fn from(value: ast::Literal) -> Self {
        match value {
            ast::Literal::Int(x) => Self::Int(x),
            ast::Literal::Text(x) => Self::Text(x),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Closure {
    capture: Environment,
    body: Tree<(), namer::Identifier>,
}

impl fmt::Display for Closure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { capture, body } = self;
        write!(f, "[ {capture} ]: {body}")
    }
}

impl Closure {
    fn capture(capture: &Environment, body: &Tree<(), namer::Identifier>) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            capture: capture.clone(),
            body: Rc::clone(body),
        }))
    }
}
