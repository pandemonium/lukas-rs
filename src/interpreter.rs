use std::{
    cell::RefCell,
    collections::HashMap,
    fmt,
    rc::{Rc, Weak},
};

use crate::{
    ast::{
        self, CompilationUnit, Expr, ProductElement, Tree,
        namer::{self, Identifier, Symbols},
    },
    parser::ParseInfo,
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
                let closure = Closure::capture(env, &the.lambda.body);
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
    // initialize this structure from the compilation unit
    // namer:: here?
    inner: RefCell<EnvironmentInner>,
}

#[derive(Debug, Default, Clone)]
struct EnvironmentInner {
    statics: HashMap<namer::MemberPath, Value>,
    stack: Vec<Value>,
}

impl Environment {
    fn with_binding<F, A>(&self, x: Value, mut f: F) -> A
    where
        F: FnMut(&Self) -> A,
    {
        {
            self.inner.borrow_mut().stack.push(x);
        }

        let v = f(self);

        {
            self.inner.borrow_mut().stack.pop();
        }

        v
    }

    fn put(&self, v: Value) {
        self.inner.borrow_mut().stack.push(v);
    }

    fn get(&self, id: &Identifier) -> Option<Value> {
        match id {
            Identifier::Bound(ix) => self.inner.borrow().stack.get(*ix).cloned(),
            Identifier::Free(id) => self.inner.borrow().statics.get(id).cloned(),
        }
    }

    // This should be TypeInfo, right?
    // But where/ when does typing happen?
    pub fn from_compilation_unit(program: CompilationUnit<ParseInfo>) -> Self {
        let symbols = Symbols::from(&program);

        if symbols.dependencies_satisfiable() {
        } else {
        }

        todo!()
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

impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let env = self.inner.borrow();

        let stack_prefix = env
            .stack
            .iter()
            .take(5)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(", ");

        let static_prefix = env
            .statics
            .iter()
            .take(5)
            .map(|(path, value)| format!("{path}: {value}"))
            .collect::<Vec<_>>()
            .join(",");

        write!(f, "static: {static_prefix}; bound: {stack_prefix}")?;

        if env.stack.len() > 5 {
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
