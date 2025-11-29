use std::{
    cell::RefCell,
    collections::HashMap,
    fmt,
    rc::{Rc, Weak},
};

use crate::{
    ast::{
        self, Apply, CompilationUnit, Expr, ProductElement, Tree,
        namer::{self, Identifier, SymbolEnvironment},
    },
    parser::ParseInfo,
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
                if let Value::Closure(closure) = the.function.reduce(env)? {
                    apply_closure(closure, the.argument.reduce(env)?)
                } else {
                    Err(RuntimeError::ExpectedClosure(the.function.reduce(env)?))
                }
            }

            Self::Let(_, binding) => {
                env.bind(binding.bound.reduce(env)?, |env| binding.body.reduce(env))
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

fn apply_closure(closure: Rc<RefCell<Closure>>, argument: Value) -> Interpretation {
    let closure = closure.borrow();
    closure
        .capture
        .bind(argument, |env| closure.body.reduce(env))
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
    statics: HashMap<namer::ModuleMemberPath, Value>,
    locals: Vec<Value>,
}

impl Environment {
    pub fn call(&self, symbol: &namer::ModuleMemberPath, argument: ast::Literal) -> Value {
        if let Some(Value::Closure(closure)) = self.get_static(symbol) {
            apply_closure(closure, Value::Constant(argument.into())).unwrap()
        } else {
            // It did not find __root__/start
            todo!()
        }
    }

    fn bind<F, A>(&self, x: Value, mut f: F) -> A
    where
        F: FnMut(&Self) -> A,
    {
        {
            self.inner.borrow_mut().locals.push(x);
        }

        let v = f(self);

        {
            self.inner.borrow_mut().locals.pop();
        }

        v
    }

    fn put(&self, v: Value) {
        self.inner.borrow_mut().locals.push(v);
    }

    fn get(&self, id: &Identifier) -> Option<Value> {
        match id {
            Identifier::Bound(ix) => self.inner.borrow().locals.get(*ix).cloned(),
            Identifier::Free(id) => self.inner.borrow().statics.get(id).cloned(),
        }
    }

    fn get_static(&self, id: &namer::ModuleMemberPath) -> Option<Value> {
        // Wtf with the cloned here
        self.inner.borrow().statics.get(id).cloned()
    }

    fn put_static(&mut self, id: &namer::ModuleMemberPath, value: Value) {
        // ValueId is wrong here. It must be Name which has to
        // become resurrected.
        self.inner.borrow_mut().statics.insert(id.clone(), value);
    }

    // 1. Build symbol table
    // 2. Check all dependencies
    // 3. Resolve bindings
    // 4. Check types
    // 5. Insert checked values into statics in Environment
    pub fn typecheck_and_initialize(program: CompilationUnit<ParseInfo>) -> typer::Typing<Self> {
        let symbols = SymbolEnvironment::from(&program);
        let mut environment = Self {
            inner: EnvironmentInner::default().into(),
        };

        if symbols.dependencies_satisfiable() {
            for namer::ValueSymbol { name, body, .. } in
                symbols.with_computed_types()?.value_symbols()
            {
                let value = Rc::new(body.erase_annotation())
                    .reduce(&environment)
                    .expect("successful static init");

                environment.put_static(name, value);
            }
        } else {
            panic!("Bad dependencies")
        }

        Ok(environment)
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

    // Is this problem free?
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

        let local_prefix = env
            .locals
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
