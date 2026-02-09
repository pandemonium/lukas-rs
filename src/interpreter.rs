use std::{
    cell::RefCell,
    collections::HashMap,
    fmt,
    rc::{Rc, Weak},
};

use thiserror::Error;

use crate::{
    ast::{
        self, Erased, Interpolate, ProductElement, Segment,
        namer::{self, Identifier},
        pattern::Pattern,
    },
    bridge::Bridge,
    parser, typer,
};

pub type Expr = ast::Expr<Erased, namer::Identifier>;
pub type Tree = Rc<Expr>;

// Erasing the annotation is not really done for a good reason here
impl Expr {
    pub fn reduce(self: &Tree, env: &Environment) -> Interpretation {
        // Plenty of clone calls here.
        match self.as_ref() {
            Self::Variable(_, the) => env
                .get(the)
                .ok_or_else(|| RuntimeError::NoSuchSymbol(the.clone())),

            Self::InvokeBridge(_, bridge) => Ok(Value::PartiallyAppliedBridge {
                bridge: bridge.clone().into(),
                arguments: vec![],
            }),

            Self::Constant(_, the) => Ok(Value::Constant(the.clone().into())),

            Self::RecursiveLambda(_, the) => {
                let closure = Closure::capture(env, &the.lambda.body);
                closure.borrow_mut().capture.put(Value::RecursiveClosure {
                    name: the.own_name.clone().into(),
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

            Self::Construct(_, the) => Ok(Value::Variant(
                VariantValue {
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

            Self::Ascription(_, the) => {
                // TODO: The typer could remove these on successful checks
                the.ascribed_tree.reduce(env)
            }
        }
    }
}

impl Pattern<Erased, namer::Identifier> {
    fn deconstruct(&self, scrutinee: &Value) -> Option<Vec<(Identifier, Value)>> {
        match (self, scrutinee) {
            (Self::Coproduct(_, pattern), Value::Variant(variant))
                if &pattern.constructor == &namer::Identifier::Free(variant.constructor.clone().into())  // W T F,
                && variant.arguments.len() == pattern.arguments.len() =>
            {
                let mut bindings = Vec::with_capacity(variant.arguments.len());

                for (pattern, scrutinee) in pattern.arguments.iter().zip(&variant.arguments) {
                    bindings.extend(pattern.deconstruct(&scrutinee)?);
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

    #[error("expected tuple, found: {0}")]
    ExpectedTuple(Value),

    #[error("{select} does not project {base}")]
    BadProjection { base: Value, select: ProductElement },

    #[error("expected at least one match")]
    ExpectedMatch,

    #[error("expired self referential: {0}")]
    ExpiredSelfReferential(String),

    #[error("function not applicable to {a} {b}")]
    NotApplicable2 { a: Value, b: Value },

    #[error("expected type {0}")]
    ExpectedType(typer::Type),

    #[error("late attempt at defining {of} to be {to}")]
    ForbiddenDefinition { of: namer::QualifiedName, to: Value },
}

pub type Interpretation<A = Value> = Result<A, RuntimeError>;

#[derive(Debug, Clone)]
enum Globals {
    Open(HashMap<namer::QualifiedName, Value>),
    Sealed(Rc<HashMap<namer::QualifiedName, Value>>),
}

impl Globals {
    fn sealed(self) -> Self {
        if let Self::Open(map) = self {
            Self::Sealed(map.into())
        } else {
            self
        }
    }

    fn define(&mut self, name: namer::QualifiedName, value: Value) -> Interpretation<()> {
        match self {
            Self::Open(values) => {
                values.insert(name, value);
                Ok(())
            }
            Self::Sealed(..) => Err(RuntimeError::ForbiddenDefinition {
                of: name,
                to: value,
            })?,
        }
    }

    fn lookup(&self, name: &namer::QualifiedName) -> Option<&Value> {
        match self {
            Globals::Open(defines) => defines.get(name),
            Globals::Sealed(defines) => defines.get(name),
        }
    }

    fn bindings(&self) -> impl Iterator<Item = (&namer::QualifiedName, &Value)> {
        match self {
            Globals::Open(defines) => defines.iter(),
            Globals::Sealed(defines) => defines.iter(),
        }
    }
}

impl Default for Globals {
    fn default() -> Self {
        Self::Open(HashMap::default())
    }
}

#[derive(Debug, Default, Clone)]
pub struct Environment {
    // initialize this structure from the compilation unit
    // namer:: here?
    inner: RefCell<EnvironmentInner>,
}

// Separate these two into an Environment and a Stack/ Locals
#[derive(Debug, Default, Clone)]
struct EnvironmentInner {
    globals: Globals,
    locals: Vec<Value>,
}

impl Environment {
    pub fn sealed(self) -> Self {
        let inner = self.inner.into_inner();
        Self {
            inner: EnvironmentInner {
                globals: inner.globals.sealed(),
                locals: inner.locals.clone(),
            }
            .into(),
        }
    }

    pub fn call(
        &self,
        symbol_name: &namer::QualifiedName,
        argument: ast::Literal,
    ) -> Interpretation {
        let symbol = self.get_global(symbol_name).ok_or_else(|| {
            RuntimeError::NoSuchSymbol(Identifier::Free(symbol_name.clone().into()))
        })?;

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
            Identifier::Free(id) => self.inner.borrow().globals.lookup(id).cloned(),
        }
    }

    fn get_global(&self, id: &namer::QualifiedName) -> Option<Value> {
        self.inner.borrow().globals.lookup(id).cloned()
    }

    pub fn define_global(&self, id: &namer::QualifiedName, value: Value) -> Interpretation<()> {
        self.inner.borrow_mut().globals.define(id.clone(), value)
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Constant(Literal),

    Closure(Rc<RefCell<Closure>>),

    RecursiveClosure {
        name: Box<namer::Identifier>,
        inner: Weak<RefCell<Closure>>,
    },

    PartiallyAppliedBridge {
        bridge: Box<Bridge>,
        arguments: Vec<Value>,
    },

    Product(Vec<Value>),

    Variant(Box<VariantValue>),
}

#[derive(Debug, Clone)]
pub struct VariantValue {
    constructor: Box<namer::QualifiedName>,
    arguments: Vec<Value>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    Int(i64),
    Text(String),
    Bool(bool),
    Unit,
}

enum AndThen {
    EvalArgument {
        argument: Tree,
        environment: Environment,
        k: Box<AndThen>,
    },

    Apply {
        function: Value,
        k: Box<AndThen>,
    },

    EvalLetBody {
        binder: Box<namer::Identifier>,
        body: Tree,
        environment: Environment,
        k: Box<AndThen>,
    },

    EvalTupleElement {
        input: Vec<Tree>,
        output: Vec<Value>,
        environment: Environment,
        k: Box<AndThen>,
    },

    EvalRecordField {
        input: Vec<(parser::Identifier, Tree)>,
        output: Vec<Value>,
        environment: Environment,
        k: Box<AndThen>,
    },

    EvalConstructor {
        input: Vec<Tree>,
        output: Vec<Value>,
        environment: Environment,
        constructor: namer::QualifiedName,
        k: Box<AndThen>,
    },

    EvalProjection {
        select: ProductElement,
        k: Box<AndThen>,
    },

    Eval {
        expression: Tree,
        environment: Environment,
        k: Box<AndThen>,
    },

    EvalDeconstruct {
        clauses: Vec<ast::pattern::MatchClause<Erased, Identifier>>,
        environment: Environment,
        k: Box<AndThen>,
    },

    EvalConditional {
        consequent: Rc<ast::Expr<Erased, Identifier>>,
        alternate: Rc<ast::Expr<Erased, Identifier>>,
        environment: Environment,
        k: Box<AndThen>,
    },

    EvalInterpolation {
        segments: Vec<Segment<Erased, Identifier>>,
        index: usize,
        environment: Environment,
        k: Box<AndThen>,
    },

    Hcf,
}

enum Suspension {
    Suspend(Suspended),
    Done(Value),
    Diverged(RuntimeError),
}

enum Suspended {
    Eval {
        expression: Tree,
        environment: Environment,
        k: AndThen,
    },
    Return {
        value: Value,
        k: AndThen,
    },
}

impl Suspension {
    fn resume(self) -> Self {
        match self {
            Self::Suspend(Suspended::Eval {
                expression,
                environment,
                k,
            }) => expression.eval(environment, k),

            Self::Suspend(Suspended::Return { value, k }) => and_then(value, k),

            done => done,
        }
    }

    fn return_and(value: Value, k: AndThen) -> Self {
        Suspension::Suspend(Suspended::Return { value, k })
    }

    fn eval_and(expr: &Tree, environment: Environment, k: AndThen) -> Self {
        Suspension::Suspend(Suspended::Eval {
            expression: Rc::clone(&expr),
            environment,
            k,
        })
    }
}

fn and_then(value: Value, k: AndThen) -> Suspension {
    match k {
        AndThen::EvalArgument {
            argument,
            environment,
            k,
        } => Suspension::Suspend(Suspended::Eval {
            expression: argument,
            environment,
            k: AndThen::Apply { function: value, k },
        }),

        AndThen::Apply { function, k } => match function {
            Value::Closure(c) => {
                let c = c.borrow();
                Suspension::Suspend(Suspended::Eval {
                    expression: Rc::clone(&c.body),
                    environment: {
                        let env = c.capture.clone();
                        env.put(value);
                        env
                    },
                    k: *k,
                })
            }

            Value::RecursiveClosure { name, inner } => match inner.upgrade() {
                Some(c) => {
                    let c = c.borrow();
                    Suspension::Suspend(Suspended::Eval {
                        expression: Rc::clone(&c.body),
                        environment: {
                            let env = c.capture.clone();
                            env.put(value);
                            env
                        },
                        k: *k,
                    })
                }

                None => {
                    Suspension::Diverged(RuntimeError::ExpiredSelfReferential(format!("{name}")))
                }
            },

            Value::PartiallyAppliedBridge {
                bridge,
                mut arguments,
            } => {
                arguments.push(value);

                if arguments.len() < bridge.external.arity() {
                    Suspension::return_and(Value::PartiallyAppliedBridge { bridge, arguments }, *k)
                } else {
                    match bridge.external.invoke(&arguments) {
                        Ok(r) => Suspension::return_and(r, *k),
                        Err(e) => Suspension::Diverged(e),
                    }
                }
            }

            otherwise => Suspension::Diverged(RuntimeError::ExpectedClosure(otherwise)),
        },

        AndThen::EvalLetBody {
            binder,
            body,
            environment,
            k,
        } => Suspension::Suspend(Suspended::Eval {
            expression: body,
            environment: {
                let env = environment.clone();
                // Could have a special env wrapper here that can be wrapped with "Cons cells"
                // for values to be added at eval
                env.put(value);
                env
            },
            k: *k,
        }),

        AndThen::EvalTupleElement {
            input,
            mut output,
            environment,
            k,
        } => {
            output.push(value);
            if output.len() < input.len() {
                Suspension::Suspend(Suspended::Eval {
                    expression: Rc::clone(&input[output.len()]),
                    environment: environment.clone(),
                    k: AndThen::EvalTupleElement {
                        input,
                        output,
                        environment,
                        k,
                    },
                })
            } else {
                Suspension::return_and(Value::Product(output), *k)
            }
        }

        AndThen::EvalRecordField {
            input,
            mut output,
            environment,
            k,
        } => {
            output.push(value);

            if output.len() < input.len() {
                Suspension::Suspend(Suspended::Eval {
                    expression: Rc::clone(&input[output.len()].1),
                    environment: environment.clone(),
                    k: AndThen::EvalRecordField {
                        input,
                        output,
                        environment,
                        k,
                    },
                })
            } else {
                Suspension::return_and(Value::Product(output), *k)
            }
        }

        AndThen::EvalConstructor {
            input,
            mut output,
            environment,
            constructor,
            k,
        } => {
            output.push(value);

            if output.len() < input.len() {
                Suspension::Suspend(Suspended::Eval {
                    expression: Rc::clone(&input[output.len()]),
                    environment: environment.clone(),
                    k: AndThen::EvalConstructor {
                        input,
                        output,
                        environment,
                        constructor,
                        k,
                    },
                })
            } else {
                Suspension::return_and(
                    Value::Variant(
                        VariantValue {
                            constructor: constructor.into(),
                            arguments: output,
                        }
                        .into(),
                    ),
                    *k,
                )
            }
        }

        AndThen::EvalProjection { select, k } => match (value, select) {
            (Value::Product(mut elements), ProductElement::Ordinal(ix)) => {
                Suspension::return_and(elements.swap_remove(ix), *k)
            }
            (base, select) => Suspension::Diverged(RuntimeError::BadProjection { base, select }),
        },

        AndThen::EvalDeconstruct {
            clauses,
            environment,
            k,
        } => {
            if let Some((bindings, consequent)) = clauses.into_iter().find_map(|clause| {
                clause
                    .pattern
                    .deconstruct(&value)
                    .map(|bindings| (bindings, clause.consequent))
            }) {
                let env = environment.clone();
                for (_, binding) in bindings {
                    env.put(binding);
                }

                Suspension::Suspend(Suspended::Eval {
                    expression: Rc::clone(&consequent),
                    environment: env,
                    k: *k,
                })
            } else {
                Suspension::Diverged(RuntimeError::ExpectedMatch)
            }
        }

        AndThen::Eval {
            expression,
            environment,
            k,
        } => Suspension::Suspend(Suspended::Eval {
            expression,
            environment,
            k: *k,
        }),

        AndThen::EvalConditional {
            consequent,
            alternate,
            environment,
            k,
        } => Suspension::Suspend(Suspended::Eval {
            expression: if let Value::Constant(Literal::Bool(true)) = value {
                Rc::clone(&consequent)
            } else {
                Rc::clone(&alternate)
            },
            environment,
            k: *k,
        }),

        AndThen::EvalInterpolation {
            segments,
            index,
            environment,
            k,
        } => {
            use std::fmt::Write as _;

            let Value::Constant(Literal::Text(mut buffer)) = value else {
                panic!("");
            };

            match &segments[index] {
                Segment::Literal(_, literal) => {
                    let _ = write!(buffer, "{literal}");
                    Suspension::return_and(Value::Constant(Literal::Text(buffer)), {
                        let index = 1 + index;
                        if index < segments.len() {
                            AndThen::EvalInterpolation {
                                segments,
                                index,
                                environment,
                                k,
                            }
                        } else {
                            *k
                        }
                    })
                }

                Segment::Expression(expr) => Suspension::Suspend(Suspended::Eval {
                    expression: Rc::clone(expr),
                    environment: environment.clone(),
                    k: {
                        let index = 1 + index;
                        if index < segments.len() {
                            AndThen::EvalInterpolation {
                                segments,
                                index,
                                environment,
                                k,
                            }
                        } else {
                            *k
                        }
                    },
                }),
            }
        }

        AndThen::Hcf => Suspension::Done(value),
    }
}

impl Expr {
    fn suspend(self: &Tree, environment: Environment) -> Suspension {
        Suspension::Suspend(Suspended::Eval {
            expression: self.clone(),
            environment,
            k: AndThen::Hcf.into(),
        })
    }

    // This should encode faults in the continuation instead of with a Result monad
    fn eval(self: &Tree, environment: Environment, k: AndThen) -> Suspension {
        match self.as_ref() {
            Self::Variable(_, the) => environment.get(the).map_or_else(
                || Suspension::Diverged(RuntimeError::NoSuchSymbol(the.clone())),
                |value| Suspension::Suspend(Suspended::Return { value, k }),
            ),

            Self::InvokeBridge(_, bridge) => Suspension::return_and(
                Value::PartiallyAppliedBridge {
                    bridge: bridge.clone().into(),
                    arguments: Vec::with_capacity(1),
                },
                k,
            ),

            Self::Constant(_, the) => {
                Suspension::return_and(Value::Constant(the.clone().into()), k)
            }

            Self::RecursiveLambda(_, the) => {
                let closure = Closure::capture(&environment, &the.lambda.body);
                closure.borrow_mut().capture.put(Value::RecursiveClosure {
                    name: the.own_name.clone().into(),
                    inner: Rc::downgrade(&closure),
                });
                Suspension::return_and(Value::Closure(Rc::clone(&closure)), k)
            }

            Self::Lambda(_, the) => {
                Suspension::return_and(Value::Closure(Closure::capture(&environment, &the.body)), k)
            }

            Self::Apply(_, the) => Suspension::Suspend(Suspended::Eval {
                expression: Rc::clone(&the.function),
                environment: environment.clone(),
                k: AndThen::EvalArgument {
                    argument: Rc::clone(&the.argument),
                    environment,
                    k: k.into(),
                },
            }),

            Self::Let(_, the) => Suspension::Suspend(Suspended::Eval {
                expression: Rc::clone(&the.bound),
                environment: environment.clone(),
                k: AndThen::EvalLetBody {
                    binder: the.binder.clone().into(),
                    body: the.body.clone(),
                    environment,
                    k: k.into(),
                },
            }),

            Self::Tuple(_, the) => Suspension::Suspend(Suspended::Eval {
                expression: Rc::clone(&the.elements[0]),
                environment: environment.clone(),
                k: AndThen::EvalTupleElement {
                    input: the.elements.clone(),
                    output: Vec::with_capacity(the.elements.len()),
                    environment,
                    k: k.into(),
                }
                .into(),
            }),

            Self::Record(_, the) => Suspension::Suspend(Suspended::Eval {
                expression: Rc::clone(&the.fields[0].1),
                environment: environment.clone(),
                k: AndThen::EvalRecordField {
                    input: the.fields.clone(),
                    output: Vec::with_capacity(the.fields.len()),
                    environment,
                    k: k.into(),
                },
            }),

            Self::Construct(_, the) => Suspension::Suspend(Suspended::Eval {
                expression: Rc::clone(&the.arguments[0]),
                environment: environment.clone(),
                k: AndThen::EvalConstructor {
                    input: the.arguments.clone(),
                    output: Vec::with_capacity(the.arguments.len()),
                    environment,
                    constructor: the.constructor.clone(),
                    k: k.into(),
                },
            }),

            Self::Project(_, the) => Suspension::Suspend(Suspended::Eval {
                expression: Rc::clone(&the.base),
                environment: environment,
                k: AndThen::EvalProjection {
                    select: the.select.clone(),
                    k: k.into(),
                },
            }),

            Self::Sequence(_, the) => Suspension::Suspend(Suspended::Eval {
                expression: Rc::clone(&the.this),
                environment: environment.clone(),
                k: AndThen::Eval {
                    expression: Rc::clone(&the.and_then),
                    environment,
                    k: k.into(),
                },
            }),

            Self::Deconstruct(_, the) => Suspension::Suspend(Suspended::Eval {
                expression: Rc::clone(&the.scrutinee),
                environment: environment.clone(),
                k: AndThen::EvalDeconstruct {
                    clauses: the.match_clauses.clone(),
                    environment,
                    k: k.into(),
                },
            }),

            Self::If(_, the) => Suspension::Suspend(Suspended::Eval {
                expression: Rc::clone(&the.predicate),
                environment: environment.clone(),
                k: AndThen::EvalConditional {
                    consequent: Rc::clone(&the.consequent),
                    alternate: Rc::clone(&the.alternate),
                    environment,
                    k: k.into(),
                },
            }),

            Self::Interpolate(_, the) => Suspension::return_and(
                Value::Constant(Literal::Text("".to_owned())),
                AndThen::EvalInterpolation {
                    segments: the.0.clone(),
                    index: 0,
                    environment,
                    k: k.into(),
                },
            ),

            Self::Ascription(_, the) => Suspension::Suspend(Suspended::Eval {
                expression: Rc::clone(&the.ascribed_tree),
                environment,
                k,
            }),
        }
    }
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
    body: Tree,
}

impl Closure {
    fn capture(capture: &Environment, body: &Tree) -> Rc<RefCell<Self>> {
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
            .bindings()
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
