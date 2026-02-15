use std::{
    cell::RefCell,
    collections::HashMap,
    fmt,
    rc::{Rc, Weak},
};

use crate::{
    ast::{
        self, Erased, ProductElement, Segment,
        namer::{self, QualifiedName},
    },
    bridge::Bridge,
    interpreter::{Expr, Interpretation, Literal, RuntimeError, Tree},
    parser,
};

#[derive(Debug, Clone)]
pub enum Val {
    Constant(Literal),

    Closure(Rc<RefCell<Closure>>),

    RecursiveClosure {
        name: Box<namer::Identifier>,
        inner: Weak<RefCell<Closure>>,
    },

    PartiallyAppliedBridge {
        bridge: Box<Bridge>,
        arguments: Vec<Val>,
    },

    Product(Vec<Val>),

    Variant(Box<VariantVal>),
}

#[derive(Debug, Clone)]
pub struct VariantVal {
    pub constructor: Box<namer::QualifiedName>,
    pub arguments: Vec<Val>,
}

#[derive(Debug)]
pub struct Closure {
    pub capture: Env,
    pub body: Tree,
}

impl Closure {
    pub fn capture(env: &Env, tree: &Tree) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            capture: env.disjoint(),
            body: Rc::clone(&tree),
        }))
    }

    pub fn provide_argument(&self, argument: Val) {
        self.capture.push_local(argument);
    }
}

impl fmt::Display for Closure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { capture, body } = self;
        write!(f, "[ {capture} ]: {body}")
    }
}

#[derive(Debug, Clone, Default)]
pub struct Globals(HashMap<QualifiedName, Val>);

// But this means that all functions essentally close over Globals thus far
// They should all share the same and it does not matter that what they own
// a reference to is modified underneeth, things cannot disappear from globals
impl Globals {
    fn lookup(&self, name: &QualifiedName) -> Option<&Val> {
        let Self(m) = self;
        m.get(name)
    }

    pub fn define(&mut self, name: QualifiedName, val: Val) {
        let Self(m) = self;
        m.insert(name, val);
    }

    fn bindings(&self) -> impl Iterator<Item = (&QualifiedName, &Val)> {
        let Self(m) = self;
        m.iter()
    }
}

#[derive(Debug, Default)]
pub struct Env {
    globals: Rc<Globals>,
    locals: Rc<RefCell<Vec<Val>>>,
}

impl Env {
    pub fn from_globals(globals: Globals) -> Self {
        Self {
            globals: Rc::new(globals),
            locals: Rc::new(RefCell::new(Vec::default())),
        }
    }

    pub fn shared(&self) -> Self {
        Self {
            globals: self.globals.clone(),
            locals: Rc::clone(&self.locals),
        }
    }

    pub fn disjoint(&self) -> Self {
        Self {
            globals: Rc::clone(&self.globals),
            locals: Rc::new(RefCell::new(self.locals.borrow().clone())),
        }
    }

    fn push_local(&self, x: Val) {
        self.locals.borrow_mut().push(x);
    }

    pub fn local(&self, index: usize) -> Option<Val> {
        self.locals.borrow().get(index).cloned()
    }

    fn pop_local(&self) -> Val {
        self.locals.borrow_mut().pop().unwrap()
    }

    pub fn global(&self, binder: &QualifiedName) -> Option<&Val> {
        self.globals.lookup(binder)
    }

    pub fn bind_and_then<F, A>(&self, x: Val, mut block: F) -> A
    where
        F: FnMut(&Self) -> A,
    {
        self.push_local(x);
        let v = block(self);
        self.pop_local();

        v
    }

    pub fn bind_several_and_then<F, A>(&self, xs: impl Iterator<Item = Val>, mut block: F) -> A
    where
        F: FnMut(&Self) -> A,
    {
        let count = {
            let values = &mut self.locals.borrow_mut();
            let baseline = values.len();
            values.extend(xs);
            values.len() - baseline
        };

        let v = block(self);

        {
            let values = &mut self.locals.borrow_mut();
            let len = values.len();
            values.truncate(len - count);
        }

        v
    }

    pub fn call(
        &self,
        symbol_name: &namer::QualifiedName,
        argument: ast::Literal,
    ) -> Interpretation<Val> {
        let symbol = self.global(symbol_name).ok_or_else(|| {
            RuntimeError::NoSuchSymbol(namer::Identifier::Free(symbol_name.clone().into()))
        })?;

        match symbol {
            Val::Closure(closure) => {
                let closure = closure.borrow();
                closure.provide_argument(Val::Constant(argument.into()));
                closure.body.interpret(closure.capture.shared())
            }

            Val::RecursiveClosure { inner, .. } => {
                let closure = inner.upgrade().ok_or_else(|| {
                    RuntimeError::ExpiredSelfReferential(format!("{symbol_name}"))
                })?;
                let closure = closure.borrow();
                closure.provide_argument(Val::Constant(argument.into()));
                closure.body.interpret(closure.capture.shared())
            }

            otherwise => Err(RuntimeError::ExpectedClosure(otherwise.clone())),
        }
    }
}

impl fmt::Display for Env {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let local_prefix = {
            self.locals
                .borrow()
                .iter()
                .take(5)
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        };

        let static_prefix = self
            .globals
            .bindings()
            .take(5)
            .map(|(path, value)| format!("{path}: {value}"))
            .collect::<Vec<_>>()
            .join(",");

        write!(f, "static: {static_prefix}; bound: {local_prefix}")?;

        if self.locals.borrow().len() > 5 {
            write!(f, ", ...")
        } else {
            Ok(())
        }
    }
}

enum AndThen {
    EvalArgument {
        argument: Tree,
        environment: Env,
        k: Box<AndThen>,
    },

    Apply {
        function: Val,
        k: Box<AndThen>,
    },

    EvalLetBody {
        body: Tree,
        environment: Env,
        k: Box<AndThen>,
    },

    EvalTupleElement {
        input: Rc<Vec<Tree>>,
        output: Vec<Val>,
        environment: Env,
        k: Box<AndThen>,
    },

    EvalRecordField {
        input: Rc<Vec<(parser::Identifier, Tree)>>,
        output: Vec<Val>,
        environment: Env,
        k: Box<AndThen>,
    },

    EvalConstructor {
        input: Rc<Vec<Tree>>,
        output: Vec<Val>,
        environment: Env,
        constructor: Box<namer::QualifiedName>,
        k: Box<AndThen>,
    },

    EvalProjection {
        select: ProductElement,
        k: Box<AndThen>,
    },

    Eval {
        expression: Tree,
        environment: Env,
        k: Box<AndThen>,
    },

    EvalDeconstruct {
        clauses: Rc<Vec<ast::pattern::MatchClause<Erased, namer::Identifier>>>,
        environment: Env,
        k: Box<AndThen>,
    },

    EvalConditional {
        consequent: Rc<ast::Expr<Erased, namer::Identifier>>,
        alternate: Rc<ast::Expr<Erased, namer::Identifier>>,
        environment: Env,
        k: Box<AndThen>,
    },

    EvalInterpolation {
        buffer: String,
        segments: Rc<Vec<Segment<Erased, namer::Identifier>>>,
        index: usize,
        environment: Env,
        k: Box<AndThen>,
    },

    Hcf,
}

enum Suspension {
    Suspend(Suspended),
    Done(Val),
    Diverged(RuntimeError),
}

enum Suspended {
    Eval {
        expression: Tree,
        environment: Env,
        k: AndThen,
    },
    Return {
        value: Val,
        k: AndThen,
    },
}

impl Suspension {
    fn run(mut self) -> Interpretation<Val> {
        loop {
            match self {
                Self::Suspend(..) => self = self.resume(),
                Self::Done(value) => break Ok(value),
                Self::Diverged(error) => break Err(error),
            }
        }
    }

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

    fn return_and(value: Val, k: AndThen) -> Self {
        Suspension::Suspend(Suspended::Return { value, k })
    }

    fn eval_and(expr: &Tree, environment: Env, k: AndThen) -> Self {
        Suspension::Suspend(Suspended::Eval {
            expression: Rc::clone(&expr),
            environment: environment.shared(),
            k,
        })
    }
}

fn and_then(value: Val, k: AndThen) -> Suspension {
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
            Val::Closure(closure) => {
                let closure = closure.borrow();
                Suspension::Suspend(Suspended::Eval {
                    expression: Rc::clone(&closure.body),
                    environment: {
                        let env = closure.capture.disjoint();
                        env.push_local(value);
                        env
                    },
                    k: *k,
                })
            }

            Val::RecursiveClosure { name, inner } => match inner.upgrade() {
                Some(closure) => {
                    let closure = closure.borrow();
                    Suspension::Suspend(Suspended::Eval {
                        expression: Rc::clone(&closure.body),
                        environment: {
                            let env = closure.capture.disjoint();
                            env.push_local(value);
                            env
                        },
                        k: *k,
                    })
                }

                None => {
                    Suspension::Diverged(RuntimeError::ExpiredSelfReferential(format!("{name}")))
                }
            },

            Val::PartiallyAppliedBridge {
                bridge,
                mut arguments,
            } => {
                arguments.push(value);

                if arguments.len() < bridge.external.arity() {
                    Suspension::return_and(Val::PartiallyAppliedBridge { bridge, arguments }, *k)
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
            body,
            environment,
            k,
        } => Suspension::Suspend(Suspended::Eval {
            expression: body,
            environment: {
                let env = environment.disjoint();
                env.push_local(value);
                env
            },
            // If I disjoint the env here, then body evaluates in its own
            // environment, which is latter thrown away and I am fine. But I could
            // also pop what is pushed here and continue sharing. But how? and_then
            // would have to be called with the environment and let it be passed
            // around. Let's disjoint first and fix this later.
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
                    environment: environment.shared(),
                    k: AndThen::EvalTupleElement {
                        input,
                        output,
                        environment,
                        k,
                    },
                })
            } else {
                Suspension::return_and(Val::Product(output), *k)
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
                    environment: environment.shared(),
                    k: AndThen::EvalRecordField {
                        input,
                        output,
                        environment,
                        k,
                    },
                })
            } else {
                Suspension::return_and(Val::Product(output), *k)
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
                Suspension::eval_and(
                    &Rc::clone(&input[output.len()]),
                    environment.shared(),
                    AndThen::EvalConstructor {
                        input,
                        output,
                        environment,
                        constructor,
                        k,
                    },
                )
            } else {
                Suspension::return_and(
                    Val::Variant(
                        VariantVal {
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
            (Val::Product(mut elements), ProductElement::Ordinal(ix)) => {
                Suspension::return_and(elements.swap_remove(ix), *k)
            }
            (base, select) => Suspension::Diverged(RuntimeError::BadProjection { base, select }),
        },

        AndThen::EvalDeconstruct {
            clauses,
            environment,
            k,
        } => {
            if let Some((bindings, consequent)) = clauses.iter().find_map(|clause| {
                clause
                    .pattern
                    .deconstruct(&value)
                    .map(|bindings| (bindings, Rc::clone(&clause.consequent)))
            }) {
                let env = environment.disjoint();
                for (_, binding) in bindings {
                    env.push_local(binding);
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
            expression: if let Val::Constant(Literal::Bool(true)) = value {
                Rc::clone(&consequent)
            } else {
                Rc::clone(&alternate)
            },
            environment,
            k: *k,
        }),

        AndThen::EvalInterpolation {
            mut buffer,
            segments,
            index,
            environment,
            k,
        } => {
            use std::fmt::Write as _;

            // value comes from return and eval. If I eval an expr, then its evalutation
            // is that value is, which is different types. So value cannot carry the buffer.

            match &segments[index] {
                Segment::Literal(_, literal) => {
                    let _ = write!(buffer, "{value}{literal}");

                    let index = 1 + index;
                    if index < segments.len() {
                        Suspension::return_and(value, {
                            AndThen::EvalInterpolation {
                                buffer,
                                segments,
                                index,
                                environment,
                                k,
                            }
                        })
                    } else {
                        Suspension::return_and(Val::Constant(Literal::Text(buffer)), *k)
                    }
                }

                Segment::Expression(expr) => Suspension::eval_and(expr, environment.shared(), {
                    let index = 1 + index;
                    if index < segments.len() {
                        AndThen::EvalInterpolation {
                            buffer,
                            segments: Rc::clone(&segments),
                            index,
                            environment,
                            k,
                        }
                    } else {
                        // What happens with the return value of this?
                        *k
                    }
                }),
            }
        }

        AndThen::Hcf => Suspension::Done(value),
    }
}

impl Expr {
    pub fn interpret(self: &Tree, environment: Env) -> Interpretation<Val> {
        self.suspend(environment).run()
    }

    fn suspend(self: &Tree, environment: Env) -> Suspension {
        Suspension::Suspend(Suspended::Eval {
            expression: self.clone(),
            environment,
            k: AndThen::Hcf.into(),
        })
    }

    fn eval(self: Tree, environment: Env, k: AndThen) -> Suspension {
        match self.as_ref() {
            Self::Variable(_, the) => {
                let value = match the {
                    namer::Identifier::Bound(index) => environment.local(*index),
                    namer::Identifier::Free(name) => environment.global(name).cloned(),
                };

                value.map_or_else(
                    || Suspension::Diverged(RuntimeError::NoSuchSymbol(the.clone())),
                    |value| Suspension::Suspend(Suspended::Return { value, k }),
                )
            }

            Self::InvokeBridge(_, bridge) => Suspension::return_and(
                Val::PartiallyAppliedBridge {
                    bridge: bridge.clone().into(),
                    arguments: Vec::with_capacity(1),
                },
                k,
            ),

            Self::Constant(_, the) => Suspension::return_and(Val::Constant(the.clone().into()), k),

            Self::RecursiveLambda(_, the) => {
                let closure = Closure::capture(&environment, &the.lambda.body);
                closure
                    .borrow()
                    .provide_argument(Val::Closure(Rc::clone(&closure)));
                Suspension::return_and(Val::Closure(Rc::clone(&closure)), k)
            }

            Self::Lambda(_, the) => {
                Suspension::return_and(Val::Closure(Closure::capture(&environment, &the.body)), k)
            }

            Self::Apply(_, the) => Suspension::eval_and(
                &the.function,
                environment.shared(),
                AndThen::EvalArgument {
                    argument: Rc::clone(&the.argument),
                    environment,
                    k: k.into(),
                },
            ),

            Self::Let(_, the) => Suspension::eval_and(
                &the.bound,
                environment.shared(),
                AndThen::EvalLetBody {
                    body: the.body.clone(),
                    environment,
                    k: k.into(),
                },
            ),

            Self::Tuple(_, the) => Suspension::eval_and(
                &the.elements[0],
                environment.shared(),
                AndThen::EvalTupleElement {
                    input: Rc::new(the.elements.clone()),
                    output: Vec::with_capacity(the.elements.len()),
                    environment,
                    k: k.into(),
                },
            ),

            Self::Record(_, the) => Suspension::eval_and(
                &the.fields[0].1,
                environment.shared(),
                AndThen::EvalRecordField {
                    input: Rc::new(the.fields.clone()),
                    output: Vec::with_capacity(the.fields.len()),
                    environment,
                    k: k.into(),
                },
            ),

            Self::Inject(_, the) => {
                if the.arguments.is_empty() {
                    Suspension::return_and(
                        Val::Variant(
                            VariantVal {
                                constructor: the.constructor.clone().into(),
                                arguments: Vec::default(),
                            }
                            .into(),
                        ),
                        k,
                    )
                } else {
                    Suspension::eval_and(
                        &the.arguments[0],
                        environment.shared(),
                        AndThen::EvalConstructor {
                            input: Rc::new(the.arguments.clone()),
                            output: Vec::with_capacity(the.arguments.len()),
                            environment,
                            constructor: the.constructor.clone().into(),
                            k: k.into(),
                        },
                    )
                }
            }

            Self::Project(_, the) => Suspension::eval_and(
                &the.base,
                environment,
                AndThen::EvalProjection {
                    select: the.select.clone(),
                    k: k.into(),
                },
            ),

            Self::Sequence(_, the) => Suspension::eval_and(
                &the.this,
                environment.shared(),
                AndThen::Eval {
                    expression: Rc::clone(&the.and_then),
                    environment,
                    k: k.into(),
                },
            ),

            Self::Deconstruct(_, the) => Suspension::eval_and(
                &the.scrutinee,
                environment.shared(),
                AndThen::EvalDeconstruct {
                    clauses: Rc::new(the.match_clauses.clone()),
                    environment,
                    k: k.into(),
                },
            ),

            Self::If(_, the) => Suspension::eval_and(
                &the.predicate,
                environment.shared(),
                AndThen::EvalConditional {
                    consequent: Rc::clone(&the.consequent),
                    alternate: Rc::clone(&the.alternate),
                    environment,
                    k: k.into(),
                },
            ),

            Self::Interpolate(_, ast::Interpolate(segments)) => match segments.first() {
                Some(Segment::Expression(expr)) => Suspension::eval_and(
                    expr,
                    environment.shared(),
                    AndThen::EvalInterpolation {
                        buffer: String::new(),
                        segments: Rc::new(segments.clone()),
                        index: 1,
                        environment,
                        k: k.into(),
                    },
                ),

                Some(Segment::Literal(_, x)) => Suspension::return_and(
                    Val::Constant(Literal::Text("".to_owned())),
                    AndThen::EvalInterpolation {
                        buffer: format!("{x}"),
                        segments: Rc::new(segments.clone()),
                        index: 1,
                        environment,
                        k: k.into(),
                    },
                ),

                None => Suspension::return_and(Val::Constant(Literal::Text("".to_owned())), k),
            },

            Self::Ascription(_, the) => Suspension::eval_and(&the.ascribed_tree, environment, k),
        }
    }
}
