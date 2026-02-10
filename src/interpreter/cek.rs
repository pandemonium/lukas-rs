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
                closure.body.reduce(&closure.capture.shared())
            }

            Val::RecursiveClosure { inner, .. } => {
                let closure = inner.upgrade().ok_or_else(|| {
                    RuntimeError::ExpiredSelfReferential(format!("{symbol_name}"))
                })?;
                let closure = closure.borrow();
                closure.provide_argument(Val::Constant(argument.into()));
                closure.body.reduce(&closure.capture.shared())
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
        binder: Box<namer::Identifier>,
        body: Tree,
        environment: Env,
        k: Box<AndThen>,
    },

    EvalTupleElement {
        input: Vec<Tree>,
        output: Vec<Val>,
        environment: Env,
        k: Box<AndThen>,
    },

    EvalRecordField {
        input: Vec<(parser::Identifier, Tree)>,
        output: Vec<Val>,
        environment: Env,
        k: Box<AndThen>,
    },

    EvalConstructor {
        input: Vec<Tree>,
        output: Vec<Val>,
        environment: Env,
        constructor: namer::QualifiedName,
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
        clauses: Vec<ast::pattern::MatchClause<Erased, namer::Identifier>>,
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
        segments: Vec<Segment<Erased, namer::Identifier>>,
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

    fn eval_and(expr: &Tree, environment: &Env, k: AndThen) -> Self {
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
                closure.provide_argument(value);
                Suspension::Suspend(Suspended::Eval {
                    expression: Rc::clone(&closure.body),
                    // capture already disjoint
                    environment: closure.capture.shared(),
                    k: *k,
                })
            }

            Val::RecursiveClosure { name, inner } => match inner.upgrade() {
                Some(closure) => {
                    let closure = closure.borrow();
                    closure.provide_argument(value);
                    Suspension::Suspend(Suspended::Eval {
                        expression: Rc::clone(&closure.body),
                        // capture already disjoint
                        environment: closure.capture.shared(),
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
            binder,
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
                Suspension::Suspend(Suspended::Eval {
                    expression: Rc::clone(&input[output.len()]),
                    environment: environment.shared(),
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
            if let Some((bindings, consequent)) = clauses.into_iter().find_map(|clause| {
                clause
                    .pattern
                    .deconstruct(&value)
                    .map(|bindings| (bindings, clause.consequent))
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
            segments,
            index,
            environment,
            k,
        } => {
            use std::fmt::Write as _;

            let Val::Constant(Literal::Text(mut buffer)) = value else {
                panic!("{value}");
            };

            match &segments[index] {
                Segment::Literal(_, literal) => {
                    let _ = write!(buffer, "{literal}");
                    Suspension::return_and(Val::Constant(Literal::Text(buffer)), {
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
                    environment: environment.shared(),
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

    fn eval(self: &Tree, environment: Env, k: AndThen) -> Suspension {
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
                // Could I do away with the RefCell since Env uses internal mutation?
                closure.borrow().provide_argument(Val::RecursiveClosure {
                    name: the.own_name.clone().into(),
                    inner: Rc::downgrade(&closure),
                });
                Suspension::return_and(Val::Closure(Rc::clone(&closure)), k)
            }

            Self::Lambda(_, the) => {
                Suspension::return_and(Val::Closure(Closure::capture(&environment, &the.body)), k)
            }

            Self::Apply(_, the) => Suspension::Suspend(Suspended::Eval {
                expression: Rc::clone(&the.function),
                environment: environment.shared(),
                k: AndThen::EvalArgument {
                    argument: Rc::clone(&the.argument),
                    environment,
                    k: k.into(),
                },
            }),

            Self::Let(_, the) => Suspension::Suspend(Suspended::Eval {
                expression: Rc::clone(&the.bound),
                environment: environment.shared(),
                k: AndThen::EvalLetBody {
                    binder: the.binder.clone().into(),
                    body: the.body.clone(),
                    environment,
                    k: k.into(),
                },
            }),

            Self::Tuple(_, the) => Suspension::Suspend(Suspended::Eval {
                expression: Rc::clone(&the.elements[0]),
                environment: environment.shared(),
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
                environment: environment.shared(),
                k: AndThen::EvalRecordField {
                    input: the.fields.clone(),
                    output: Vec::with_capacity(the.fields.len()),
                    environment,
                    k: k.into(),
                },
            }),

            Self::Construct(_, the) => {
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
                    Suspension::Suspend(Suspended::Eval {
                        expression: Rc::clone(&the.arguments[0]),
                        environment: environment.shared(),
                        k: AndThen::EvalConstructor {
                            input: the.arguments.clone(),
                            output: Vec::with_capacity(the.arguments.len()),
                            environment,
                            constructor: the.constructor.clone(),
                            k: k.into(),
                        },
                    })
                }
            }

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
                environment: environment.shared(),
                k: AndThen::Eval {
                    expression: Rc::clone(&the.and_then),
                    environment,
                    k: k.into(),
                },
            }),

            Self::Deconstruct(_, the) => Suspension::Suspend(Suspended::Eval {
                expression: Rc::clone(&the.scrutinee),
                environment: environment.shared(),
                k: AndThen::EvalDeconstruct {
                    clauses: the.match_clauses.clone(),
                    environment,
                    k: k.into(),
                },
            }),

            Self::If(_, the) => Suspension::Suspend(Suspended::Eval {
                expression: Rc::clone(&the.predicate),
                environment: environment.shared(),
                k: AndThen::EvalConditional {
                    consequent: Rc::clone(&the.consequent),
                    alternate: Rc::clone(&the.alternate),
                    environment,
                    k: k.into(),
                },
            }),

            Self::Interpolate(_, the) => Suspension::return_and(
                Val::Constant(Literal::Text("".to_owned())),
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
