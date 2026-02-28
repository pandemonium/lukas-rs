use std::{
    fmt,
    rc::Rc,
    sync::atomic::{AtomicU32, Ordering},
};

use crate::{
    ast::{
        Apply, Literal, ProductElement, Projection,
        namer::{QualifiedName, Symbol, SymbolName},
    },
    closed::{self, CaptureInfo, Closed, Expr, Identifier, LexicalLevel},
    parser::{self, IdentifierPath},
    phase,
};

impl closed::SymbolTable {
    pub fn lambda_lift(self) -> Program {
        let mut functions = Vec::default();

        for (name, symbol) in self.symbols {
            let SymbolName::Term(name) = name else {
                panic!("All terms have term names")
            };

            if let Symbol::Term(term) = symbol {
                let mut crane = Crane::new(term.name.clone());
                let capture_info = term.body().annotation().clone();
                let lifted = crane.lift_lambdas(term.body.unwrap());
                functions.extend(lifted.functions);
                functions.push(LiftedFunction {
                    name,
                    code: lifted.body,
                    capture_info,
                });
            }
        }

        Program {
            functions,
            start: Expr::Apply(
                CaptureInfo::dummy(),
                Apply {
                    function: Expr::Variable(
                        CaptureInfo::dummy(),
                        Identifier::Global(
                            QualifiedName::from_root_symbol(parser::Identifier::from_str("start"))
                                .into(),
                        ),
                    )
                    .into(),
                    argument: Expr::Constant(CaptureInfo::dummy(), Literal::Unit).into(),
                },
            ),
        }
    }
}

#[derive(Debug)]
struct Crane {
    target_module: IdentifierPath,
    lifted: Vec<LiftedFunction>,
}

struct Lifting {
    functions: Vec<LiftedFunction>,
    body: Expr,
}

static FRESH_LAMBDA_ID: AtomicU32 = AtomicU32::new(0);

impl Crane {
    fn new(name: QualifiedName) -> Self {
        Self {
            target_module: name.module().clone(),
            lifted: Vec::default(),
        }
    }

    fn fresh_name(&self) -> QualifiedName {
        QualifiedName::new(
            self.target_module.clone(),
            &format!("lambda_{}", FRESH_LAMBDA_ID.fetch_add(1, Ordering::Relaxed)),
        )
    }

    fn lift_lambdas(&mut self, body: Expr) -> Lifting {
        let mut functions = Vec::default();
        let body = body.map(&mut |e| match e {
            Expr::Lambda(capture_info, lambda) => {
                let name = self.fresh_name();

                println!(
                    "lift_lambdas: {name} has type {}",
                    capture_info.type_info.inferred_type
                );

                functions.push(LiftedFunction::from_lambda(
                    capture_info.clone(),
                    name.clone(),
                    lambda,
                ));

                Expr::MakeClosure(
                    capture_info.clone(),
                    ClosureInfo {
                        environment: capture_info.make_environment_tuple().into(),
                        lifted_name: name,
                        is_recursive: false,
                    },
                )
            }

            Expr::RecursiveLambda(capture_info, mut self_ref) => {
                let lambda_name = self.fresh_name();

                println!(
                    "lift_lambdas: rec {lambda_name} has type {}",
                    capture_info.type_info.inferred_type
                );

                // transform the local own_name into a global
                self_ref.lambda.body = Rc::unwrap_or_clone(self_ref.lambda.body)
                    .map(&mut |e| match e {
                        Expr::Variable(ci, Identifier::Local(LexicalLevel(0))) => {
                            Expr::Variable(ci, Identifier::Global(lambda_name.clone().into()))
                        }

                        otherwise => otherwise,
                    })
                    .into();

                functions.push(LiftedFunction::from_lambda(
                    capture_info.clone(),
                    lambda_name.clone(),
                    self_ref.lambda,
                ));

                Expr::MakeClosure(
                    capture_info.clone(),
                    ClosureInfo {
                        environment: capture_info.make_environment_tuple().into(),
                        lifted_name: lambda_name,
                        is_recursive: true,
                    },
                )
            }

            Expr::Variable(capture_info, closed::Identifier::Captured(capture)) => Expr::Project(
                capture_info.clone(),
                Projection {
                    base: Expr::Variable(capture_info, closed::Identifier::Local(LexicalLevel(0)))
                        .into(),
                    select: ProductElement::Ordinal(capture.index()),
                },
            ),

            otherwise => otherwise,
        });

        Lifting { functions, body }
    }
}

#[derive(Debug, Clone)]
pub struct ClosureInfo {
    pub environment: Box<Expr>,
    pub lifted_name: QualifiedName,
    pub is_recursive: bool,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub functions: Vec<LiftedFunction>,
    pub start: Expr,
}

#[derive(Debug, Clone)]
pub struct LiftedFunction {
    pub name: QualifiedName,
    pub code: Expr,
    pub capture_info: CaptureInfo,
}

impl LiftedFunction {
    fn from_lambda(
        capture_info: CaptureInfo,
        name: QualifiedName,
        lambda: phase::Lambda<Closed>,
    ) -> Self {
        Self {
            name,
            code: Rc::unwrap_or_clone(lambda.body),
            capture_info,
        }
    }
}

impl fmt::Display for ClosureInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            environment,
            lifted_name,
            is_recursive,
        } = self;
        write!(
            f,
            "ClosureInfo: {} {lifted_name} [{}] ",
            *environment,
            if *is_recursive { "rec" } else { "" }
        )
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { functions, start } = self;

        for function in functions {
            writeln!(f, "{function}")?;
        }

        writeln!(f, "start: {start}")
    }
}

impl fmt::Display for LiftedFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            name,
            code,
            capture_info,
        } = self;
        let ty = &capture_info.type_info.inferred_type;
        write!(f, "lifted => {name}::{ty} --- {code}")
    }
}
