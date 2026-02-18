use std::{
    fmt,
    rc::Rc,
    sync::atomic::{AtomicU32, Ordering},
};

use crate::{
    ast::namer::{QualifiedName, Symbol, SymbolName},
    closed::{self, CaptureIndex, CaptureLayout, Expr},
    parser::{self, IdentifierPath},
};

impl closed::SymbolTable {
    pub fn lambda_lift(mut self) -> Program {
        let start = self
            .symbols
            .remove(&SymbolName::Term(QualifiedName::from_root_symbol(
                parser::Identifier::from_str("start"),
            )))
            .unwrap();

        for (name, symbol) in self.symbols {
            if let Symbol::Term(term) = symbol {
                let mut crane = Crane::new(term.name.clone());
                let lifted = crane.lift_lambdas(term.body.unwrap());
            }
        }

        Program {
            functions: todo!(),
            start: todo!(),
        }
    }
}

#[derive(Debug)]
struct Crane {
    target_module: IdentifierPath,
    lifted: Vec<LiftedFunction>,
}

struct LiftedLambda {
    lambdas: Vec<LiftedFunction>,
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

    fn lift_lambdas(&mut self, body: Expr) -> LiftedLambda {
        let mut lifted = Vec::default();
        let body = body.map(&mut |e| match e {
            Expr::Lambda(ci, lambda) => {
                let name = self.fresh_name();

                lifted.push(LiftedFunction {
                    name: name.clone(),
                    code: Rc::unwrap_or_clone(lambda.body),
                    layout: ci.layout.clone().unwrap(),
                    own_name_slot: None,
                });

                Expr::MakeClosure(
                    ci.clone(),
                    ClosureInfo {
                        environment: ci.environment_tuple().into(),
                        lifted_name: name,
                    },
                )
            }

            Expr::RecursiveLambda(..) => todo!(),

            Expr::Variable(_, closed::Identifier::Captured(..)) => todo!(),

            otherwise => otherwise,
        });

        LiftedLambda {
            lambdas: lifted,
            body,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ClosureInfo {
    pub environment: Box<Expr>,
    pub lifted_name: QualifiedName,
}

#[derive(Debug, Clone)]
pub struct Program {
    functions: Vec<LiftedFunction>,
    start: Expr,
}

#[derive(Debug, Clone)]
pub struct LiftedFunction {
    name: QualifiedName,
    code: Expr,
    layout: CaptureLayout,
    own_name_slot: Option<CaptureIndex>,
}

impl fmt::Display for ClosureInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "")
    }
}
