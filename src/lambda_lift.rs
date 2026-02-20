use std::{
    fmt,
    rc::Rc,
    sync::atomic::{AtomicU32, Ordering},
};

use crate::{
    ast::{
        ProductElement,
        namer::{QualifiedName, Symbol, SymbolName},
    },
    closed::{self, CaptureInfo, CaptureLayout, Expr, Lambda, LexicalLevel, Projection},
    parser::{self, IdentifierPath},
};

impl closed::SymbolTable {
    pub fn lambda_lift(mut self) -> Program {
        let Symbol::Term(start) = self
            .symbols
            .remove(&SymbolName::Term(QualifiedName::from_root_symbol(
                parser::Identifier::from_str("start"),
            )))
            .unwrap()
        else {
            panic!("Expected to be a term")
        };

        let mut functions = Vec::default();

        for (name, symbol) in self.symbols {
            let SymbolName::Term(name) = name else {
                panic!("All terms have term names")
            };

            if let Symbol::Term(term) = symbol {
                let mut crane = Crane::new(term.name.clone());
                let lifted = crane.lift_lambdas(term.body.unwrap());
                functions.extend(lifted.functions);
                functions.push(LiftedFunction {
                    name,
                    code: lifted.body,
                    layout: CaptureLayout::default(),
                });
            }
        }

        Program {
            functions,
            start: start.body.unwrap(),
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
        let mut lifted = Vec::default();
        let body = body.map(&mut |e| match e {
            Expr::Lambda(capture_info, lambda) => {
                let name = self.fresh_name();

                lifted.push(LiftedFunction::from_lambda(
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

            Expr::RecursiveLambda(capture_info, self_ref) => {
                let name = self.fresh_name();

                lifted.push(LiftedFunction::from_lambda(
                    capture_info.clone(),
                    name.clone(),
                    self_ref.lambda,
                ));

                Expr::MakeClosure(
                    capture_info.clone(),
                    ClosureInfo {
                        // how does it inject the self placeholder into this?
                        environment: capture_info.make_environment_tuple().into(),
                        lifted_name: name,
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

        Lifting {
            functions: lifted,
            body,
        }
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
    functions: Vec<LiftedFunction>,
    start: Expr,
}

#[derive(Debug, Clone)]
pub struct LiftedFunction {
    name: QualifiedName,
    code: Expr,
    layout: CaptureLayout,
}

impl LiftedFunction {
    fn from_lambda(ci: CaptureInfo, name: QualifiedName, lambda: Lambda) -> Self {
        Self {
            name,
            code: Rc::unwrap_or_clone(lambda.body),
            layout: ci.layout.clone().unwrap(),
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
            if self.is_recursive { "rec" } else { "" }
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
        let Self { name, code, layout } = self;
        write!(f, "{name} (<<layout-info?>>) {code}")
    }
}
