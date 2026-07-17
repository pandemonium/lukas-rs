use std::{
    fmt,
    rc::Rc,
    sync::atomic::{AtomicU32, Ordering},
};

use crate::{
    ast::{
        Apply, Literal,
        namer::{QualifiedName, Symbol, SymbolName},
    },
    closed::{self, CaptureInfo, Closed, Expr, Identifier},
    parser::{self, IdentifierPath},
    phase,
    typer::TypeInfo,
};

impl closed::SymbolTable {
    // `order` is the dependency-resolvable order of the symbols (computed on the
    // pre-closure table, where the dependency matrix lives). Globals are emitted
    // in it so that a top-level definition whose value is *eagerly* evaluated
    // (e.g. `reverse := fold_left (flip Cons) Nil`) is initialised only after the
    // globals it reads -- the same static-init order the interpreter uses.
    pub fn lambda_lift(mut self, order: &[SymbolName]) -> Program {
        // Two distinct outputs: `functions` are the hoisted anonymous lambdas
        // (code taking env + parameter), while `globals` are the top-level
        // definitions themselves (each a value expression -- typically a
        // `MakeClosure` -- evaluated once). Codegen emits the former as C
        // functions and the latter as initialized C globals; the distinction is
        // erased if both share one list, so keep them apart.
        let mut functions = Vec::default();
        let mut globals = Vec::default();

        // `in_resolvable_order` (whence `order` comes) lists every symbol, so we
        // just walk it and pull each out -- the same idiom the interpreter and
        // the Chez backend use. Names in `order` with no term symbol here
        // (constraint methods, foreign terms) simply aren't found.
        for name in order {
            let Some(Symbol::Term(term)) = self.symbols.remove(name) else {
                continue;
            };
            let SymbolName::Term(name) = name.clone() else {
                continue;
            };
            let mut crane = Crane::new(term.name.clone());
            let type_info = term.body.annotation().type_info.clone();
            let lifted = crane.lift_lambdas(term.body);
            functions.extend(lifted.functions);
            globals.push(TopLevelBinding {
                name,
                value: lifted.body,
                type_info,
            });
        }

        // Foreign terms have no body to lift, so they never enter `globals`
        // above (their symbol isn't a `Term` with an expression). Carry their
        // names through so codegen can declare, initialise, and root the C
        // globals that the companion `<Module>.c` file defines.
        let foreign = self
            .foreign_terms
            .iter()
            .map(|ext| ext.name.clone())
            .collect();

        Program {
            functions,
            globals,
            foreign,
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

                tracing::trace!(
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

            Expr::RecursiveLambda(capture_info, self_ref) => {
                let lambda_name = self.fresh_name();

                tracing::trace!(
                    "lift_lambdas: rec {lambda_name} has type {}",
                    capture_info.type_info.inferred_type
                );

                // Self-references stay `Identifier::SelfRef` in the body; codegen
                // resolves them against this lifted function (recursive call, or a
                // reconstructed closure over the env parameter). Free variables are
                // already explicit as `Captured`, so the body needs no rewriting --
                // lifting is now pure hoisting.
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
    /// Hoisted anonymous lambdas -- each is code taking an environment and a
    /// parameter, emitted as a C function.
    pub functions: Vec<LiftedFunction>,
    /// Top-level definitions -- each a value expression evaluated once, emitted
    /// as an initialized C global.
    pub globals: Vec<TopLevelBinding>,
    /// Foreign functions: names only, no body. Their curried closures are built
    /// by a companion `<Module>.c` (via the `FOREIGN_DECL` macro); codegen emits
    /// the matching `extern` global, its `startup` initialiser, and its GC root.
    pub foreign: Vec<QualifiedName>,
    pub start: Expr,
}

/// A top-level definition (`name := value`). For a function definition `value`
/// is a `MakeClosure` over one of the lifted `functions`; for a data definition
/// it is a constant or other value expression.
#[derive(Debug, Clone)]
pub struct TopLevelBinding {
    pub name: QualifiedName,
    pub value: Expr,
    pub type_info: TypeInfo,
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
        let Self {
            functions,
            globals,
            foreign,
            start,
        } = self;

        for function in functions {
            writeln!(f, "{function}")?;
        }

        for global in globals {
            writeln!(f, "{global}")?;
        }

        for name in foreign {
            writeln!(f, "foreign {name}")?;
        }

        writeln!(f, "start: {start}")
    }
}

impl fmt::Display for TopLevelBinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            name,
            value,
            type_info,
        } = self;
        write!(f, "global {name}::{} = {value}", type_info.inferred_type)
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
