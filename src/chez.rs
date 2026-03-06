use std::{
    fmt,
    rc::Rc,
    result,
    sync::atomic::{AtomicUsize, Ordering},
};

use thiserror::Error;

use crate::{
    ast::{
        self, Deconstruct, Lambda, Literal, ProductElement,
        namer::{Identifier, QualifiedName, Symbol, TermSymbol},
        pattern::{MatchClause, Pattern},
    },
    codegen::CodeBuffer,
    phase::{self, ConstructorPattern, Expr},
    typer::{TypeInfo, Types},
};
use fmt::Write;

#[derive(Debug, Error)]
pub enum ChezError {
    #[error("Formatting error {0}")]
    FmtError(#[from] fmt::Error),
}

pub type Result<A> = result::Result<A, ChezError>;

impl phase::SymbolTable<Types> {
    pub fn emit_scheme_code(&self, code: &mut CodeBuffer) -> Result<()> {
        let deps = self.dependency_matrix();
        let symbols = deps
            .in_resolvable_order()
            .iter()
            .map(|name| &self.symbols[name])
            .collect::<Vec<_>>();

        for declaration in symbols {
            if let Symbol::Term(TermSymbol { name, body, .. }) = declaration {
                writeln!(code, "(define {}", name.into_scheme_name())?;
                body.emit(code)?;
                writeln!(code, ")")?;
            }
        }

        Ok(())
    }
}

impl QualifiedName {
    fn into_scheme_name(&self) -> String {
        todo!()
    }
}

impl Identifier {
    fn emit(&self, code: &mut CodeBuffer) -> Result<()> {
        match self {
            Identifier::Bound(level) => write!(code, "x{}", level)?,
            Identifier::Free(name) => write!(code, "{}", name.into_scheme_name())?,
        }
        Ok(())
    }

    fn into_scheme_name(&self) -> String {
        match self {
            Identifier::Bound(level) => format!("x{}", level),
            Identifier::Free(name) => format!("{}", name.into_scheme_name()),
        }
    }
}
impl ast::Literal {
    fn emit(&self, code: &mut CodeBuffer) -> Result<()> {
        match self {
            ast::Literal::Int(x) => write!(code, "{x}")?,
            ast::Literal::Text(x) => write!(code, "\"{x}\"")?,
            ast::Literal::Bool(true) => write!(code, "#t")?,
            ast::Literal::Bool(false) => write!(code, "#f")?,
            ast::Literal::Unit => write!(code, "'()")?,
        }
        Ok(())
    }
}

impl phase::Expr<Types> {
    fn emit(&self, code: &mut CodeBuffer) -> Result<()> {
        match self {
            ast::Expr::Variable(_, the) => the.emit(code)?,

            ast::Expr::InvokeBridge(_, _the) => {
                // return the.arity nested lambdas
                todo!()
            }

            ast::Expr::Constant(_, the) => the.emit(code)?,

            ast::Expr::RecursiveLambda(_, the) => {
                write!(code, "(define ")?;
                the.own_name.emit(code)?;
                write!(code, " ")?;
                the.lambda.emit(code)?;
                write!(code, ") ")?;
            }

            ast::Expr::Lambda(_, the) => the.emit(code)?,

            ast::Expr::Apply(_, the) => {
                write!(code, "(")?;
                the.function.emit(code)?;
                write!(code, " ")?;
                the.argument.emit(code)?;
                write!(code, ")")?;
            }

            ast::Expr::Let(_, the) => {
                write!(code, "(letrec ([")?;
                the.binder.emit(code)?;
                write!(code, " ")?;
                the.bound.emit(code)?;
                write!(code, "]) ")?;
                the.body.emit(code)?;
                write!(code, ")")?;
            }

            ast::Expr::Tuple(_, the) => {
                write!(code, "(vector")?;
                for el in &the.elements {
                    write!(code, " ")?;
                    el.emit(code)?;
                }
                write!(code, ")")?
            }

            ast::Expr::Record(_, the) => {
                write!(code, "(vector")?;
                for (_, el) in &the.fields {
                    write!(code, " ")?;
                    el.emit(code)?;
                }
                write!(code, ")")?
            }

            ast::Expr::Inject(_, the) => {
                write!(code, "(vector '{}", the.constructor.into_scheme_name())?;
                for arg in &the.arguments {
                    write!(code, " ")?;
                    arg.emit(code)?;
                }
                writeln!(code, ")")?;
            }

            ast::Expr::Project(_, the) => {
                write!(code, "(vector-ref ")?;
                the.base.emit(code)?;
                write!(code, " ")?;
                let ProductElement::Ordinal(index) = the.select else {
                    panic!("ordinal projections only")
                };
                write!(code, "{index})")?;
            }

            ast::Expr::Sequence(_, the) => {
                write!(code, "(")?;
                the.this.emit(code)?;
                writeln!(code, ")")?;
                write!(code, "(")?;
                the.and_then.emit(code)?;
                writeln!(code, ")")?;
            }

            ast::Expr::Deconstruct(_, the) => the.emit(code)?,

            ast::Expr::If(_, the) => {
                write!(code, "(if ")?;
                the.predicate.emit(code)?;
                write!(code, " ")?;
                the.consequent.emit(code)?;
                write!(code, " ")?;
                the.alternate.emit(code)?;
                writeln!(code, ")")?;
            }

            ast::Expr::Interpolate(_, the) => {
                write!(code, "(apply string-append (list")?;
                for segment in &the.0 {
                    write!(code, " ")?;
                    match segment {
                        ast::Segment::Literal(_, the) => the.emit(code)?,
                        ast::Segment::Expression(expr) => {
                            write!(code, "(show ")?;
                            expr.emit(code)?;
                            write!(code, ")")?;
                        }
                    }
                }
                write!(code, "))")?
            }

            ast::Expr::Ascription(_, the) => the.ascribed_tree.emit(code)?,

            ast::Expr::MakeClosure(..) => panic!("not used"),
        }

        Ok(())
    }
}

impl Lambda<TypeInfo, Identifier> {
    fn emit(&self, code: &mut CodeBuffer) -> Result<()> {
        write!(code, "(lambda (")?;
        self.parameter.emit(code)?;
        write!(code, ") ")?;
        self.body.emit(code)?;
        write!(code, ")")?;
        Ok(())
    }
}

impl Deconstruct<TypeInfo, Identifier> {
    fn emit(&self, code: &mut CodeBuffer) -> Result<()> {
        write!(code, "(let [scrutinee ")?;
        self.scrutinee.emit(code)?;
        writeln!(code, "] ")?;

        write!(code, "(cond")?;

        for clause in &self.match_clauses {}

        writeln!(code, "))")?;
        Ok(())
    }
}

#[derive(Debug, Clone)]
struct Binding {
    binder: Binder,
    bound: Box<Staged>,
}

impl Binding {
    fn fresh(bound: Staged) -> Self {
        let binder = Binder::fresh();
        Self {
            binder,
            bound: bound.into(),
        }
    }
}

#[derive(Debug, Clone)]
enum Predicate {
    CheckLiteral {
        literal: Literal,
        scrutinee: Staged,
    },

    CheckTag {
        tag: QualifiedName,
        scrutinee: Staged,
    },
}

#[derive(Debug, Clone)]
enum Staged {
    Var(Binder),

    GetElement {
        base: Box<Self>,
        index: usize,
    },

    Let {
        binding: Binding,
        k: Box<Self>,
    },

    Check {
        predicate: Box<Predicate>,
        k: Box<Self>,
    },

    Sequence(Vec<Self>),

    Eval(Expr<Types>),
}

impl Staged {
    fn get_constructor_arg(base: Self, index: usize) -> Self {
        Self::GetElement {
            base: base.into(),
            index: 1 + index,
        }
    }

    fn get_product_element(base: Self, index: usize) -> Self {
        Self::GetElement {
            base: base.into(),
            index,
        }
    }
}

static BINDER_NAME: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, Clone)]
enum Binder {
    Temp(usize),
    Bonafide(Identifier),
}

impl Binder {
    fn fresh() -> Self {
        Self::Temp(BINDER_NAME.fetch_add(1, Ordering::Relaxed))
    }

    fn bonafide(id: Identifier) -> Self {
        Self::Bonafide(id)
    }

    fn into_scheme_name(&self) -> String {
        match self {
            Self::Temp(x) => format!("temp-{x}"),
            Self::Bonafide(identifier) => identifier.into_scheme_name(),
        }
    }
}

impl ConstructorPattern<Types> {
    fn constructor(&self) -> &QualifiedName {
        self.constructor.try_as_free().unwrap()
    }
}

impl Pattern<TypeInfo, Identifier> {
    fn stage(&self, scrutinee: Staged, k: Staged) -> Staged {
        match self {
            Self::Coproduct(_, the) => Staged::Check {
                predicate: Predicate::CheckTag {
                    scrutinee: scrutinee.clone(),
                    tag: the.constructor().clone(),
                }
                .into(),
                k: the
                    .arguments
                    .iter()
                    .enumerate()
                    .fold(k, |k, (index, arg)| {
                        let binding = Binding::fresh(Staged::get_constructor_arg(
                            (&scrutinee).clone(),
                            index,
                        ));
                        let binder = Staged::Var(binding.binder.clone());
                        Staged::Let {
                            binding,
                            k: arg.stage(binder, k).into(),
                        }
                    })
                    .into(),
            },

            Self::Tuple(_, the) => the.elements.iter().enumerate().fold(k, |k, (index, arg)| {
                let binding = Binding::fresh(Staged::get_product_element(scrutinee.clone(), index));
                let binder = Staged::Var(binding.binder.clone());
                Staged::Let {
                    binding,
                    k: arg.stage(binder, k).into(),
                }
            }),

            Self::Struct(_, the) => {
                the.fields
                    .iter()
                    .enumerate()
                    .fold(k, |k, (index, (_, arg))| {
                        let binding =
                            Binding::fresh(Staged::get_product_element(scrutinee.clone(), index));
                        let binder = Staged::Var(binding.binder.clone());
                        Staged::Let {
                            binding,
                            k: arg.stage(binder, k).into(),
                        }
                    })
            }

            Self::Literally(_, the) => Staged::Check {
                predicate: Predicate::CheckLiteral {
                    literal: the.clone(),
                    scrutinee: scrutinee.into(),
                }
                .into(),
                k: k.into(),
            },

            Self::Bind(_, the) => Staged::Let {
                binding: Binding {
                    binder: Binder::bonafide(the.clone()),
                    bound: scrutinee.into(),
                },
                k: k.into(),
            },
        }
    }
}

impl MatchClause<TypeInfo, Identifier> {
    fn stage(&self, scrutinee: Staged) -> Staged {
        self.pattern.stage(
            scrutinee,
            Staged::Eval(Rc::unwrap_or_clone(self.consequent.clone())),
        )
    }
}

impl Deconstruct<TypeInfo, Identifier> {
    fn stage(&self) -> Staged {
        let binding = Binding::fresh(Staged::Eval(Rc::unwrap_or_clone(self.scrutinee.clone())));
        let binder = Staged::Var(binding.binder.clone());
        Staged::Let {
            binding,
            k: Staged::Sequence(
                self.match_clauses
                    .iter()
                    .map(|clause| clause.stage(binder.clone()))
                    .collect(),
            )
            .into(),
        }
    }
}
