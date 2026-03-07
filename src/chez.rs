use std::{
    fmt,
    rc::Rc,
    result,
    sync::atomic::{AtomicUsize, Ordering},
};

use thiserror::Error;

use crate::{
    ast::{
        self, BUILTIN_MODULE_NAME, Deconstruct, Erased, Lambda, Literal, ProductElement,
        STDLIB_MODULE_NAME,
        namer::{Identifier, QualifiedName, Symbol, TermSymbol},
        pattern::{MatchClause, Pattern},
    },
    codegen::CodeBuffer,
    parser::IdentifierPath,
    phase::{self, ConstructorPattern, Expr, Phase},
    typer::Types,
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
            .filter(|name| self.symbols.contains_key(name))
            .map(|name| {
                println!("emit_scheme_code: {name}");
                &self.symbols[name]
            })
            .collect::<Vec<_>>();

        for declaration in symbols {
            if let Symbol::Term(TermSymbol { name, body, .. }) = declaration {
                writeln!(code, "(define {}", name.into_surface_name())?;
                body.erase_annotation().emit(code)?;
                writeln!(code, ")")?;
            }
        }

        Ok(())
    }
}

impl QualifiedName {
    fn is_builtin(&self) -> bool {
        self.module.head == BUILTIN_MODULE_NAME || self.module.head == STDLIB_MODULE_NAME
    }

    fn into_surface_name(&self) -> String {
        let Self {
            module: IdentifierPath { head, tail },
            member,
        } = self;
        let mut buffer = Vec::with_capacity(2 + tail.len());
        buffer.push(head.clone());
        buffer.extend_from_slice(tail.as_slice());
        buffer.push(member.as_str().to_owned());
        buffer.join("-")
    }

    fn into_scheme_name(&self) -> String {
        if self.is_builtin() {
            map_builtin_name(self).to_owned()
        } else {
            self.into_surface_name()
        }
    }
}

impl Identifier {
    fn emit(&self, code: &mut CodeBuffer) -> Result<()> {
        match self {
            Identifier::Bound(level) => write!(code, "x{}", level)?,
            Identifier::Free(name) => write!(code, "{}", name.into_surface_name())?,
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

impl Phase for Erased {
    type Annotation = Self;
    type TermId = Identifier;
    type TypeId = QualifiedName;
}

enum Uncurry {
    Abstract { param: Binder, body: Box<Self> },
    Eliminate { name: String },
}

impl Uncurry {
    fn of_arity(name: &QualifiedName, arity: usize) -> Self {
        (0..arity).rfold(
            Self::Eliminate {
                name: name.into_scheme_name(),
            },
            |z, _| Self::Abstract {
                param: Binder::fresh(),
                body: z.into(),
            },
        )
    }

    fn emit(self, code: &mut CodeBuffer) -> Result<()> {
        self.emit_inner(Vec::default(), code)
    }

    fn emit_inner(self, mut arguments: Vec<Binder>, code: &mut CodeBuffer) -> Result<()> {
        match self {
            Self::Abstract { param, body } => {
                write!(code, "(lambda ({}) ", param.into_scheme_name())?;

                body.emit_inner(
                    {
                        arguments.push(param);
                        arguments
                    },
                    code,
                )?;
                write!(code, ")")?
            }
            Self::Eliminate { name } => write!(
                code,
                "({name} {})",
                arguments
                    .into_iter()
                    .map(|p| p.into_scheme_name())
                    .collect::<Vec<_>>()
                    .join(" ")
            )?,
        }
        Ok(())
    }
}

fn map_builtin_name(name: &QualifiedName) -> &'static str {
    let QualifiedName { module, member } = name;
    match member.as_str() {
        "print_endline" => "write",
        "show" => "show",
        "=" => "=",
        "-" => "-",
        "+" => "+",
        "*" => "*",
        "/" => "/",
        "%" => "mod",
        "<" => "<",
        ">" => ">",
        "and" => "and",
        "xor" => "logxor",
        "or" => "or",
        ">=" => ">=",
        "<=" => "<=",
        otherwise => panic!("unmapped external {otherwise:?}"),
    }
}

// I need some sort of external function declarator
impl phase::Expr<Erased> {
    fn emit(&self, code: &mut CodeBuffer) -> Result<()> {
        match self {
            ast::Expr::Variable(_, the) => the.emit(code)?,

            ast::Expr::InvokeBridge(_, the) => {
                Uncurry::of_arity(&the.qualified_name, the.external.arity()).emit(code)?
            }

            ast::Expr::Constant(_, the) => the.emit(code)?,

            ast::Expr::RecursiveLambda(_, the) => {
                write!(code, "(letrec ([")?;
                the.own_name.emit(code)?;
                write!(code, " ")?;
                the.lambda.emit(code)?;
                write!(code, "]) ")?;
                the.own_name.emit(code)?;
                write!(code, ")")?;
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

impl Lambda<Erased, Identifier> {
    fn emit(&self, code: &mut CodeBuffer) -> Result<()> {
        write!(code, "(lambda (")?;
        self.parameter.emit(code)?;
        write!(code, ") ")?;
        self.body.emit(code)?;
        write!(code, ")")?;
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
    Literal {
        literal: Literal,
        scrutinee: Staged,
    },

    UnionTag {
        tag: QualifiedName,
        scrutinee: Staged,
    },
}

impl Predicate {
    fn emit(&self, code: &mut CodeBuffer) -> Result<()> {
        match self {
            Self::Literal { literal, scrutinee } => {
                write!(code, "(eq? ")?;
                scrutinee.emit(code)?;
                write!(code, " {})", literal)?
            }

            Self::UnionTag { tag, scrutinee } => {
                write!(code, "(eq? ")?;
                scrutinee.get_product_element(0).emit(code)?;
                write!(code, " '{})", tag.into_scheme_name())?
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
enum Staged {
    Var(Binder),

    GetElement {
        base: Box<Self>,
        index: usize,
    },

    Bind {
        binding: Binding,
        k: Box<Self>,
    },

    Check {
        predicate: Box<Predicate>,
        k: Box<Self>,
    },

    Sequence(Vec<Self>),

    Eval(Expr<Erased>),

    Return(Box<Self>),
}

impl Staged {
    fn bind(self, binding: Binding) -> Self {
        Self::Bind {
            binding,
            k: self.into(),
        }
    }

    fn check(self, predicate: Predicate) -> Self {
        Self::Check {
            predicate: predicate.into(),
            k: self.into(),
        }
    }

    fn get_constructor_arg(&self, index: usize) -> Self {
        Self::GetElement {
            base: self.clone().into(),
            index: 1 + index,
        }
    }

    fn get_product_element(&self, index: usize) -> Self {
        Self::GetElement {
            base: self.clone().into(),
            index,
        }
    }

    fn emit(&self, code: &mut CodeBuffer) -> Result<()> {
        match self {
            Self::Var(binder) => write!(code, "{}", binder.into_scheme_name())?,

            Self::GetElement { base, index } => {
                write!(code, "(vector-ref ")?;
                base.emit(code)?;
                write!(code, " {})", index)?
            }

            Self::Bind { binding, k } => {
                write!(code, "(let ([{} ", binding.binder.into_scheme_name())?;
                binding.bound.emit(code)?;
                write!(code, "]) ")?;
                k.emit(code)?;
                write!(code, ")")?
            }

            Self::Check { predicate, k } => {
                write!(code, "(when ")?;
                predicate.emit(code)?;
                k.emit(code)?;
                write!(code, ")")?
            }

            Self::Sequence(exprs) => {
                write!(code, "(begin")?;
                for expr in exprs {
                    write!(code, " ")?;
                    expr.emit(code)?;
                }
                write!(code, ")")?
            }

            Self::Eval(expr) => expr.emit(code)?,

            Self::Return(expr) => {
                write!(code, "(return ")?;
                expr.emit(code)?;
                write!(code, ")")?
            }
        }
        Ok(())
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

impl ConstructorPattern<Erased> {
    fn constructor(&self) -> &QualifiedName {
        self.constructor.try_as_free().unwrap()
    }
}

impl Pattern<Erased, Identifier> {
    fn stage(&self, scrutinee: Staged, k: Staged) -> Staged {
        match self {
            Self::Coproduct(_, the) => the
                .arguments
                .iter()
                .enumerate()
                .rfold(k, |k, (index, arg)| {
                    let binding = Binding::fresh(scrutinee.get_constructor_arg(index));
                    let binder = Staged::Var(binding.binder.clone());
                    Staged::Bind {
                        binding,
                        k: arg.stage(binder, k).into(),
                    }
                })
                .check(Predicate::UnionTag {
                    scrutinee: scrutinee.clone(),
                    tag: the.constructor().clone(),
                }),

            Self::Tuple(_, the) => the.elements.iter().enumerate().rfold(k, |k, (index, arg)| {
                let binding = Binding::fresh(scrutinee.get_product_element(index));
                let binder = Staged::Var(binding.binder.clone());
                arg.stage(binder, k).bind(binding)
            }),

            Self::Struct(_, the) => {
                the.fields
                    .iter()
                    .enumerate()
                    .rfold(k, |k, (index, (_, arg))| {
                        let binding = Binding::fresh(scrutinee.get_product_element(index));
                        let binder = Staged::Var(binding.binder.clone());
                        arg.stage(binder, k).bind(binding)
                    })
            }

            Self::Literally(_, the) => Staged::Check {
                predicate: Predicate::Literal {
                    literal: the.clone(),
                    scrutinee: scrutinee.into(),
                }
                .into(),
                k: k.into(),
            },

            Self::Bind(_, the) => k.bind(Binding {
                binder: Binder::bonafide(the.clone()),
                bound: scrutinee.into(),
            }),
        }
    }
}

impl MatchClause<Erased, Identifier> {
    fn stage(&self, scrutinee: Staged) -> Staged {
        self.pattern.stage(
            scrutinee,
            Staged::Return(Staged::Eval(Rc::unwrap_or_clone(self.consequent.clone())).into()),
        )
    }
}

impl Deconstruct<Erased, Identifier> {
    fn stage(&self) -> Staged {
        let binding = Binding::fresh(Staged::Eval(Rc::unwrap_or_clone(self.scrutinee.clone())));
        let binder = Staged::Var(binding.binder.clone());
        Staged::Bind {
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

    fn emit(&self, code: &mut CodeBuffer) -> Result<()> {
        write!(code, "(call/cc (lambda (return) ")?;
        self.stage().emit(code)?;
        write!(code, "))")?;

        Ok(())
    }
}
