use fmt::Write;
use std::fmt;

use crate::{
    ast::{Literal, ProductElement},
    closed::{Apply, Binding, Expr, Identifier, IfThenElse, LexicalLevel, Projection, Sequence},
    lambda_lift::{self, ClosureInfo, LiftedFunction},
    typer::{self, BaseType},
};

impl typer::Type {
    fn return_type(&self) -> (Option<&Self>, &Self) {
        match self {
            Self::Arrow { domain, codomain } if codomain.is_arrow() => (Some(domain), codomain),
            otherwise => (None, otherwise),
        }
    }

    fn try_as_arrow(&self) -> Option<(&Self, &Self)> {
        match self {
            Self::Arrow { domain, codomain } => Some((domain, codomain)),
            _otherwise => None,
        }
    }

    fn is_arrow(&self) -> bool {
        matches!(self, Self::Arrow { .. })
    }

    fn c_type_name(&self) -> String {
        match self {
            Self::Base(BaseType::Unit) => "void".to_owned(),
            Self::Base(BaseType::Int) => "int64_t".to_owned(),
            Self::Base(BaseType::Text) => "char *".to_owned(),
            Self::Base(BaseType::Bool) => "bool".to_owned(),
            _otherwise => format!("unknown_t /* {} */", self.to_string()),
        }
    }
}

#[derive(Debug, Default)]
pub struct CodeBuffer(String);

impl fmt::Write for CodeBuffer {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0.push_str(s);
        Ok(())
    }
}

impl fmt::Display for CodeBuffer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self(buffer) = self;
        write!(f, "{buffer}")
    }
}

impl lambda_lift::Program {
    pub fn generate_code(&self, out: &mut CodeBuffer) -> fmt::Result {
        for LiftedFunction {
            name,
            code,
            capture_info,
        } in &self.functions
        {
            let ty = &capture_info.type_info.inferred_type;

            println!("generate_code: {name} :: {ty}");

            match ty.try_as_arrow() {
                Some((param, return_ty)) => {
                    writeln!(
                        out,
                        "{} {} (void *env, {}) \n{{",
                        if return_ty.is_arrow() {
                            "Closure".to_owned()
                        } else {
                            return_ty.c_type_name()
                        },
                        name,
                        param.c_type_name(),
                    )?;

                    self.compile_expr(code, out)?;
                    writeln!(out, "\n}}\n")?;
                }

                _otherwise => todo!(),
            }
        }
        Ok(())
    }

    // What does this output?
    fn compile_expr(&self, expr: &Expr, code: &mut CodeBuffer) -> fmt::Result {
        match expr {
            Expr::Variable(_, the) => write!(code, "{}", self.compile_var(the)),
            Expr::InvokeBridge(_, the) => write!(code, "{}", the.qualified_name),
            Expr::Constant(_, the) => write!(code, "{}", self.compile_constant(the)),
            Expr::RecursiveLambda(_, _the) => panic!("lambdas are lifted"),
            Expr::Lambda(_, _the) => panic!("lambdas are lifted"),
            Expr::Apply(_, the) => self.compile_apply(the, code), // foo(x) or apply(closure, x)
            Expr::Let(_, the) => self.compile_let(the, code),
            Expr::Tuple(_, _the) => todo!(),
            Expr::Record(_, _the) => todo!(),
            Expr::Inject(_, _the) => todo!(),
            Expr::Project(_, the) => self.compile_projection(the, code),
            Expr::Sequence(_, the) => self.compile_sequence(the, code),
            Expr::Deconstruct(_, _the) => todo!(),
            Expr::If(_, the) => self.compile_if(the, code),
            Expr::Interpolate(_, _the) => todo!(),
            Expr::Ascription(_, the) => self.compile_expr(&the.ascribed_tree, code),
            Expr::MakeClosure(_, the) => self.compile_closure(the, code),
        }
    }

    fn compile_projection(&self, the: &Projection, code: &mut CodeBuffer) -> fmt::Result {
        self.compile_expr(&the.base, code)?;
        write!(code, "->")?;
        match &the.select {
            ProductElement::Ordinal(i) => write!(code, "elements[{i}]"),
            ProductElement::Name(id) => write!(code, "{id}"),
        }
    }

    fn compile_apply(&self, the: &Apply, code: &mut CodeBuffer) -> fmt::Result {
        match &*the.function {
            Expr::Variable(_, name) => {
                write!(
                    code,
                    "{}(",
                    match name {
                        Identifier::Local(LexicalLevel(level)) => format!("l{level}"),
                        Identifier::Captured(capture) => format!("c{}", capture.index()),
                        Identifier::Global(name) => name.to_string(),
                    }
                )?;
                self.compile_expr(&the.argument, code)?;
                write!(code, ")")
            }
            _otherwise => {
                write!(code, "apply(")?;
                self.compile_expr(&the.function, code)?;
                write!(code, ", ")?;
                self.compile_expr(&the.argument, code)?;
                write!(code, ")")
            }
        }
    }

    fn compile_closure(&self, _the: &ClosureInfo, code: &mut CodeBuffer) -> fmt::Result {
        writeln!(code, "VClo(???)")
    }

    fn compile_sequence(&self, the: &Sequence, code: &mut CodeBuffer) -> fmt::Result {
        write!(code, "(")?;
        self.compile_expr(&the.this, code)?;
        write!(code, ", ")?;
        self.compile_expr(&the.and_then, code)?;
        write!(code, ")")
    }

    fn compile_if(&self, the: &IfThenElse, code: &mut CodeBuffer) -> fmt::Result {
        write!(code, "if (")?;
        self.compile_expr(&the.predicate, code)?;
        writeln!(code, ") {{\n")?;
        self.compile_expr(&the.consequent, code)?;
        writeln!(code, "\n}} else {{")?;
        self.compile_expr(&the.alternate, code)?;
        writeln!(code, "}}")
    }

    fn compile_var(&self, var: &Identifier) -> String {
        match var {
            Identifier::Local(LexicalLevel(level)) => format!("l{level}"),
            Identifier::Captured(capture) => format!("c{}", capture.index()),
            Identifier::Global(qualified_name) => qualified_name.to_string(), //escape this
        }
    }

    fn compile_constant(&self, the: &Literal) -> String {
        match the {
            Literal::Int(x) => format!("VInt({x})"),
            Literal::Text(x) => format!("VText(\"{x}\")"),
            Literal::Bool(x) => format!("VBool({x})"),
            Literal::Unit => "VUnit()".to_owned(),
        }
    }

    fn compile_let(
        &self,
        Binding {
            binder,
            bound,
            body,
        }: &Binding,
        code: &mut CodeBuffer,
    ) -> fmt::Result {
        let bound_ty = bound.annotation().type_info.inferred_type.c_type_name();
        write!(
            code,
            "{bound_ty} {} = ",
            match binder {
                Identifier::Local(LexicalLevel(level)) => format!("l{level}"),
                Identifier::Captured(..) => todo!(),
                Identifier::Global(..) => todo!(),
            }
        )?;
        self.compile_expr(bound, code)?;
        writeln!(code, ";\n")?;
        self.compile_expr(body, code)?;
        writeln!(code, ";\n")
    }
}
