use std::{fmt, marker::PhantomData, rc::Rc};

use crate::{
    ast::{
        self, ArrowTypeExpr,
        namer::{self, QualifiedName, TermSymbol},
    },
    interpreter::{Interpretation, Literal, RuntimeError, Value},
    parser::{self, ParseInfo, TypeSignature},
    typer::{BaseType, Type},
};

#[derive(Clone)]
pub struct Bridge {
    pub external: Rc<dyn External + 'static>,
    pub return_type: Type,
    pub qualified_name: QualifiedName,
}

#[derive(Debug)]
pub struct Lambda1<A, R> {
    pub name: &'static str,
    pub apply: fn(A) -> R,
}

#[derive(Debug)]
pub struct Lambda2<A, B, R> {
    pub name: &'static str,
    pub apply: fn(A, B) -> R,
}

#[derive(Debug)]
pub struct RawLambda1<R> {
    pub name: &'static str,
    pub apply: fn(Value) -> R,
}

#[derive(Debug)]
pub struct PartialRawLambda2<F> {
    pub name: &'static str,
    pub apply: F,
    pub signature: TypeSignature,
}

impl Bridge {
    pub fn for_external<E>(external: E, module: &parser::IdentifierPath) -> Self
    where
        E: External + 'static,
    {
        let return_type = external.return_type();
        let qualified_name = QualifiedName::new(module.clone(), external.name());
        Bridge {
            external: Rc::new(external),
            return_type,
            qualified_name,
        }
    }

    pub fn qualified_name(&self) -> &namer::QualifiedName {
        &self.qualified_name
    }
}

pub trait External {
    fn name(&self) -> &'static str;

    fn arity(&self) -> usize;

    fn invoke(&self, arguments: &[Value]) -> Interpretation;

    fn type_signature(&self) -> ast::TypeSignature<ParseInfo, parser::IdentifierPath>;

    fn return_type(&self) -> Type;

    fn into_curried_lambda_tree(self, module: &parser::IdentifierPath) -> parser::Expr
    where
        Self: Sized + 'static,
    {
        (0..self.arity()).rfold(
            parser::Expr::InvokeBridge(ParseInfo::default(), Bridge::for_external(self, module)),
            |body, index| {
                parser::Expr::Lambda(
                    ParseInfo::default(),
                    parser::Lambda {
                        parameter: parser::IdentifierPath::new(&format!("p{index}")),
                        body: body.into(),
                    },
                )
            },
        )
    }

    fn into_symbol(
        self,
        module: &parser::IdentifierPath,
    ) -> TermSymbol<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>
    where
        Self: Sized + 'static,
    {
        TermSymbol {
            name: QualifiedName::new(module.clone(), self.name()),
            type_signature: Some(self.type_signature()),
            body: self.into_curried_lambda_tree(module).into(),
        }
    }
}

trait TypeBridge {
    const TYPE: Type;

    fn synthesize_type() -> Type {
        Self::TYPE
    }
}

impl TypeBridge for String {
    const TYPE: Type = Type::Base(BaseType::Text);
}

impl TypeBridge for () {
    const TYPE: Type = Type::Base(BaseType::Unit);
}

impl TypeBridge for i64 {
    const TYPE: Type = Type::Base(BaseType::Int);
}

//impl TypeBridge for f64 {
//    const TYPE: Type = Type::Base(BaseType::Float);
//}

impl TypeBridge for bool {
    const TYPE: Type = Type::Base(BaseType::Bool);
}

#[macro_export]
macro_rules! lambda1 {
    ($f:ident) => {
        Lambda1 {
            name: stringify!($f),
            apply: $f,
        }
    };
}

#[macro_export]
macro_rules! lambda2 {
    ($f:ident) => {
        Lambda2 {
            name: stringify!($f),
            apply: $f,
        }
    };
}

#[macro_export]
macro_rules! rawlambda1 {
    ($f:ident) => {
        RawLambda1 {
            name: stringify!($f),
            apply: $f,
        }
    };
}

impl<A, R> External for Lambda1<A, R>
where
    A: TypeBridge + TryFrom<Value, Error = RuntimeError>,
    R: TypeBridge + Into<Value>,
{
    fn name(&self) -> &'static str {
        self.name
    }

    fn arity(&self) -> usize {
        1
    }

    fn invoke(&self, arguments: &[Value]) -> Interpretation {
        let Self { apply, .. } = self;
        Ok(apply(arguments[0].clone().try_into()?).into())
    }

    fn type_signature(&self) -> TypeSignature {
        let body_type = Type::Arrow {
            domain: A::TYPE.into(),
            codomain: R::TYPE.into(),
        };

        TypeSignature {
            universal_quantifiers: vec![],
            body: body_type.reify(&vec![]),
            phase: PhantomData,
        }
    }

    fn return_type(&self) -> Type {
        R::TYPE
    }
}

impl<A, B, R> External for Lambda2<A, B, R>
where
    A: TypeBridge + TryFrom<Value, Error = RuntimeError>,
    B: TypeBridge + TryFrom<Value, Error = RuntimeError>,
    R: TypeBridge + Into<Value>,
{
    fn name(&self) -> &'static str {
        self.name
    }

    fn arity(&self) -> usize {
        2
    }

    fn invoke(&self, arguments: &[Value]) -> Interpretation {
        let Self { apply, .. } = self;
        Ok(apply(
            arguments[0].clone().try_into()?,
            arguments[1].clone().try_into()?,
        )
        .into())
    }

    fn type_signature(&self) -> TypeSignature {
        let body_type = Type::Arrow {
            domain: A::TYPE.into(),
            codomain: Type::Arrow {
                domain: B::TYPE.into(),
                codomain: R::TYPE.into(),
            }
            .into(),
        };

        TypeSignature {
            universal_quantifiers: vec![],
            body: body_type.reify(&vec![]),
            phase: PhantomData,
        }
    }

    fn return_type(&self) -> Type {
        R::TYPE
    }
}

impl<R> External for RawLambda1<R>
where
    R: TypeBridge + Into<Value>,
{
    fn name(&self) -> &'static str {
        self.name
    }

    fn arity(&self) -> usize {
        1
    }

    fn invoke(&self, arguments: &[Value]) -> Interpretation {
        let Self { apply, .. } = self;
        Ok(apply(arguments[0].clone()).into())
    }

    fn type_signature(&self) -> ast::TypeSignature<ParseInfo, parser::IdentifierPath> {
        let pi = ParseInfo::default();
        let a = parser::Identifier::from_str("a");
        ast::TypeSignature {
            universal_quantifiers: vec![a.clone()],
            body: parser::TypeExpression::Arrow(
                pi,
                ArrowTypeExpr {
                    domain: parser::TypeExpression::Parameter(pi, a).into(),
                    codomain: R::TYPE.reify(&vec![]).into(),
                },
            ),
            phase: PhantomData,
        }
    }

    fn return_type(&self) -> Type {
        R::TYPE
    }
}

impl<F> External for PartialRawLambda2<F>
where
    // By reference instead?
    F: Fn(Value, Value) -> Option<Value>,
{
    fn name(&self) -> &'static str {
        self.name
    }

    fn arity(&self) -> usize {
        2
    }

    fn invoke(&self, arguments: &[Value]) -> Interpretation {
        let Self { apply, .. } = self;
        let a = &arguments[0];
        let b = &arguments[1];
        apply(a.clone(), b.clone()).ok_or_else(|| RuntimeError::NotApplicable2 {
            a: a.clone(),
            b: b.clone(),
        })
    }

    fn type_signature(&self) -> ast::TypeSignature<ParseInfo, parser::IdentifierPath> {
        self.signature.clone()
    }

    fn return_type(&self) -> Type {
        // Otherwise, synthesize_type from self.type_signature, which is a pain
        Type::fresh()
    }
}

impl TryFrom<Value> for () {
    type Error = RuntimeError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        if let Value::Constant(Literal::Unit) = value {
            Ok(())
        } else {
            Err(RuntimeError::ExpectedType(Type::Base(BaseType::Unit)))
        }
    }
}

impl From<()> for Value {
    fn from(_value: ()) -> Self {
        Self::Constant(Literal::Unit)
    }
}

impl TryFrom<Value> for String {
    type Error = RuntimeError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        if let Value::Constant(Literal::Text(s)) = value {
            Ok(s)
        } else {
            Err(RuntimeError::ExpectedType(Type::Base(BaseType::Text)))
        }
    }
}

impl From<String> for Value {
    fn from(value: String) -> Self {
        Self::Constant(Literal::Text(value))
    }
}

impl TryFrom<Value> for i64 {
    type Error = RuntimeError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        if let Value::Constant(Literal::Int(s)) = value {
            Ok(s)
        } else {
            Err(RuntimeError::ExpectedType(Type::Base(BaseType::Text)))
        }
    }
}

impl From<i64> for Value {
    fn from(value: i64) -> Self {
        Self::Constant(Literal::Int(value))
    }
}

impl TryFrom<Value> for bool {
    type Error = RuntimeError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        if let Value::Constant(Literal::Bool(s)) = value {
            Ok(s)
        } else {
            Err(RuntimeError::ExpectedType(Type::Base(BaseType::Text)))
        }
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Self::Constant(Literal::Bool(value))
    }
}

impl fmt::Display for Bridge {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { external, .. } = self;
        write!(
            f,
            "Bridge {} :: {}",
            external.name(),
            external.type_signature()
        )
    }
}

impl fmt::Debug for Bridge {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Bridge")
            .field(&self.external.name())
            .field(&self.external.type_signature())
            .finish()
    }
}
