use std::{fmt, rc::Rc};

use crate::{
    ast::namer::{self, QualifiedName, TermSymbol},
    interpreter::{Interpretation, Literal, RuntimeError, Value},
    parser::{self, ParseInfo},
    typer::{BaseType, Type, TypeParameter, TypeScheme},
};

#[derive(Clone)]
pub struct Bridge {
    pub external: Rc<dyn External + 'static>,
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
    pub type_scheme: TypeScheme,
}

impl Bridge {
    pub fn for_external<E>(external: E, module: &parser::IdentifierPath) -> Self
    where
        E: External + 'static,
    {
        let qualified_name = QualifiedName::new(module.clone(), external.name());
        Bridge {
            external: Rc::new(external),
            qualified_name,
        }
    }

    pub fn qualified_name(&self) -> &namer::QualifiedName {
        &self.qualified_name
    }

    pub fn type_scheme(&self) -> TypeScheme {
        self.external.type_scheme()
    }
}

pub trait External {
    fn name(&self) -> &'static str;

    fn arity(&self) -> usize;

    fn invoke(&self, arguments: &[Value]) -> Interpretation;

    fn type_scheme(&self) -> TypeScheme;

    fn into_symbol(
        self,
        module: &parser::IdentifierPath,
    ) -> TermSymbol<ParseInfo, parser::IdentifierPath, parser::IdentifierPath>
    where
        Self: Sized + 'static,
    {
        TermSymbol {
            name: QualifiedName::new(module.clone(), self.name()),
            type_signature: None, // Some(self.type_signature()), (reify the type_scheme!)
            body: parser::Expr::InvokeBridge(
                ParseInfo::default(),
                Bridge::for_external(self, module),
            )
            .into(),
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

    fn type_scheme(&self) -> TypeScheme {
        TypeScheme::from_constant(Type::Arrow {
            domain: A::TYPE.into(),
            codomain: R::TYPE.into(),
        })
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

    fn type_scheme(&self) -> TypeScheme {
        TypeScheme::from_constant(Type::Arrow {
            domain: A::TYPE.into(),
            codomain: Type::Arrow {
                domain: B::TYPE.into(),
                codomain: R::TYPE.into(),
            }
            .into(),
        })
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

    fn type_scheme(&self) -> TypeScheme {
        let tp = TypeParameter::fresh();
        TypeScheme {
            quantifiers: vec![tp],
            underlying: Type::Arrow {
                domain: Type::Variable(tp).into(),
                codomain: R::TYPE.into(),
            },
        }
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

    fn type_scheme(&self) -> TypeScheme {
        self.type_scheme.clone()
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
            external.type_scheme()
        )
    }
}

impl fmt::Debug for Bridge {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Bridge")
            .field(&self.external.name())
            .field(&self.external.type_scheme())
            .finish()
    }
}
