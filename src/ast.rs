use std::{fmt, marker::PhantomData, rc::Rc};

use crate::{
    ast::{self, annotation::Annotated},
    parser::{self, Identifier},
};

pub mod annotation;
pub mod namer;

pub const ROOT_MODULE_NAME: &str = "__root__";

pub struct CompilationUnit<A> {
    pub root: ModuleDeclaration<A>,
}

impl<A> CompilationUnit<A> {
    pub fn from_declarations(decls: Vec<Declaration<A>>) -> Self {
        Self {
            root: ModuleDeclaration {
                name: Identifier::from_str(ROOT_MODULE_NAME),
                declarator: ModuleDeclarator { members: decls },
            },
        }
    }
}

pub enum Declaration<A> {
    Value(A, ValueDeclaration<A>),
    Module(A, ModuleDeclaration<A>),
    Type(A, TypeDeclaration<A>),
}

pub struct ValueDeclaration<A> {
    pub name: parser::Identifier,
    pub declarator: ValueDeclarator<A>,
}

pub struct ValueDeclarator<A> {
    pub type_signature: Option<TypeSignature<A, parser::IdentifierPath>>,
    pub body: ast::Expr<A, parser::IdentifierPath>,
}

pub struct ModuleDeclaration<A> {
    pub name: parser::Identifier,
    pub declarator: ModuleDeclarator<A>,
}

pub struct ModuleDeclarator<A> {
    pub members: Vec<Declaration<A>>,
}

pub struct TypeDeclaration<A> {
    pub name: parser::Identifier,
    pub declarator: TypeDeclarator<A>,
}

pub enum TypeDeclarator<A> {
    Record(A, RecordDeclarator<A>),
}

pub struct RecordDeclarator<A> {
    pub fields: Vec<FieldDeclarator<A>>,
}

pub struct FieldDeclarator<A> {
    pub name: parser::Identifier,
    pub type_signature: TypeExpression<A, parser::IdentifierPath>,
}

#[derive(Debug, Clone)]
pub struct TypeSignature<A, TypeId> {
    pub universal_quantifiers: Vec<parser::Identifier>,
    pub body: TypeExpression<A, TypeId>,
    pub phase: PhantomData<A>,
}

impl<A, TypeId1> TypeSignature<A, TypeId1> {
    pub fn map<F, B, TypeId2>(self, f: F) -> TypeSignature<B, TypeId2>
    where
        F: FnOnce(TypeExpression<A, TypeId1>) -> TypeExpression<B, TypeId2>,
    {
        TypeSignature {
            universal_quantifiers: self.universal_quantifiers,
            body: f(self.body),
            phase: PhantomData,
        }
    }
}

#[derive(Debug, Clone)]
pub enum TypeExpression<A, TypeId> {
    Constructor(A, TypeId),
    Parameter(A, Identifier),
    Apply(A, TypeApply<A, TypeId>),
    Arrow(A, TypeArrow<A, TypeId>),
}

#[derive(Debug, Clone)]
pub struct TypeApply<A, TypeId> {
    pub function: Box<TypeExpression<A, TypeId>>,
    pub argument: Box<TypeExpression<A, TypeId>>,
    pub phase: PhantomData<TypeId>,
}

#[derive(Debug, Clone)]
pub struct TypeArrow<A, TypeId> {
    pub domain: Box<TypeExpression<A, TypeId>>,
    pub codomain: Box<TypeExpression<A, TypeId>>,
}

pub type Tree<A, Id> = Rc<Expr<A, Id>>;

#[derive(Debug, Clone)]
pub enum Expr<A, Id> {
    Variable(A, Id),
    Constant(A, Literal),
    RecursiveLambda(A, SelfReferential<A, Id>),
    Lambda(A, Lambda<A, Id>),
    Apply(A, Apply<A, Id>),
    Let(A, Binding<A, Id>),
    Tuple(A, Tuple<A, Id>),
    Record(A, Record<A, Id>),
    Project(A, Projection<A, Id>),
    Sequence(A, Sequence<A, Id>),
}

impl<A, Id> Expr<A, Id> {
    pub fn annotation(&self) -> &A {
        match self {
            Expr::Variable(a, ..)
            | Expr::Constant(a, ..)
            | Expr::RecursiveLambda(a, ..)
            | Expr::Lambda(a, ..)
            | Expr::Apply(a, ..)
            | Expr::Let(a, ..)
            | Expr::Record(a, ..)
            | Expr::Tuple(a, ..)
            | Expr::Project(a, ..)
            | Expr::Sequence(a, ..) => a,
        }
    }

    pub fn erase_annotation(&self) -> Expr<(), Id>
    where
        Self: Annotated<A, (), Id, Output = Expr<(), Id>>,
    {
        self.map_annotation(|_| ())
    }
}

#[derive(Debug, Clone)]
pub struct Record<A, Id> {
    pub fields: Vec<(parser::Identifier, Tree<A, Id>)>,
}

#[derive(Debug, Clone)]
pub struct Tuple<A, Id> {
    pub elements: Vec<Tree<A, Id>>,
}

#[derive(Debug, Clone)]
pub enum Literal {
    Int(i64),
    Text(String),
}

#[derive(Debug, Clone)]
pub struct Binding<A, Id> {
    pub binder: Id,
    pub bound: Tree<A, Id>,
    pub body: Tree<A, Id>,
}

#[derive(Debug, Clone)]
pub struct SelfReferential<A, Id> {
    pub own_name: Id,
    pub lambda: Lambda<A, Id>,
}

impl<A, Id> SelfReferential<A, Id> {
    pub fn annotation(&self) -> &A {
        self.lambda.annotation()
    }
}

#[derive(Debug, Clone)]
pub struct Lambda<A, Id> {
    pub parameter: Id,
    pub body: Tree<A, Id>,
}

impl<A, Id> Lambda<A, Id> {
    pub fn annotation(&self) -> &A {
        self.body.annotation()
    }
}

#[derive(Debug, Clone)]
pub struct Apply<A, Id> {
    pub function: Tree<A, Id>,
    pub argument: Tree<A, Id>,
}

#[derive(Debug, Clone)]
pub struct Projection<A, Id> {
    pub base: Tree<A, Id>,
    pub select: ProductElement,
}

#[derive(Debug, Clone)]
pub enum ProductElement {
    Ordinal(usize),
    Name(parser::Identifier),
}

#[derive(Debug, Clone)]
pub struct Sequence<A, Id> {
    pub this: Tree<A, Id>,
    pub and_then: Tree<A, Id>,
}

impl<A, Id> fmt::Display for Expr<A, Id>
where
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Variable(_, x) => write!(f, "{x}"),
            Self::Constant(_, x) => write!(f, "{x}"),
            Self::RecursiveLambda(_, x) => write!(f, "{} := {}", x.own_name, x.lambda),
            Self::Lambda(_, x) => write!(f, "{}", x),
            Self::Apply(_, x) => write!(f, "({} {})", x.function, x.argument),
            Self::Let(_, x) => write!(f, "let {} = {} in {}", x.binder, x.bound, x.body),
            Self::Record(_, x) => write!(f, "{x}"),
            Self::Tuple(_, x) => write!(f, "{x}"),
            Self::Project(_, x) => write!(f, "{}.{}", x.base, x.select),
            Self::Sequence(_, x) => write!(f, "{}; {}", x.this, x.and_then),
        }
    }
}

impl fmt::Display for ProductElement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ordinal(id) => write!(f, "&{id}"),
            Self::Name(id) => write!(f, "\"{id}\""),
        }
    }
}

impl<A, Id> fmt::Display for Lambda<A, Id>
where
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { parameter, body } = self;
        write!(f, "λ{parameter}. {body}")
    }
}

impl<A, Id> fmt::Display for Record<A, Id>
where
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let record_rendering = self
            .fields
            .iter()
            .map(|(label, e)| format!("{label}: {e}"))
            .collect::<Vec<_>>()
            .join("; ");
        write!(f, "{{ {record_rendering} }}")
    }
}

impl<A, Id> fmt::Display for Tuple<A, Id>
where
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let tuple_rendering = self
            .elements
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "({tuple_rendering})")
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(x) => write!(f, "{x}"),
            Self::Text(x) => write!(f, "{x}"),
        }
    }
}
