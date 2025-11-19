use std::{fmt, rc::Rc};

use crate::{
    ast::{self, annotation::Annotated},
    parser,
};

pub mod annotation;
pub mod namer;

pub struct CompilationUnit<A> {
    pub root: ModuleDeclaration<A>,
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
    pub type_signature: Option<TypeSignature>,
    pub body: ast::Expr<A, parser::Identifier>,
}

pub struct ModuleDeclaration<A> {
    pub name: parser::Identifier,
    pub declarator: ModuleDeclarator<A>,
}

pub struct ModuleDeclarator<A> {
    pub contents: Vec<Declaration<A>>,
}

pub struct TypeDeclaration<A> {
    pub name: parser::Identifier,
    pub declarator: TypeDeclarator<A>,
}

pub enum TypeDeclarator<A> {
    Record(A, RecordDeclarator),
}

pub struct RecordDeclarator {
    pub fields: Vec<FieldDeclarator>,
}

pub struct FieldDeclarator {
    pub name: parser::Identifier,
    pub type_signature: TypeSignature,
}

#[derive(Debug, Clone)]
pub enum TypeSignature {}

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
    Project(A, Projection<A, Id>),
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
            | Expr::Tuple(a, ..)
            | Expr::Project(a, ..) => a,
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
pub struct Tuple<A, Id> {
    pub elements: Vec<Tree<A, Id>>,
}

#[derive(Debug, Clone)]
pub enum Literal {
    Int(i32),
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
    pub underlying: Lambda<A, Id>,
}

impl<A, Id> SelfReferential<A, Id> {
    pub fn annotation(&self) -> &A {
        self.underlying.annotation()
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

impl<A, Id> fmt::Display for Expr<A, Id>
where
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Variable(_, x) => write!(f, "{x}"),
            Self::Constant(_, x) => write!(f, "{x}"),
            Self::RecursiveLambda(_, x) => write!(f, "{} := {}", x.own_name, x.underlying),
            Self::Lambda(_, x) => write!(f, "{}", x),
            Self::Apply(_, x) => write!(f, "({} {})", x.function, x.argument),
            Self::Let(_, x) => write!(f, "let {} = {} in {}", x.binder, x.bound, x.body),
            Self::Tuple(_, x) => write!(f, "{x}"),
            Self::Project(_, x) => write!(f, "{}.{}", x.base, x.select),
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
