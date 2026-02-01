use std::{fmt, marker::PhantomData, rc::Rc};

use crate::{
    ast::{self, annotation::Annotated, namer::QualifiedName},
    bridge::Bridge,
    compiler, parser,
};

pub mod annotation;
pub mod namer;
pub mod pattern;

pub const ROOT_MODULE_NAME: &str = "Root"; // This should be the main source file name
pub const BUILTIN_MODULE_NAME: &str = "__builtin__";
pub const STDLIB_MODULE_NAME: &str = "stdlib";

#[derive(Debug)]
pub struct CompilationUnit<A> {
    pub root_module: ModuleDeclaration<A>,
    pub compiler: compiler::Compiler,
}

#[derive(Debug)]
pub enum Declaration<A> {
    Value(A, ValueDeclaration<A>),
    Module(A, ModuleDeclaration<A>),
    Type(A, TypeDeclaration<A>),
    Use(A, UseDeclaration<A>),
}

#[derive(Debug)]
pub struct UseDeclaration<A> {
    pub qualified_binder: Option<parser::Identifier>,
    pub module: ModuleDeclaration<A>,
}

#[derive(Debug)]
pub struct ValueDeclaration<A> {
    pub name: parser::Identifier,
    pub declarator: ValueDeclarator<A>,
}

#[derive(Debug)]
pub struct ValueDeclarator<A> {
    pub type_signature: Option<TypeSignature<A, parser::IdentifierPath>>,
    pub body: ast::Expr<A, parser::IdentifierPath>,
}

#[derive(Debug)]
pub struct ModuleDeclaration<A> {
    pub name: parser::Identifier,
    pub declarator: ModuleDeclarator<A>,
}

#[derive(Debug)]
pub enum ModuleDeclarator<A> {
    Inline(Vec<Declaration<A>>),
    External(parser::Identifier),
}

#[derive(Debug)]
pub struct TypeDeclaration<A> {
    pub name: parser::Identifier,
    pub type_parameters: Vec<parser::Identifier>,
    pub declarator: TypeDeclarator<A>,
}

#[derive(Debug)]
pub enum TypeDeclarator<A> {
    Record(A, RecordDeclarator<A>),
    Coproduct(A, CoproductDeclarator<A>),
}

#[derive(Debug)]
pub struct RecordDeclarator<A> {
    pub fields: Vec<FieldDeclarator<A>>,
}

#[derive(Debug)]
pub struct CoproductDeclarator<A> {
    pub constructors: Vec<CoproductConstructor<A>>,
}

#[derive(Debug)]
pub struct CoproductConstructor<A> {
    pub name: parser::Identifier,
    pub signature: Vec<TypeExpression<A, parser::IdentifierPath>>,
}

#[derive(Debug)]
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

impl<A, TypeId> TypeSignature<A, TypeId> {
    pub fn map<F, B, TypeId2>(self, f: F) -> TypeSignature<B, TypeId2>
    where
        F: FnOnce(TypeExpression<A, TypeId>) -> TypeExpression<B, TypeId2>,
    {
        TypeSignature {
            universal_quantifiers: self.universal_quantifiers,
            body: f(self.body),
            phase: PhantomData,
        }
    }

    // Is this really a workable thing?
    pub fn ultimate(&self) -> Self
    where
        A: Clone,
        TypeId: Clone,
    {
        let ultimate = self.body.ultimate();
        Self {
            universal_quantifiers: self.universal_quantifiers.clone(),
            body: ultimate.clone(),
            phase: PhantomData,
        }
    }
}

#[derive(Debug, Clone)]
pub enum TypeExpression<A, TypeId> {
    Constructor(A, TypeId),
    Parameter(A, parser::Identifier),
    Apply(A, ApplyTypeExpr<A, TypeId>),
    Arrow(A, ArrowTypeExpr<A, TypeId>),
    Tuple(A, TupleTypeExpr<A, TypeId>),
}

impl<A, TypeId> TypeExpression<A, TypeId> {
    pub fn annotation(&self) -> &A {
        match self {
            Self::Constructor(a, _)
            | Self::Parameter(a, _)
            | Self::Apply(a, _)
            | Self::Arrow(a, _)
            | Self::Tuple(a, _) => a,
        }
    }

    fn ultimate(&self) -> &Self {
        match self {
            Self::Constructor(..) | Self::Parameter(..) | Self::Apply(..) | Self::Tuple(..) => self,
            Self::Arrow(_, ArrowTypeExpr { codomain, .. }) => codomain.ultimate(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TupleTypeExpr<A, TypeId>(pub Vec<TypeExpression<A, TypeId>>);

#[derive(Debug, Clone)]
pub struct ApplyTypeExpr<A, TypeId> {
    pub function: Box<TypeExpression<A, TypeId>>,
    pub argument: Box<TypeExpression<A, TypeId>>,
    pub phase: PhantomData<TypeId>,
}

#[derive(Debug, Clone)]
pub struct ArrowTypeExpr<A, TypeId> {
    pub domain: Box<TypeExpression<A, TypeId>>,
    pub codomain: Box<TypeExpression<A, TypeId>>,
}

pub type Tree<A, Id> = Rc<Expr<A, Id>>;

#[derive(Debug, Clone)]
pub enum Expr<A, Id> {
    Variable(A, Id),
    InvokeBridge(A, Bridge),
    Constant(A, Literal),
    RecursiveLambda(A, SelfReferential<A, Id>),
    Lambda(A, Lambda<A, Id>),
    Apply(A, Apply<A, Id>),
    Let(A, Binding<A, Id>),
    Tuple(A, Tuple<A, Id>),
    Record(A, Record<A, Id>),
    Construct(A, Construct<A, Id>),
    Project(A, Projection<A, Id>),
    Sequence(A, Sequence<A, Id>),
    Deconstruct(A, Deconstruct<A, Id>),
    If(A, IfThenElse<A, Id>),
    Interpolate(A, Interpolate<A, Id>),
    Ascription(A, TypeAscription<A, Id>),
}

impl<A, Id> Expr<A, Id> {
    pub fn annotation(&self) -> &A {
        match self {
            Expr::Variable(a, ..)
            | Expr::InvokeBridge(a, ..)
            | Expr::Constant(a, ..)
            | Expr::RecursiveLambda(a, ..)
            | Expr::Lambda(a, ..)
            | Expr::Apply(a, ..)
            | Expr::Let(a, ..)
            | Expr::Record(a, ..)
            | Expr::Tuple(a, ..)
            | Expr::Construct(a, ..)
            | Expr::Project(a, ..)
            | Expr::Sequence(a, ..)
            | Expr::Deconstruct(a, ..)
            | Expr::If(a, ..)
            | Expr::Interpolate(a, ..)
            | Expr::Ascription(a, ..) => a,
        }
    }

    pub fn erase_annotation(&self) -> Expr<Erased, Id>
    where
        Self: Annotated<A, Erased, Id, Output = Expr<Erased, Id>>,
    {
        self.map_annotation(&|_| Erased)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Erased;

#[derive(Debug, Clone)]
pub struct Interpolate<A, Id>(pub Vec<Segment<A, Id>>);

#[derive(Debug, Clone)]
pub enum Segment<A, Id> {
    Literal(A, Literal),
    Expression(Tree<A, Id>),
}

#[derive(Debug, Clone)]
pub struct TypeAscription<A, Id> {
    pub ascribed_tree: Tree<A, Id>,
    pub type_signature: TypeSignature<A, QualifiedName>,
}

#[derive(Debug, Clone)]
pub struct Deconstruct<A, Id> {
    pub scrutinee: Tree<A, Id>,
    pub match_clauses: Vec<pattern::MatchClause<A, Id>>,
}

#[derive(Debug, Clone)]
pub struct IfThenElse<A, Id> {
    pub predicate: Tree<A, Id>,
    pub consequent: Tree<A, Id>,
    pub alternate: Tree<A, Id>,
}

#[derive(Debug, Clone)]
pub struct Record<A, Id> {
    pub fields: Vec<(parser::Identifier, Tree<A, Id>)>,
}

impl<A, Id> Record<A, Id> {
    pub fn from_fields(fields: &[(parser::Identifier, Tree<A, Id>)]) -> Self {
        let mut fields = fields.to_vec();
        fields.sort_by(|(t, _), (u, _)| t.cmp(u));

        Self { fields }
    }
}

#[derive(Debug, Clone)]
pub struct Tuple<A, Id> {
    pub elements: Vec<Tree<A, Id>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub enum Literal {
    Int(i64),
    Text(String),
    Bool(bool),
    Unit,
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
pub struct Construct<A, Id> {
    pub constructor: QualifiedName,
    pub arguments: Vec<Tree<A, Id>>,
}

#[derive(Debug, Clone)]
pub struct Sequence<A, Id> {
    pub this: Tree<A, Id>,
    pub and_then: Tree<A, Id>,
}

impl<A, Id> fmt::Display for Expr<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Variable(a, x) => write!(f, "{x}::{a}"),
            Self::InvokeBridge(_, x) => write!(f, "bridge_{}", x),
            Self::Constant(_, x) => write!(f, "{x}"),
            Self::RecursiveLambda(_, x) => write!(f, "{} := {}", x.own_name, x.lambda),
            Self::Lambda(_, x) => write!(f, "{}", x),
            Self::Apply(_, x) => write!(f, "({} {})", x.function, x.argument),
            Self::Let(_, x) => write!(f, "let {} = {} in {}", x.binder, x.bound, x.body),
            Self::Record(_, x) => write!(f, "{x}"),
            Self::Tuple(_, x) => write!(f, "{x}"),
            Self::Construct(_, x) => {
                write!(
                    f,
                    "{} {}",
                    x.constructor,
                    Tuple {
                        elements: x.arguments.clone()
                    }
                )
            }
            Self::Project(_, x) => write!(f, "{}.{}", x.base, x.select),
            Self::Sequence(_, x) => write!(f, "{}; {}", x.this, x.and_then),
            Self::Deconstruct(_, x) => write!(f, "{x}"),
            Self::If(_, x) => write!(f, "{x}"),
            Self::Interpolate(_, x) => write!(f, "{x}"),
            Self::Ascription(_, x) => write!(f, "{}::{}", x.ascribed_tree, x.type_signature),
        }
    }
}

impl<A, Id> fmt::Display for Interpolate<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self(segments) = self;
        let segments = segments
            .into_iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>();

        write!(f, "{}", segments.join(" "))
    }
}

impl<A, Id> fmt::Display for Segment<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Segment::Literal(_, literal) => write!(f, "<{literal}>"),
            Segment::Expression(expr) => write!(f, "<{expr}>"),
        }
    }
}

impl fmt::Display for Erased {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "()")
    }
}

impl<A, Id> fmt::Display for Projection<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { base, select } = self;
        write!(f, "{base}.{select}")
    }
}

impl<A, Id> fmt::Display for Deconstruct<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            scrutinee,
            match_clauses,
        } = self;
        write!(f, "deconstruct {scrutinee}:")?;

        for clause in match_clauses {
            write!(f, "| {} -> {}", clause.pattern, clause.consequent)?;
        }

        Ok(())
    }
}

impl<A, Id> fmt::Display for IfThenElse<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            predicate,
            consequent,
            alternate,
        } = self;
        write!(f, "if {predicate} then {consequent} else {alternate}")
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
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { parameter, body } = self;
        write!(f, "λ{parameter}. {body}")
    }
}

impl<A, Id> fmt::Display for Record<A, Id>
where
    A: fmt::Display,
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
    A: fmt::Display,
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
            Self::Bool(x) => write!(f, "{x}"),
            Self::Unit => write!(f, "()"),
        }
    }
}

impl<A> fmt::Display for CompilationUnit<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.root_module)
    }
}

impl<A> fmt::Display for UseDeclaration<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            qualified_binder,
            module,
        } = self;
        write!(f, "{module}")?;
        if let Some(qualifier) = qualified_binder {
            write!(f, " at {qualifier}")?;
        }

        Ok(())
    }
}

impl<A> fmt::Display for Declaration<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Value(_, decl) => write!(f, "value {decl}"),
            Self::Module(_, decl) => write!(f, "module {decl}"),
            Self::Type(_, decl) => write!(f, "type {decl}"),
            Self::Use(_, decl) => write!(f, "use {decl}"),
        }
    }
}

impl<A> fmt::Display for ValueDeclaration<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { name, declarator } = self;
        write!(f, "{name} is {declarator}")
    }
}

impl<A> fmt::Display for ValueDeclarator<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            type_signature,
            body,
        } = self;
        write!(f, "{body}")?;
        if let Some(ts) = type_signature {
            write!(f, ":: {ts}")?;
        }

        Ok(())
    }
}

impl<A> fmt::Display for ModuleDeclaration<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { name, declarator } = self;
        write!(f, "module {name}:")?;
        write!(f, "{declarator}")
    }
}

impl<A> fmt::Display for ModuleDeclarator<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Inline(declarations) => {
                for m in declarations {
                    writeln!(f, "{m}")?
                }
            }

            Self::External(identifier) => write!(f, "external module {identifier}")?,
        };

        Ok(())
    }
}

impl<A> fmt::Display for TypeDeclaration<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            name,
            type_parameters,
            declarator,
        } = self;
        write!(f, "{name} ::= ")?;
        if !type_parameters.is_empty() {
            write!(f, "forall")?;
            for p in type_parameters {
                write!(f, " {p}")?;
            }
            write!(f, ".")?;
        }
        write!(f, "{declarator}")
    }
}

impl<A> fmt::Display for TypeDeclarator<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Record(_, decl) => write!(f, "{decl}"),
            Self::Coproduct(_, decl) => write!(f, "{decl}"),
        }
    }
}

impl<A> fmt::Display for RecordDeclarator<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for field in &self.fields {
            writeln!(f, "{field}")?;
        }
        Ok(())
    }
}

impl<A> fmt::Display for CoproductDeclarator<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut constructors = self.constructors.iter();

        if let Some(constructor) = constructors.next() {
            write!(f, "{}", constructor)?;

            for c in constructors {
                write!(f, " | {c}")?;
            }
        }

        Ok(())
    }
}

impl<A> fmt::Display for CoproductConstructor<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)?;
        let mut signature = self.signature.iter();

        if let Some(ty_expr) = signature.next() {
            write!(f, "({ty_expr})")?;

            for ty_expr in signature {
                write!(f, " ({ty_expr})")?;
            }
        }

        Ok(())
    }
}

impl<A> fmt::Display for FieldDeclarator<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            name,
            type_signature,
        } = self;
        write!(f, "{name} :: {type_signature}")
    }
}

impl<A, TypeId> fmt::Display for TypeSignature<A, TypeId>
where
    TypeId: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            universal_quantifiers,
            body,
            ..
        } = self;
        if !universal_quantifiers.is_empty() {
            write!(f, "forall ")?;
            for q in universal_quantifiers {
                write!(f, "{q}")?;
            }
            write!(f, ". ")?;
        }

        write!(f, "{body}")?;

        Ok(())
    }
}

impl<A, TypeId> fmt::Display for TypeExpression<A, TypeId>
where
    TypeId: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constructor(_, name) => write!(f, "{name}"),

            Self::Parameter(_, name) => write!(f, "{name}"),

            Self::Apply(
                _,
                ApplyTypeExpr {
                    function, argument, ..
                },
            ) => write!(f, "({function} {argument})"),

            Self::Arrow(_, ArrowTypeExpr { domain, codomain }) => {
                write!(f, "({domain} -> {codomain})")
            }

            Self::Tuple(_, TupleTypeExpr(elements)) => {
                let body = elements
                    .iter()
                    .map(|elt| elt.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({body})")
            }
        }
    }
}
