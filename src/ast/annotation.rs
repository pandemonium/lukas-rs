use crate::ast::pattern::{ConstructorPattern, MatchClause, Pattern, StructPattern, TuplePattern};

use super::*;

pub trait Annotated<A, B, Id> {
    type Output;
    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B;
}

impl<A, B, Id> Annotated<A, B, Id> for Expr<A, Id>
where
    Id: Clone,
{
    type Output = Expr<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        // Gets around the monomorphisation phase in the compiler which seems to
        // get thrown off by the recursive nature of this data type. It diverges.
        fn inner<A, B, Id>(node: &Expr<A, Id>, f: &dyn Fn(&A) -> B) -> Expr<B, Id>
        where
            Id: Clone,
        {
            match node {
                Expr::Variable(a, node) => Expr::Variable(f(a), node.clone()),
                Expr::InvokeBridge(a, node) => Expr::InvokeBridge(f(a), node.clone()),
                Expr::Constant(a, node) => Expr::Constant(f(a), node.clone()),
                Expr::RecursiveLambda(a, node) => {
                    Expr::RecursiveLambda(f(a), node.map_annotation(&f))
                }
                Expr::Lambda(a, node) => Expr::Lambda(f(a), node.map_annotation(&f)),
                Expr::Apply(a, node) => Expr::Apply(f(a), node.map_annotation(&f)),
                Expr::Let(a, node) => Expr::Let(f(a), node.map_annotation(&f)),
                Expr::Record(a, node) => Expr::Record(f(a), node.map_annotation(&f)),
                Expr::Tuple(a, node) => Expr::Tuple(f(a), node.map_annotation(&f)),
                Expr::Construct(a, node) => Expr::Construct(f(a), node.map_annotation(&f)),
                Expr::Project(a, node) => Expr::Project(f(a), node.map_annotation(&f)),
                Expr::Sequence(a, node) => Expr::Sequence(f(a), node.map_annotation(&f)),
                Expr::Deconstruct(a, node) => Expr::Deconstruct(f(a), node.map_annotation(&f)),
                Expr::If(a, node) => Expr::If(f(a), node.map_annotation(&f)),
                Expr::Interpolate(a, node) => Expr::Interpolate(f(a), node.map_annotation(&f)),
                Expr::Ascription(a, node) => Expr::Ascription(f(a), node.map_annotation(&f)),
            }
        }

        inner(self, &f)
    }
}

impl<A, B, Id, T> Annotated<A, B, Id> for Rc<T>
where
    T: Annotated<A, B, Id>,
{
    type Output = Rc<T::Output>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        Rc::new((**self).map_annotation(f))
    }
}

impl<A, B, Id> Annotated<A, B, Id> for SelfReferential<A, Id>
where
    Id: Clone,
{
    type Output = SelfReferential<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        let SelfReferential {
            own_name: name,
            lambda,
        } = self;
        SelfReferential {
            own_name: name.clone(),
            lambda: lambda.map_annotation(f),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for Lambda<A, Id>
where
    Id: Clone,
{
    type Output = Lambda<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        let Lambda { parameter, body } = self;
        Lambda {
            parameter: parameter.clone(),
            body: body.map_annotation(f),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for Apply<A, Id>
where
    Id: Clone,
{
    type Output = Apply<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        let Apply { function, argument } = self;
        Apply {
            function: function.map_annotation(f),
            argument: argument.map_annotation(f),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for Binding<A, Id>
where
    Id: Clone,
{
    type Output = Binding<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        let Binding {
            binder,
            bound,
            body,
        } = self;
        Binding {
            binder: binder.clone(),
            bound: bound.map_annotation(f),
            body: body.map_annotation(f),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for Record<A, Id>
where
    Id: Clone,
{
    type Output = Record<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        Record {
            fields: self
                .fields
                .iter()
                .map(|(label, e)| (label.clone(), e.map_annotation(f)))
                .collect(),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for Tuple<A, Id>
where
    Id: Clone,
{
    type Output = Tuple<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        Tuple {
            elements: self.elements.iter().map(|e| e.map_annotation(f)).collect(),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for Construct<A, Id>
where
    Id: Clone,
{
    type Output = Construct<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        let Self {
            constructor: name,
            arguments,
        } = self;
        Construct {
            constructor: name.clone(),
            arguments: arguments
                .iter()
                .map(|expr| expr.map_annotation(f))
                .collect(),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for Projection<A, Id>
where
    Id: Clone,
{
    type Output = Projection<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        Projection {
            base: self.base.map_annotation(f),
            select: self.select.clone(),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for Sequence<A, Id>
where
    Id: Clone,
{
    type Output = Sequence<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        Sequence {
            this: self.this.map_annotation(f),
            and_then: self.and_then.map_annotation(f),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for Deconstruct<A, Id>
where
    Id: Clone,
{
    type Output = Deconstruct<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        Deconstruct {
            scrutinee: self.scrutinee.map_annotation(f).into(),
            match_clauses: self
                .match_clauses
                .iter()
                .map(|clause| MatchClause {
                    pattern: clause.pattern.map_annotation(f),
                    consequent: clause.consequent.map_annotation(f).into(),
                })
                .collect(),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for IfThenElse<A, Id>
where
    Id: Clone,
{
    type Output = IfThenElse<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        IfThenElse {
            predicate: self.predicate.map_annotation(f),
            consequent: self.consequent.map_annotation(f),
            alternate: self.alternate.map_annotation(f),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for TypeAscription<A, Id>
where
    Id: Clone,
{
    type Output = TypeAscription<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        TypeAscription {
            ascribed_tree: self.ascribed_tree.map_annotation(f),
            type_signature: self.type_signature.map_annotation(f),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for TypeSignature<A, Id>
where
    Id: Clone,
{
    type Output = TypeSignature<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        TypeSignature {
            universal_quantifiers: self.universal_quantifiers.clone(),
            body: self.body.map_annotation(f),
            phase: PhantomData,
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for TypeExpression<A, Id>
where
    Id: Clone,
{
    type Output = TypeExpression<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        match self {
            Self::Constructor(a, id) => TypeExpression::Constructor(f(a), id.clone()),
            Self::Parameter(a, id) => TypeExpression::Parameter(f(a), id.clone()),
            Self::Apply(a, node) => TypeExpression::Apply(f(a), node.map_annotation(f)),
            Self::Arrow(a, node) => TypeExpression::Arrow(f(a), node.map_annotation(f)),
            Self::Tuple(a, node) => TypeExpression::Tuple(f(a), node.map_annotation(f)),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for ApplyTypeExpr<A, Id>
where
    Id: Clone,
{
    type Output = ApplyTypeExpr<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        ApplyTypeExpr {
            function: self.function.map_annotation(f).into(),
            argument: self.argument.map_annotation(f).into(),
            phase: PhantomData,
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for ArrowTypeExpr<A, Id>
where
    Id: Clone,
{
    type Output = ArrowTypeExpr<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        ArrowTypeExpr {
            domain: self.domain.map_annotation(f).into(),
            codomain: self.codomain.map_annotation(f).into(),
        }
    }
}
impl<A, B, Id> Annotated<A, B, Id> for TupleTypeExpr<A, Id>
where
    Id: Clone,
{
    type Output = TupleTypeExpr<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        let Self(elements) = self;
        TupleTypeExpr(elements.iter().map(|e| e.map_annotation(f)).collect())
    }
}

impl<A, B, Id> Annotated<A, B, Id> for Interpolate<A, Id>
where
    Id: Clone,
{
    type Output = Interpolate<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        let Self(segments) = self;
        Interpolate(
            segments
                .into_iter()
                .map(|s| match s {
                    Segment::Literal(a, literal) => Segment::Literal(f(a), literal.clone()),
                    Segment::Expression(expr) => Segment::Expression(expr.map_annotation(f)),
                })
                .collect(),
        )
    }
}

impl<A, B, Id> Annotated<A, B, Id> for Pattern<A, Id>
where
    Id: Clone,
{
    type Output = Pattern<B, Id>;

    fn map_annotation<F>(&self, f: &F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        match self {
            Self::Coproduct(a, pattern) => Pattern::Coproduct(
                f(a),
                ConstructorPattern {
                    constructor: pattern.constructor.clone(),
                    arguments: pattern
                        .arguments
                        .iter()
                        .map(|arg| arg.map_annotation(f))
                        .collect(),
                },
            ),
            Self::Tuple(a, pattern) => Pattern::Tuple(
                f(a),
                TuplePattern {
                    elements: pattern
                        .elements
                        .iter()
                        .map(|elt| elt.map_annotation(f))
                        .collect(),
                },
            ),
            Self::Struct(a, pattern) => Pattern::Struct(
                f(a),
                StructPattern {
                    fields: pattern
                        .fields
                        .iter()
                        .map(|(field, pattern)| (field.clone(), pattern.map_annotation(f)))
                        .collect(),
                },
            ),
            Self::Literally(a, pattern) => Pattern::Literally(f(a), pattern.clone()),
            Self::Bind(a, pattern) => Pattern::Bind(f(a), pattern.clone()),
        }
    }
}
