use super::*;

pub trait Annotated<A, B, Id> {
    type Output;
    fn map_annotation<F>(&self, f: F) -> Self::Output
    where
        F: Fn(&A) -> B;
}

impl<A, B, Id> Annotated<A, B, Id> for Expr<A, Id>
where
    Id: Clone,
{
    type Output = Expr<B, Id>;

    fn map_annotation<F>(&self, f: F) -> Self::Output
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
                Expr::Constant(a, node) => Expr::Constant(f(a), node.clone()),
                Expr::RecursiveLambda(a, node) => {
                    Expr::RecursiveLambda(f(a), node.map_annotation(&f))
                }
                Expr::Lambda(a, node) => Expr::Lambda(f(a), node.map_annotation(&f)),
                Expr::Apply(a, node) => Expr::Apply(f(a), node.map_annotation(&f)),
                Expr::Let(a, node) => Expr::Let(f(a), node.map_annotation(&f)),
                Expr::Record(a, node) => Expr::Record(f(a), node.map_annotation(&f)),
                Expr::Tuple(a, node) => Expr::Tuple(f(a), node.map_annotation(&f)),
                Expr::Project(a, node) => Expr::Project(f(a), node.map_annotation(&f)),
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

    fn map_annotation<F>(&self, f: F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        Rc::new((**self).map_annotation(&f))
    }
}

impl<A, B, Id> Annotated<A, B, Id> for SelfReferential<A, Id>
where
    Id: Clone,
{
    type Output = SelfReferential<B, Id>;

    fn map_annotation<F>(&self, f: F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        let SelfReferential {
            own_name: name,
            lambda,
        } = self;
        SelfReferential {
            own_name: name.clone(),
            lambda: lambda.map_annotation(&f),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for Lambda<A, Id>
where
    Id: Clone,
{
    type Output = Lambda<B, Id>;

    fn map_annotation<F>(&self, f: F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        let Lambda { parameter, body } = self;
        Lambda {
            parameter: parameter.clone(),
            body: body.map_annotation(&f),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for Apply<A, Id>
where
    Id: Clone,
{
    type Output = Apply<B, Id>;

    fn map_annotation<F>(&self, f: F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        let Apply { function, argument } = self;
        Apply {
            function: function.map_annotation(&f),
            argument: argument.map_annotation(&f),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for Binding<A, Id>
where
    Id: Clone,
{
    type Output = Binding<B, Id>;

    fn map_annotation<F>(&self, f: F) -> Self::Output
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
            bound: bound.map_annotation(&f),
            body: body.map_annotation(&f),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for Record<A, Id>
where
    Id: Clone,
{
    type Output = Record<B, Id>;

    fn map_annotation<F>(&self, f: F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        Record {
            fields: self
                .fields
                .iter()
                .map(|(label, e)| (label.clone(), e.map_annotation(&f)))
                .collect(),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for Tuple<A, Id>
where
    Id: Clone,
{
    type Output = Tuple<B, Id>;

    fn map_annotation<F>(&self, f: F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        Tuple {
            elements: self.elements.iter().map(|e| e.map_annotation(&f)).collect(),
        }
    }
}

impl<A, B, Id> Annotated<A, B, Id> for Projection<A, Id>
where
    Id: Clone,
{
    type Output = Projection<B, Id>;

    fn map_annotation<F>(&self, f: F) -> Self::Output
    where
        F: Fn(&A) -> B,
    {
        Projection {
            base: self.base.map_annotation(f).into(),
            select: self.select.clone(),
        }
    }
}
