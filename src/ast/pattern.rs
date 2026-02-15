use std::{
    collections::{BTreeSet, HashMap},
    default, fmt,
};

use crate::{
    ast::{self, Literal, Tree, namer},
    parser,
};

#[derive(Debug, Clone)]
pub struct MatchClause<A, Id> {
    pub pattern: Pattern<A, Id>,
    pub consequent: Tree<A, Id>,
}

#[derive(Debug, Clone)]
pub enum Pattern<A, Id> {
    Coproduct(A, ConstructorPattern<A, Id>),
    Tuple(A, TuplePattern<A, Id>),
    Struct(A, StructPattern<A, Id>),
    Literally(A, Literal),
    Bind(A, Id),
}

impl<A, Id> Pattern<A, Id> {
    pub fn annotation(&self) -> &A {
        match self {
            Self::Coproduct(a, _)
            | Self::Tuple(a, _)
            | Self::Struct(a, _)
            | Self::Literally(a, _)
            | Self::Bind(a, _) => a,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ConstructorPattern<A, Id> {
    pub constructor: Id, // Ought to be QualifiedName!
    pub arguments: Vec<Pattern<A, Id>>,
}

#[derive(Debug, Clone)]
pub struct TuplePattern<A, Id> {
    pub elements: Vec<Pattern<A, Id>>,
}

#[derive(Debug, Clone)]
pub struct StructPattern<A, Id> {
    pub fields: Vec<(parser::Identifier, Pattern<A, Id>)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum Denotation {
    #[default]
    Empty,
    Structured(Shape),
    Finite(BTreeSet<ast::Literal>),
    Universal,
}

impl Denotation {
    pub fn join(&self, rhs: &Self) -> Option<Self> {
        match (self, rhs) {
            (Self::Empty, x) | (x, Self::Empty) => Some(x.clone()),

            (Self::Structured(p), Self::Structured(q)) => p.join(q).map(Self::Structured),

            (Self::Finite(t), Self::Finite(u)) => Some(Self::Finite(t.union(u).cloned().collect())),

            (Self::Universal, _) | (_, Self::Universal) => Some(Self::Universal),

            _ => None,
        }
    }

    pub fn normalize(&self) -> Self {
        match self {
            Self::Structured(object) => Self::Structured(object.normalize()),

            Self::Finite(set) => {
                let entire_bool_universe =
                    set.contains(&Literal::Bool(true)) && set.contains(&Literal::Bool(false));
                if entire_bool_universe {
                    Self::Universal
                } else {
                    self.clone()
                }
            }

            otherwise => otherwise.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Shape {
    Coproduct(HashMap<namer::QualifiedName, Vec<Denotation>>),
    Struct(HashMap<parser::Identifier, Denotation>),
    Tuple(Vec<Denotation>),
}

impl Shape {
    fn normalize(&self) -> Self {
        match self {
            Self::Coproduct(denots) => Self::Coproduct(
                denots
                    .iter()
                    .map(|(constructor, args)| {
                        (
                            constructor.clone(),
                            args.iter().map(|d| d.normalize()).collect(),
                        )
                    })
                    .collect(),
            ),

            Self::Struct(denots) => Self::Struct(
                denots
                    .iter()
                    .map(|(field, denot)| (field.clone(), denot.normalize()))
                    .collect(),
            ),

            Self::Tuple(denots) => Self::Tuple(denots.iter().map(|d| d.normalize()).collect()),
        }
    }

    fn join(&self, rhs: &Self) -> Option<Self> {
        match (self, rhs) {
            (Self::Coproduct(lhs), Self::Coproduct(rhs)) => {
                let mut lhs = lhs.clone();
                for (constructor, rhs) in rhs {
                    if let Some(lhs) = lhs.get_mut(constructor) {
                        join_many(lhs, rhs)?;
                    } else {
                        lhs.insert(constructor.clone(), rhs.clone());
                    }
                }

                Some(Self::Coproduct(lhs))
            }

            (Self::Struct(lhs), Self::Struct(rhs)) => {
                let mut lhs = lhs.clone();
                for (field, rhs) in rhs {
                    if let Some(lhs) = lhs.get_mut(field) {
                        *lhs = lhs.join(rhs)?;
                    } else {
                        None?
                    }
                }
                Some(Self::Struct(lhs))
            }

            (Self::Tuple(lhs), Self::Tuple(rhs)) => {
                let mut lhs = lhs.clone();
                join_many(&mut lhs, rhs);
                Some(Self::Tuple(lhs))
            }

            _ => None,
        }
    }
}

fn join_many(lhs: &mut [Denotation], rhs: &[Denotation]) -> Option<()> {
    for (lhs, rhs) in lhs.iter_mut().zip(rhs) {
        *lhs = lhs.join(rhs)?;
    }
    Some(())
}

impl<A, Id> fmt::Display for MatchClause<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            pattern,
            consequent,
        } = self;
        write!(f, "{pattern} -> {consequent}")
    }
}

impl<A, Id> fmt::Display for Pattern<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Coproduct(_, x) => write!(f, "{x}"),
            Self::Tuple(_, x) => write!(f, "{x}"),
            Self::Struct(_, x) => write!(f, "{x}"),
            Self::Literally(_, x) => write!(f, "{x}"),
            Self::Bind(_, x) => write!(f, "{x}"),
        }
    }
}

impl<A, Id> fmt::Display for ConstructorPattern<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            constructor,
            arguments,
        } = self;
        write!(f, "{constructor}")?;
        for argument in arguments {
            write!(f, " {argument}")?;
        }

        Ok(())
    }
}

impl<A, Id> fmt::Display for TuplePattern<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { elements } = self;
        let mut elements = elements.iter();

        if let Some(element) = elements.next() {
            write!(f, "{element}")?;
        }

        for element in elements {
            write!(f, ", {element}")?;
        }

        Ok(())
    }
}

impl<A, Id> fmt::Display for StructPattern<A, Id>
where
    A: fmt::Display,
    Id: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { fields } = self;
        write!(f, "{{ ")?;

        let mut fields = fields.iter();
        if let Some((field, pattern)) = fields.next() {
            write!(f, "{field}: {pattern}")?;
        }

        for (field, pattern) in fields {
            write!(f, "; {field}: {pattern}")?;
        }

        write!(f, " }}")
    }
}
