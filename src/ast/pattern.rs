use std::fmt;

use crate::{
    ast::{Literal, Tree},
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

#[derive(Debug, Clone)]
pub struct ConstructorPattern<A, Id> {
    pub constructor: Id,
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

impl<A, Id> fmt::Display for Pattern<A, Id>
where
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
