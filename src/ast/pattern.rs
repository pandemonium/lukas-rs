use std::{collections::BTreeSet, fmt};

use crate::hash::HashMap;

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

    pub fn map_id<F, B>(self, f: &F) -> Pattern<A, B>
    where
        F: Fn(Id) -> B,
    {
        match self {
            Self::Coproduct(a, the) => Pattern::Coproduct(
                a,
                ConstructorPattern {
                    constructor: f(the.constructor),
                    arguments: the.arguments.into_iter().map(|p| p.map_id(f)).collect(),
                },
            ),

            Self::Tuple(a, the) => Pattern::Tuple(
                a,
                TuplePattern {
                    elements: the.elements.into_iter().map(|p| p.map_id(f)).collect(),
                },
            ),

            Self::Struct(a, the) => Pattern::Struct(
                a,
                StructPattern {
                    fields: the
                        .fields
                        .into_iter()
                        .map(|(a, label, p)| (a, label, p.map_id(f)))
                        .collect(),
                },
            ),

            Self::Literally(a, the) => Pattern::Literally(a, the),

            Self::Bind(a, the) => Pattern::Bind(a, f(the)),
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
    /// Each field's label, where the label is written, and the pattern matched
    /// against it -- the same triple a record literal's fields carry, for the same
    /// reason: a label with no position is a label an editor cannot answer about.
    pub fields: Vec<(A, parser::Identifier, Pattern<A, Id>)>,
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
    pub fn is_subsumed_by(&self, wider: &Self) -> bool {
        match (self, wider) {
            (_, Self::Universal) => true,
            (Self::Empty, _) => true,

            (Self::Structured(narrow), Self::Structured(wide)) => narrow.is_subsumed_by(wide),

            (Self::Finite(narrow), Self::Finite(wide)) => narrow.is_subset(wide),

            _ => false,
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

    fn is_subsumed_by(&self, wider: &Self) -> bool {
        match (self, wider) {
            // Every constructor this shape can match must be one `wider` matches too,
            // with arguments that are themselves subsumed.
            (Self::Coproduct(narrow), Self::Coproduct(wide)) => {
                narrow.iter().all(|(constructor, arguments)| {
                    wide.get(constructor).is_some_and(|wide_arguments| {
                        arguments.len() == wide_arguments.len()
                            && arguments
                                .iter()
                                .zip(wide_arguments)
                                .all(|(narrow, wide)| narrow.is_subsumed_by(wide))
                    })
                })
            }

            (Self::Struct(narrow), Self::Struct(wide)) => narrow.iter().all(|(field, narrow)| {
                wide.get(field)
                    .is_some_and(|wide| narrow.is_subsumed_by(wide))
            }),

            (Self::Tuple(narrow), Self::Tuple(wide)) => {
                narrow.len() == wide.len()
                    && narrow
                        .iter()
                        .zip(wide)
                        .all(|(narrow, wide)| narrow.is_subsumed_by(wide))
            }

            _ => false,
        }
    }
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

        // Parenthesise so a nested tuple pattern shows its shape: `((a, b), c)` rather than the
        // flat-looking `a, b, c` (mirrors the parenthesised `Val::Product` display).
        write!(f, "(")?;
        if let Some(element) = elements.next() {
            write!(f, "{element}")?;
        }

        for element in elements {
            write!(f, ", {element}")?;
        }

        write!(f, ")")
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
        if let Some((_, field, pattern)) = fields.next() {
            write!(f, "{field}: {pattern}")?;
        }

        for (_, field, pattern) in fields {
            write!(f, "; {field}: {pattern}")?;
        }

        write!(f, " }}")
    }
}
