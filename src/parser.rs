use std::{fmt, iter};

use crate::ast;

pub type Expr = ast::Expr<ParseInfo, IdentifierPath>;
pub type SelfReference = ast::SelfReferential<ParseInfo, IdentifierPath>;
pub type Lambda = ast::Lambda<ParseInfo, IdentifierPath>;
pub type Apply = ast::Apply<ParseInfo, IdentifierPath>;
pub type Binding = ast::Binding<ParseInfo, IdentifierPath>;
pub type Record = ast::Record<ParseInfo, IdentifierPath>;
pub type Tuple = ast::Tuple<ParseInfo, IdentifierPath>;
pub type Projection = ast::Projection<ParseInfo, IdentifierPath>;

impl Expr {
    pub fn parse_info(&self) -> &ParseInfo {
        self.annotation()
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct ParseInfo {
    pub location: SourceLocation,
}

#[derive(Debug, Copy, Clone, Default)]
pub struct SourceLocation {
    pub row: usize,
    pub col: usize,
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub struct IdentifierPath {
    pub head: String,
    pub tail: Vec<String>,
}

impl IdentifierPath {
    pub fn new(head: &str) -> Self {
        Self {
            head: head.to_owned(),
            tail: vec![],
        }
    }

    pub fn try_from_components(components: &[&str]) -> Option<Self> {
        if let [head, tail @ ..] = components {
            Some(Self {
                head: (*head).to_owned(),
                tail: tail.iter().map(|&s| s.to_owned()).collect(),
            })
        } else {
            None
        }
    }

    pub fn as_root_module_member(&self) -> Self {
        let Self { head, tail } = self;
        Self {
            head: ast::ROOT_MODULE_NAME.to_owned(),
            tail: {
                let mut new_tail = Vec::with_capacity(1 + tail.capacity());
                new_tail.push(head.clone());
                new_tail.extend_from_slice(tail);
                new_tail
            },
        }
    }

    pub fn push(&mut self, component: &str) {
        self.tail.push(component.to_owned());
    }

    pub fn make_member_path(&self, suffix: &str) -> String {
        self.iter()
            .chain(iter::once(suffix))
            .map(|s| s.to_owned())
            .collect::<Vec<_>>()
            .join("/")
    }

    pub fn try_as_simple(&self) -> Option<Identifier> {
        if self.tail.is_empty() {
            Some(Identifier(self.head.clone()))
        } else {
            None
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &str> {
        iter::once(self.head.as_str()).chain(self.tail.iter().map(|s| s.as_str()))
    }
}

// What about ParseInfo?
#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub struct Identifier(String);

impl Identifier {
    pub fn from_str(id: &str) -> Self {
        Self(id.to_owned())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self(id) = self;
        write!(f, "{id}")
    }
}

impl fmt::Display for IdentifierPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { head, tail } = self;
        write!(f, "{head}")?;
        for part in tail {
            write!(f, ".{part}")?;
        }
        Ok(())
    }
}
