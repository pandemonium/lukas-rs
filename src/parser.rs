use std::fmt;

use crate::ast;

#[derive(Debug, Clone, Copy, Default)]
pub struct ParseInfo {
    pub location: SourceLocation,
}

#[derive(Debug, Copy, Clone, Default)]
pub struct SourceLocation {
    pub row: usize,
    pub col: usize,
}

// This should be IdentiferPath at this point
#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub struct Identifier {
    head: String,
    tail: Vec<String>,
}

impl Identifier {
    pub fn from_str(id: &str) -> Self {
        Self {
            head: id.to_owned(),
            tail: vec![],
        }
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { head, tail } = self;
        write!(f, "{head}")?;
        for part in tail {
            write!(f, ".{part}")?;
        }
        Ok(())
    }
}

pub type Expr = ast::Expr<ParseInfo, Identifier>;
impl Expr {
    pub fn parse_info(&self) -> &ParseInfo {
        self.annotation()
    }
}

pub type SelfReference = ast::SelfReferential<ParseInfo, Identifier>;
pub type Lambda = ast::Lambda<ParseInfo, Identifier>;
pub type Apply = ast::Apply<ParseInfo, Identifier>;
pub type Binding = ast::Binding<ParseInfo, Identifier>;
pub type Tuple = ast::Tuple<ParseInfo, Identifier>;
pub type Projection = ast::Projection<ParseInfo, Identifier>;
