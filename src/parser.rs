use std::{fmt, iter, result};

use crate::{
    ast,
    lexer::{Keyword, Layout, Literal, SourceLocation, Token, TokenType},
};

pub type Expr = ast::Expr<ParseInfo, IdentifierPath>;
pub type SelfReference = ast::SelfReferential<ParseInfo, IdentifierPath>;
pub type Lambda = ast::Lambda<ParseInfo, IdentifierPath>;
pub type Apply = ast::Apply<ParseInfo, IdentifierPath>;
pub type Binding = ast::Binding<ParseInfo, IdentifierPath>;
pub type Record = ast::Record<ParseInfo, IdentifierPath>;
pub type Tuple = ast::Tuple<ParseInfo, IdentifierPath>;
pub type Projection = ast::Projection<ParseInfo, IdentifierPath>;
pub type TypeExpression = ast::TypeExpression<ParseInfo, IdentifierPath>;

impl Expr {
    pub fn parse_info(&self) -> &ParseInfo {
        self.annotation()
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ParseInfo {
    pub location: SourceLocation,
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

    pub fn with_suffix(mut self, suffix: &str) -> Self {
        self.push(suffix);
        self
    }

    pub fn try_as_simple(&self) -> Option<Identifier> {
        if self.tail.is_empty() {
            Some(Identifier(self.head.clone()))
        } else {
            None
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &str> {
        iter::once(&self.head).chain(&self.tail).map(|s| s.as_str())
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

#[derive(Debug)]
enum Fault {
    UnexpectedEof,
    Expected(TokenType),
    ExpectedIdentifier,
}

type Result<A> = result::Result<A, Fault>;

#[derive(Debug, Default)]
struct Parser<'a> {
    remains: &'a [Token],
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Result<&Token> {
        if !self.remains.is_empty() {
            Ok(&self.remains[0])
        } else {
            Err(Fault::UnexpectedEof)
        }
    }

    fn expect(&mut self, expected: TokenType) -> Result<()> {
        match self.remains {
            [token, remains @ ..] if token.kind == expected => Ok(self.remains = remains),
            _ => Err(Fault::Expected(expected)),
        }
    }

    fn identifier(&mut self) -> Result<(SourceLocation, String)> {
        if let Token {
            kind: TokenType::Identifier(id),
            position,
        } = self.peek()?
        {
            let retval = (*position, id.to_owned());
            self.consume()?;
            Ok(retval)
        } else {
            Err(Fault::ExpectedIdentifier)
        }
    }

    fn consume(&mut self) -> Result<&Token> {
        if let Some(the) = self.remains.first() {
            self.remains = &self.remains[1..];
            Ok(the)
        } else {
            Err(Fault::UnexpectedEof)
        }
    }

    fn parse_block<Parse, A>(&mut self, body: Parse, terminals: &[TokenType]) -> Result<A>
    where
        Parse: FnOnce(&mut Parser<'a>, &[TokenType]) -> Result<A>,
    {
        if self.peek()?.is_indent() {
            self.consume()?;
            let body = body(self, terminals)?;
            self.expect(TokenType::Layout(Layout::Dedent))?;
            Ok(body)
        } else {
            body(self, terminals)
        }
    }

    fn parse_let(&mut self) -> Result<Expr> {
        self.expect(TokenType::Keyword(Keyword::Let))?;
        let (pos, binder) = self.identifier()?;
        self.expect(TokenType::Equals)?;
        let bound = self.parse_block(
            |parser, terminals| parser.parse_expr(terminals),
            &[TokenType::Keyword(Keyword::In)],
        )?;
        self.expect(TokenType::Keyword(Keyword::In))?;
        let body = self.parse_block(|parser, terminals| parser.parse_expr(terminals), &[])?;
        Ok(Expr::Let(
            ParseInfo { location: pos },
            Binding {
                binder: IdentifierPath::new(&binder),
                bound: bound.into(),
                body: body.into(),
            },
        ))
    }

    fn parse_expr(&mut self, _terminals: &[TokenType]) -> Result<Expr> {
        match &self.remains {
            [
                Token {
                    kind: TokenType::Literal(literal),
                    position,
                },
                remains @ ..,
            ] => {
                self.remains = remains;
                Ok(Expr::Constant(
                    ParseInfo {
                        location: *position,
                    },
                    literal.clone().into(),
                ))
            }
            otherwise => panic!("{otherwise:?}"),
        }
    }
}

impl From<Literal> for ast::Literal {
    fn from(value: Literal) -> Self {
        match value {
            Literal::Integer(x) => ast::Literal::Int(x),
            Literal::Text(x) => ast::Literal::Text(x),
            Literal::Bool(..) => todo!(),
        }
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

#[cfg(test)]
mod tests {
    use crate::{
        lexer::{Keyword, LexicalAnalyzer, TokenType},
        parser::{Expr, ParseInfo, Parser},
    };

    #[test]
    fn parsington() {
        let mut lexer = LexicalAnalyzer::default();
        let input = include_str!("3.txt");

        let tokens = lexer.tokenize(&input.chars().collect::<Vec<_>>());

        let mut p = Parser { remains: tokens };
        let x = p.parse_let().unwrap();
    }
}
