use std::{fmt, iter, result};

use backtrace::{Backtrace, BacktraceSymbol};

use crate::{
    ast,
    lexer::{Interpolation, Keyword, Layout, Literal, Operator, SourceLocation, Token, TokenKind},
};

pub type Expr = ast::Expr<ParseInfo, IdentifierPath>;
pub type SelfReference = ast::SelfReferential<ParseInfo, IdentifierPath>;
pub type Lambda = ast::Lambda<ParseInfo, IdentifierPath>;
pub type Apply = ast::Apply<ParseInfo, IdentifierPath>;
pub type Binding = ast::Binding<ParseInfo, IdentifierPath>;
pub type Record = ast::Record<ParseInfo, IdentifierPath>;
pub type Tuple = ast::Tuple<ParseInfo, IdentifierPath>;
pub type Projection = ast::Projection<ParseInfo, IdentifierPath>;
pub type Sequence = ast::Sequence<ParseInfo, IdentifierPath>;
pub type TypeExpression = ast::TypeExpression<ParseInfo, IdentifierPath>;

impl Expr {
    pub fn parse_info(&self) -> &ParseInfo {
        self.annotation()
    }

    pub fn position(&self) -> &SourceLocation {
        &self.parse_info().location
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ParseInfo {
    pub location: SourceLocation,
}

impl ParseInfo {
    pub fn from_position(location: SourceLocation) -> Self {
        Self { location }
    }
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
    Expected {
        expected: TokenKind,
        found: TokenKind,
        position: SourceLocation,
    },
    ExpectedIdentifier,
}

type Result<A> = result::Result<A, Fault>;

#[derive(Debug)]
struct TraceLogEntry<'a> {
    step: String,
    remains: &'a [Token],
}

impl<'a> fmt::Display for TraceLogEntry<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { step, remains } = self;
        write!(
            f,
            "{step:<20}: {}",
            remains
                .iter()
                .map(|t| t.to_string())
                .take(10)
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

#[derive(Debug, Default)]
struct Parser<'a> {
    remains: &'a [Token],
}

impl<'a> Parser<'a> {
    fn trace(&mut self) {
        let backtrace = Backtrace::new();
        let calling_symbol = backtrace.frames().iter().find_map(|frame| {
            frame
                .symbols()
                .iter()
                .find_map(|sym| sym.name().filter(|n| !n.to_string().contains("trace")))
        });

        if let Some(caller) = calling_symbol {
            let caller_name = caller.to_string();
            let caller = caller_name.split("::").collect::<Vec<_>>();
            let caller = caller.get(caller.len() - 2);
            let e = TraceLogEntry {
                step: caller.unwrap_or(&caller_name.as_str()).to_string(),
                remains: self.remains,
            };
            println!("{e}");
        } else {
            println!("Unknown caller.")
        }
    }

    fn peek(&self) -> Result<&Token> {
        if !self.remains.is_empty() {
            Ok(&self.remains[0])
        } else {
            Err(Fault::UnexpectedEof)
        }
    }

    fn expect(&mut self, expected: TokenKind) -> Result<&Token> {
        match self.remains {
            [token, remains @ ..] if token.kind == expected => {
                self.remains = remains;
                Ok(token)
            }
            [token, ..] => Err(Fault::Expected {
                expected,
                found: token.kind.clone(),
                position: token.position,
            }),
            _ => panic!(),
        }
    }

    fn identifier(&mut self) -> Result<(SourceLocation, String)> {
        if let Token {
            kind: TokenKind::Identifier(id),
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

    fn consume_if<P>(&mut self, mut p: P) -> Result<&Token>
    where
        P: FnMut(&Token) -> bool,
    {
        if let Some(the) = self.remains.first()
            && p(the)
        {
            self.remains = &self.remains[1..];
            Ok(the)
        } else {
            Err(Fault::UnexpectedEof)
        }
    }

    fn parse_block<F, A>(&mut self, parse_body: F) -> Result<A>
    where
        F: FnOnce(&mut Parser<'a>) -> Result<A>,
    {
        self.trace();

        if self.peek()?.is_indent() {
            self.consume()?;
            let body = parse_body(self)?;
            // This does not interact well with sequences because parse_sequence
            // does not see a sequence separator anymore after this
            println!("parse_block: delete dedent");
            self.expect(TokenKind::Layout(Layout::Dedent))?;
            Ok(body)
        } else {
            parse_body(self)
        }
    }

    fn parse_let(&mut self) -> Result<Expr> {
        self.trace();

        let location = *self.expect(TokenKind::Keyword(Keyword::Let))?.location();
        let (.., binder) = self.identifier()?;
        self.expect(TokenKind::Equals)?;
        let bound = self.parse_block(|parser| parser.parse_sequence())?;
        if self.peek()?.is_newline() {
            self.consume()?;
        }
        self.expect(TokenKind::Keyword(Keyword::In))?;
        if self.peek()?.is_newline() {
            self.consume()?;
        }
        let body = self.parse_block(|parser| parser.parse_sequence())?;
        println!("parse_let: body `{body}`");
        Ok(Expr::Let(
            ParseInfo { location },
            Binding {
                binder: IdentifierPath::new(&binder),
                bound: bound.into(),
                body: body.into(),
            },
        ))
    }

    // This probably needs to be a parse_seq_prefix/infix pair too
    // because this style super bort the grand parent
    fn parse_sequence(&mut self) -> Result<Expr> {
        self.trace();

        let prefix = self.parse_expression(0)?;

        println!(
            "parse_sequence: prefix `{prefix}` at {}",
            prefix.parse_info().location
        );

        match self.remains {
            [t, u, ..] if t.is_sequence_separator() && Self::is_expr_prefix(&u.kind) => {
                self.consume()?;
                self.parse_subsequent(prefix)
            }

            // If the previous expression ends in a Dedent "back to" sequence level
            [t, u, ..]
                if t.is_dedent()
                    && Self::is_expr_prefix(&u.kind)
                    && u.location().is_same_block(&prefix.parse_info().location) =>
            {
                self.consume()?;
                self.parse_subsequent(prefix)
            }

            [t, u, ..]
                if Self::is_expr_prefix(&t.kind)
                    && t.location().is_same_block(&prefix.parse_info().location)
                    && u.kind != TokenKind::End =>
            {
                self.parse_subsequent(prefix)
            }

            _ => {
                println!("parse_sequence: sequence concluded with prefix `{prefix}`");
                Ok(prefix)
            }
        }
    }

    fn parse_subsequent(&mut self, this: Expr) -> Result<Expr> {
        self.trace();

        let and_then = self.parse_sequence()?;

        Ok(Expr::Sequence(
            *and_then.parse_info(),
            Sequence {
                this: this.into(),
                and_then: and_then.into(),
            },
        ))
    }

    fn parse_expression(&mut self, precedence: usize) -> Result<Expr> {
        self.trace();

        let prefix = self.parse_expr_prefix()?;
        self.parse_expr_infix(prefix, precedence)
    }

    fn parse_expr_prefix(&mut self) -> Result<Expr> {
        self.trace();

        match self.remains {
            [
                Token {
                    kind: TokenKind::Literal(lit),
                    position,
                },
                remains @ ..,
            ] => {
                self.remains = remains;
                self.parse_literal(lit, position)
            }

            [
                Token {
                    kind: TokenKind::Identifier(id),
                    position,
                },
                remains @ ..,
            ] => {
                self.remains = remains;
                self.parse_identifier(id, position)
            }

            [t, ..] if t.is_keyword(Keyword::Let) => self.parse_let(),

            otherwise => panic!("{otherwise:?}"),
        }
    }

    fn is_expr_prefix(kind: &TokenKind) -> bool {
        !matches!(
            kind,
            TokenKind::Layout(Layout::Dedent)
                | TokenKind::Layout(Layout::Newline)
                | TokenKind::End
                | TokenKind::Keyword(
                    Keyword::And
                        | Keyword::Or
                        | Keyword::Xor
                        | Keyword::Else
                        | Keyword::Into
                        | Keyword::In
                )
                | TokenKind::Interpolate(Interpolation::Epilogue(..))
        )
    }

    // All infices must be right of lhs.
    fn parse_expr_infix(&mut self, lhs: Expr, context_precedence: usize) -> Result<Expr> {
        let terminals = [
            TokenKind::Layout(Layout::Dedent),
            TokenKind::Keyword(Keyword::Let),
            TokenKind::Keyword(Keyword::In),
            TokenKind::End,
        ];
        let is_terminal = |t| terminals.contains(t);

        self.trace();

        match self.remains {
            [t, ..] if is_terminal(&t.kind) => Ok(lhs),

            [t, u, ..] if t.is_layout() && is_terminal(&u.kind) => Ok(lhs),

            // f
            //   x <- this
            // or:
            // f
            //   x
            //   y <- this
            [t, u, ..]
                if (t.is_indent() || t.is_newline())
                    && Self::is_expr_prefix(&u.kind)
                    && Operator::Juxtaposition.precedence() > context_precedence
                    && (u.location().is_descendant_of(&lhs.position())) =>
            {
                println!("Calling parse_juxtaposed(1)");
                self.consume()?; //the indent
                self.parse_juxtaposed(lhs, context_precedence)
            }

            // f x
            [t, u, ..]
                if Self::is_expr_prefix(&t.kind)
                    && Operator::Juxtaposition.precedence() > context_precedence =>
            {
                println!("Calling parse_juxtaposed(2)");
                self.parse_juxtaposed(lhs, context_precedence)
            }

            _ => Ok(lhs),
        }
    }

    fn parse_juxtaposed(&mut self, lhs: Expr, context_precedence: usize) -> Result<Expr> {
        self.trace();

        let rhs = self.parse_expr_prefix()?;
        self.parse_expr_infix(
            Expr::Apply(
                *lhs.parse_info(),
                ast::Apply {
                    function: lhs.into(),
                    argument: rhs.into(),
                },
            ),
            context_precedence,
        )
    }

    fn parse_literal(&mut self, literal: &Literal, position: &SourceLocation) -> Result<Expr> {
        Ok(Expr::Constant(
            ParseInfo {
                location: *position,
            },
            literal.clone().into(),
        ))
    }

    fn parse_identifier(&mut self, id: &str, position: &SourceLocation) -> Result<Expr> {
        Ok(Expr::Variable(
            ParseInfo::from_position(*position),
            IdentifierPath::new(id),
        ))
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
    use crate::{lexer::LexicalAnalyzer, parser::Parser};

    #[test]
    fn parsington() {
        let mut lexer = LexicalAnalyzer::default();
        let input = include_str!("3.txt");

        let tokens = lexer.tokenize(&input.chars().collect::<Vec<_>>());

        for t in tokens {
            println!("{t}")
        }

        let mut p = Parser { remains: tokens };
        let x = p.parse_sequence().unwrap();
        println!("{x}")
    }
}
