use std::{cell::Cell, fmt, iter, marker::PhantomData, result, vec};

use backtrace::Backtrace;

use crate::{
    ast::{
        self, ApplyTypeExpr, ArrowTypeExpr, CompilationUnit, CoproductConstructor,
        CoproductDeclarator, Declaration, FieldDeclarator, RecordDeclarator, Tree, TypeDeclaration,
        TypeDeclarator, ValueDeclaration, ValueDeclarator,
    },
    lexer::{Interpolation, Keyword, Layout, Literal, Operator, SourceLocation, Token, TokenKind},
};

pub type Expr = ast::Expr<ParseInfo, IdentifierPath>;
pub type SelfReferential = ast::SelfReferential<ParseInfo, IdentifierPath>;
pub type Lambda = ast::Lambda<ParseInfo, IdentifierPath>;
pub type Apply = ast::Apply<ParseInfo, IdentifierPath>;
pub type Binding = ast::Binding<ParseInfo, IdentifierPath>;
pub type Record = ast::Record<ParseInfo, IdentifierPath>;
pub type Tuple = ast::Tuple<ParseInfo, IdentifierPath>;
pub type Projection = ast::Projection<ParseInfo, IdentifierPath>;
pub type Construct = ast::Construct<ParseInfo, IdentifierPath>;
pub type Sequence = ast::Sequence<ParseInfo, IdentifierPath>;
pub type Deconstruct = ast::Deconstruct<ParseInfo, IdentifierPath>;
pub type Pattern = ast::pattern::Pattern<ParseInfo, IdentifierPath>;
pub type MatchClause = ast::pattern::MatchClause<ParseInfo, IdentifierPath>;
pub type ConstructorPattern = ast::pattern::ConstructorPattern<ParseInfo, IdentifierPath>;
pub type TuplePattern = ast::pattern::TuplePattern<ParseInfo, IdentifierPath>;
pub type StructPattern = ast::pattern::StructPattern<ParseInfo, IdentifierPath>;
pub type TypeExpression = ast::TypeExpression<ParseInfo, IdentifierPath>;
pub type TypeSignature = ast::TypeSignature<ParseInfo, IdentifierPath>;

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

#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
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
        self.clone()
            .prefigure(head, tail, ast::ROOT_MODULE_NAME.to_owned())
    }

    pub fn as_builtin_module_member(&self) -> Self {
        let Self { head, tail } = self;
        self.clone()
            .prefigure(head, tail, ast::BUILTIN_MODULE_NAME.to_owned())
    }

    pub fn in_module(&self, module: &IdentifierPath) -> Self {
        IdentifierPath {
            head: module.head.clone(),
            tail: {
                let mut new_tail = module.tail.to_vec();
                new_tail.push(self.head.clone());
                new_tail.extend_from_slice(&self.tail);

                new_tail
            },
        }
    }

    fn prefigure(self, head: &str, tail: &Vec<String>, head1: String) -> IdentifierPath {
        Self {
            head: head1,
            tail: {
                let mut new_tail = Vec::with_capacity(1 + tail.capacity());
                new_tail.push(head.to_owned());
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
#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
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
pub enum Fault {
    UnexpectedOverflow,
    UnexpectedUnderflow,
    Expected {
        expected: TokenKind,
        found: TokenKind,
        position: SourceLocation,
    },
    ExpectedParameterList,
    ExpectedIdentifier(Token),
    ExpectedTypeConstructor,
}

type Result<A> = result::Result<A, Fault>;

#[derive(Debug)]
struct TraceLogEntry<'a> {
    step: String,
    remains: &'a [Token],
}

thread_local! {
    static STACK_DEPTH: Cell<usize> = const { Cell::new(0) };
}

pub struct TraceGuard;

impl TraceGuard {
    fn enter() -> Self {
        STACK_DEPTH.with(|d| d.set(d.get() + 1));
        TraceGuard
    }
}

impl Drop for TraceGuard {
    fn drop(&mut self) {
        STACK_DEPTH.with(|d| d.set(d.get() - 1));
    }
}

fn stack_depth() -> usize {
    STACK_DEPTH.with(|d| d.get())
}

#[derive(Debug, Default)]
pub struct Parser<'a> {
    remains: &'a [Token],
    offset: usize,
}

impl<'a> Parser<'a> {
    pub fn from_tokens(remains: &'a [Token]) -> Self {
        Self { remains, offset: 0 }
    }

    fn remains(&self) -> &'a [Token] {
        &self.remains[self.offset..]
    }

    fn advance(&mut self, by: usize) {
        self.offset += by;
    }

    fn trace(&mut self) -> TraceGuard {
        let depth = stack_depth();

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
                remains: self.remains(),
            };
            println!(
                "{:indent$}{}{:<pad$}{}",
                "",
                e.step,
                "",
                self.remains()
                    .iter()
                    .map(|t| t.to_string())
                    .take(8)
                    .collect::<Vec<_>>()
                    .join(" "),
                indent = depth * 2,
                pad = 90 - (depth * 2 + e.step.len())
            );
        } else {
            println!("Unknown caller.")
        }

        TraceGuard::enter()
    }

    fn peek(&self) -> Result<&Token> {
        self.remains().first().ok_or(Fault::UnexpectedOverflow)
    }

    fn expect(&mut self, expected: TokenKind) -> Result<&Token> {
        match self.remains() {
            [token, ..] if token.kind == expected => {
                self.advance(1);
                Ok(token)
            }

            [token, ..] => Err(Fault::Expected {
                expected,
                found: token.kind.clone(),
                position: token.position,
            }),

            _ => Err(Fault::UnexpectedUnderflow),
        }
    }

    fn identifier(&mut self) -> Result<(SourceLocation, String)> {
        let token = self.peek()?;
        if let Token {
            kind: TokenKind::Identifier(id),
            position,
        } = token
        {
            let retval = (*position, id.to_owned());
            self.consume()?;
            Ok(retval)
        } else {
            Err(Fault::ExpectedIdentifier(token.clone()))
        }
    }

    fn consume(&mut self) -> Result<&Token> {
        if let Some(the) = self.remains().first() {
            self.advance(1);
            Ok(the)
        } else {
            Err(Fault::UnexpectedOverflow)
        }
    }

    fn unconsume(&mut self) -> Result<()> {
        if self.offset > 0 {
            self.offset -= 1;
            Ok(())
        } else {
            Err(Fault::UnexpectedUnderflow)
        }
    }

    fn _consume_if<P>(&mut self, p: P) -> Result<&Token>
    where
        P: FnMut(&&Token) -> bool,
    {
        if let Some(the) = self.remains().first().filter(p) {
            self.advance(1);
            Ok(the)
        } else {
            Err(Fault::UnexpectedOverflow)
        }
    }

    pub fn parse_compilation_unit(&mut self) -> Result<CompilationUnit<ParseInfo>> {
        let _t = self.trace();

        let mut decls = vec![self.parse_declaration()?];

        while self.has_declaration_prefix() {
            if self.peek()?.is_newline() {
                self.advance(1);
            }

            if !self.peek()?.is_end() {
                let decl = self.parse_declaration()?;
                decls.push(decl);
            } else {
                break;
            }
        }

        Ok(CompilationUnit::from_declarations(decls))
    }

    fn has_declaration_prefix(&self) -> bool {
        matches!(
            self.remains(),
            [
                Token {
                    kind: TokenKind::Identifier(..),
                    ..
                },
                Token {
                    kind: TokenKind::Assign | TokenKind::TypeAssign | TokenKind::TypeAscribe,
                    ..
                },
                ..
            ] | [
                Token {
                    kind: TokenKind::Layout(Layout::Newline),
                    ..
                },
                ..
            ]
        )
    }

    fn parse_declaration(&mut self) -> Result<Declaration<ParseInfo>> {
        let _t = self.trace();

        match self.remains() {
            [
                Token {
                    kind: TokenKind::Identifier(name),
                    position,
                },
                Token {
                    kind: TokenKind::Assign,
                    ..
                },
                ..,
            ] => {
                // <id> <:=>
                self.advance(2);

                let own_name = IdentifierPath::new(name);

                Ok(Declaration::Value(
                    ParseInfo::from_position(*position),
                    ValueDeclaration {
                        name: Identifier::from_str(name),
                        declarator: self.parse_value_declarator(None, own_name)?,
                    },
                ))
            }

            [
                Token {
                    kind: TokenKind::Identifier(name),
                    position,
                },
                Token {
                    kind: TokenKind::TypeAscribe,
                    ..
                },
                ..,
            ] => {
                // <id> <::>
                self.advance(2);

                let type_signature = self.parse_type_signature().map(Some)?;

                // <:=>
                self.advance(1);

                let own_name = IdentifierPath::new(name);

                Ok(Declaration::Value(
                    ParseInfo::from_position(*position),
                    ValueDeclaration {
                        name: Identifier::from_str(name),
                        declarator: self.parse_value_declarator(type_signature, own_name)?,
                    },
                ))
            }

            [
                Token {
                    kind: TokenKind::Identifier(name),
                    position,
                },
                Token {
                    kind: TokenKind::TypeAssign,
                    ..
                },
                ..,
            ] => {
                // <id> <::=>
                self.advance(2);

                Ok(Declaration::Type(
                    ParseInfo::from_position(*position),
                    TypeDeclaration {
                        name: Identifier::from_str(name),
                        // Move this to TypeDeclarator
                        type_parameters: self.parse_forall_clause()?,
                        declarator: self.parse_block(|parser| parser.parse_type_declarator())?,
                    },
                ))
            }

            otherwise => panic!("{otherwise:?}"),
        }
    }

    // preceed with parse_block, but it has to lookahead to see
    // that there is a forall in there, or it will erroneously
    // consume the type body block tokens.
    fn parse_forall_clause(&mut self) -> Result<Vec<Identifier>> {
        let _t = self.trace();

        if self.peek()?.is_keyword(Keyword::Forall) {
            // forall
            self.advance(1);

            let mut params = vec![];
            while self.peek()?.is_identifier() {
                params.push(self.identifier().map(|(_, id)| Identifier(id))?);
            }

            if params.is_empty() {
                Err(Fault::ExpectedIdentifier(self.peek()?.clone()))?;
            }

            self.expect(TokenKind::Period)?;

            Ok(params)
        } else {
            Ok(vec![])
        }
    }

    fn parse_value_declarator(
        &mut self,
        type_signature: Option<TypeSignature>,
        own_name: IdentifierPath,
    ) -> Result<ValueDeclarator<ParseInfo>> {
        let _t = self.trace();

        Ok(ValueDeclarator {
            type_signature,
            body: self
                .parse_block(|parser| parser.parse_expression(0))
                .map(|lambda| {
                    if let Expr::Lambda(pi, lambda) = lambda {
                        Expr::RecursiveLambda(
                            pi,
                            SelfReferential {
                                own_name,
                                lambda: lambda.into(),
                            },
                        )
                    } else {
                        lambda
                    }
                })?,
        })
    }

    fn parse_type_declarator(&mut self) -> Result<TypeDeclarator<ParseInfo>> {
        let _t = self.trace();

        match self.remains() {
            [t, ..] if t.kind == TokenKind::LeftBrace => {
                self.parse_block(|parser| {
                    // The `{`
                    let info = ParseInfo::from_position(*parser.consume()?.location());
                    parser
                        .parse_record_type_decl()
                        .map(|decl| TypeDeclarator::Record(info, decl))
                })
            }

            [t, ..] if t.is_identifier() => self.parse_block(|parser| {
                let info = ParseInfo::from_position(*parser.peek()?.location());
                parser
                    .parse_coproduct()
                    .map(|decl| TypeDeclarator::Coproduct(info, decl))
            }),

            otherwise => panic!("{otherwise:?}"),
        }
    }

    // This is incredibly noisy for something very simple
    fn parse_record_type_decl(&mut self) -> Result<RecordDeclarator<ParseInfo>> {
        let _t = self.trace();

        self.strip_layout()?;

        let column = *self.peek()?.location();
        let mut fields = vec![self.parse_field_decl()?];

        while self.is_record_field_separator(column)? {
            self.consume()?;
            fields.push(self.parse_field_decl()?);
        }

        self.strip_layout()?;

        self.expect(TokenKind::RightBrace)?;

        Ok(RecordDeclarator { fields })
    }

    fn is_record_field_separator(&mut self, block: SourceLocation) -> Result<bool> {
        let t = self.peek()?;
        Ok(
            ((t.is_newline() || t.is_indent()) && t.location().is_same_block(&block))
                || t.kind == TokenKind::Semicolon,
        )
    }

    fn strip_layout(&mut self) -> Result<()> {
        let _t = self.trace();

        while self.peek()?.is_layout() {
            self.consume()?;
        }

        Ok(())
    }

    fn parse_field_decl(&mut self) -> Result<FieldDeclarator<ParseInfo>> {
        let _t = self.trace();

        let (_, label) = self.identifier()?;
        self.expect(TokenKind::TypeAscribe)?;
        let type_signature = self.parse_type_expression()?;
        Ok(FieldDeclarator {
            // It could really keep this Identifier instead of cloning it
            name: Identifier::from_str(&label),
            type_signature,
        })
    }

    fn parse_type_expression(&mut self) -> Result<TypeExpression> {
        let _t = self.trace();

        let prefix = self.parse_type_expr_prefix()?;
        self.parse_type_expr_infix(prefix)
    }

    fn parse_type_expr_prefix(&mut self) -> Result<TypeExpression> {
        let _t = self.trace();

        match self.remains() {
            [
                Token {
                    kind: TokenKind::Identifier(id),
                    position,
                },
                ..,
            ] => {
                self.advance(1);
                Ok(self.parse_simple_type_expr_term(id, position))
            }

            [
                Token {
                    kind: TokenKind::LeftParen,
                    ..
                },
                ..,
            ] => {
                self.advance(1);
                let prefix = self.parse_type_expression();
                self.expect(TokenKind::RightParen)?;
                prefix
            }

            // parens
            otherwise => panic!("{otherwise:?}"),
        }
    }

    fn parse_simple_type_expr_term(
        &mut self,
        id: &String,
        position: &SourceLocation,
    ) -> ast::TypeExpression<ParseInfo, IdentifierPath> {
        let _t = self.trace();

        let parse_info = ParseInfo::from_position(*position);
        if is_lowercase(id) {
            TypeExpression::Parameter(parse_info, Identifier::from_str(id))
        } else {
            TypeExpression::Constructor(parse_info, IdentifierPath::new(id))
        }
    }

    fn parse_type_expr_infix(&mut self, lhs: TypeExpression) -> Result<TypeExpression> {
        let _t = self.trace();

        match self.remains() {
            [
                Token {
                    kind: TokenKind::Identifier(id),
                    position,
                },
                ..,
            ] => {
                if lhs.is_applicable() {
                    self.advance(1);
                    let rhs = self.parse_simple_type_expr_term(id, position);
                    self.parse_type_expr_infix(TypeExpression::Apply(
                        ParseInfo::from_position(*position),
                        ApplyTypeExpr {
                            function: lhs.into(),
                            argument: rhs.into(),
                            phase: PhantomData,
                        },
                    ))
                } else {
                    Err(Fault::ExpectedTypeConstructor)
                }
            }

            [
                Token {
                    kind: TokenKind::Arrow,
                    position,
                },
                ..,
            ] => {
                self.advance(1);
                let rhs = self.parse_type_expression()?;
                self.parse_type_expr_infix(TypeExpression::Arrow(
                    ParseInfo::from_position(*position),
                    ArrowTypeExpr {
                        domain: lhs.into(),
                        codomain: rhs.into(),
                    },
                ))
            }

            [
                Token {
                    kind: TokenKind::RightParen,
                    ..
                },
                ..,
            ] => {
                //                self.advance(1);
                Ok(lhs)
            }

            _otherwise => Ok(lhs),
        }
    }

    fn parse_block<F, A>(&mut self, parse_body: F) -> Result<A>
    where
        F: FnOnce(&mut Parser<'a>) -> Result<A>,
    {
        let _t = self.trace();

        if self.peek()?.is_indent() {
            self.consume()?;
            let body = parse_body(self)?;
            // This does not interact well with sequences because parse_sequence
            // does not see a sequence separator anymore after this
            //            println!("parse_block: delete dedent");
            self.expect(TokenKind::Layout(Layout::Dedent))?;
            Ok(body)
        } else {
            parse_body(self)
        }
    }

    fn parse_local_binding(&mut self) -> Result<Expr> {
        let _t = self.trace();

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

    fn parse_record(&mut self) -> Result<Expr> {
        let _t = self.trace();

        // the `{`
        self.advance(1);
        self.strip_layout()?;
        let column = *self.peek()?.location();

        let mut fields = vec![self.parse_field_init()?];

        while self.is_record_field_separator(column)? {
            self.consume()?;
            fields.push(self.parse_field_init()?);
        }

        self.strip_layout()?;

        self.expect(TokenKind::RightBrace)?;

        Ok(Expr::Record(
            ParseInfo::from_position(column),
            Record::from_fields(&fields),
        ))
    }

    fn parse_field_init(&mut self) -> Result<(Identifier, Tree<ParseInfo, IdentifierPath>)> {
        let _t = self.trace();

        let (_, label) = self.identifier()?;
        self.expect(TokenKind::Colon)?;

        let expr = self.parse_expression(0)?;

        Ok((Identifier::from_str(&label), expr.into()))
    }

    fn parse_lambda(&mut self) -> Result<Expr> {
        let _t = self.trace();

        self.expect(TokenKind::Keyword(Keyword::Lambda))?;

        let mut params = vec![];
        while self.peek()?.is_identifier() {
            params.push(self.identifier()?);
        }

        if params.is_empty() {
            Err(Fault::ExpectedIdentifier(self.peek()?.clone()))?;
        }

        self.expect(TokenKind::Period)?;

        let body = self.parse_block(|parser| parser.parse_expression(0))?;

        let lambda = params.into_iter().rfold(body, |body, (pos, param)| {
            Expr::Lambda(
                ParseInfo::from_position(pos),
                Lambda {
                    parameter: IdentifierPath::new(&param),
                    body: body.into(),
                },
            )
        });

        Ok(lambda)
    }

    fn parse_sequence(&mut self) -> Result<Expr> {
        let _t = self.trace();

        let prefix = self.parse_expression(0)?;

        println!(
            "parse_sequence: prefix `{prefix}` at {}",
            prefix.parse_info().location
        );

        match self.remains() {
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
        let _t = self.trace();

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
        let _t = self.trace();

        let prefix = self.parse_expr_prefix()?;
        self.parse_expr_infix(prefix, precedence)
    }

    fn parse_expr_prefix(&mut self) -> Result<Expr> {
        let _t = self.trace();

        match self.remains() {
            [
                Token {
                    kind: TokenKind::Literal(lit),
                    position,
                },
                ..,
            ] => {
                self.advance(1);
                self.parse_literal(lit, position)
            }

            [
                Token {
                    kind: TokenKind::Identifier(id),
                    position,
                },
                ..,
            ] => {
                self.advance(1);
                self.parse_variable(id, position)
            }

            [
                Token {
                    kind: TokenKind::LeftBrace,
                    ..
                },
                ..,
            ] => self.parse_record(),

            [t, ..] if t.is_keyword(Keyword::Lambda) => self.parse_lambda(),

            [t, ..] if t.is_keyword(Keyword::Let) => self.parse_local_binding(),

            [t, ..] if t.is_keyword(Keyword::Deconstruct) => self.parse_deconstruct_into(),

            [
                Token {
                    kind: TokenKind::LeftParen,
                    ..
                },
                ..,
            ] => {
                // '('
                self.advance(1);
                let expr = self.parse_expression(0);
                self.expect(TokenKind::RightParen)?;
                expr
            }

            otherwise => panic!("{otherwise:?}"),
        }
    }

    fn is_expr_prefix(kind: &TokenKind) -> bool {
        !matches!(
            kind,
            TokenKind::Layout(Layout::Dedent | Layout::Indent | Layout::Newline)
                | TokenKind::RightBrace
                | TokenKind::Pipe
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
        let _t = self.trace();

        let terminals = [
            TokenKind::RightParen,
            TokenKind::Semicolon,
            TokenKind::Pipe,
            TokenKind::Layout(Layout::Dedent),
            TokenKind::Keyword(Keyword::Let),
            TokenKind::Keyword(Keyword::In),
            TokenKind::Keyword(Keyword::Into),
            TokenKind::End,
        ];

        let is_terminal = |t| terminals.contains(t);

        match self.remains() {
            [t, ..] if is_terminal(&t.kind) => Ok(lhs),

            [t, u, ..] if t.is_layout() && is_terminal(&u.kind) => Ok(lhs),

            [t, ..] if Operator::is_defined(&t.kind) => {
                let operator = Operator::try_from(&t.kind).expect("msg");
                // the operator
                self.advance(1);
                self.parse_operator(lhs, operator, *t.location(), context_precedence)
            }

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
                    && u.location().is_descendant_of(lhs.position()) =>
            {
                //                println!(
                //                    "Calling parse_juxtaposed(1); lhs pos {}",
                //                    lhs.parse_info().location
                //                );
                self.advance(1); //the indent
                self.parse_juxtaposed(lhs, context_precedence)
            }

            // f x
            [t, u, ..]
                if Self::is_expr_prefix(&t.kind)
                    && !matches!(u.kind, TokenKind::Assign | TokenKind::TypeAscribe)
                    && Operator::Juxtaposition.precedence() > context_precedence =>
            {
                println!("Calling parse_juxtaposed(2) with u {u:?}");
                self.parse_juxtaposed(lhs, context_precedence)
            }

            _ => Ok(lhs),
        }
    }

    fn parse_juxtaposed(&mut self, lhs: Expr, context_precedence: usize) -> Result<Expr> {
        let _t = self.trace();

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
            ParseInfo::from_position(*position),
            literal.clone().into(),
        ))
    }

    fn parse_variable(&mut self, id: &str, position: &SourceLocation) -> Result<Expr> {
        Ok(Expr::Variable(
            ParseInfo::from_position(*position),
            IdentifierPath::new(id),
        ))
    }

    fn parse_operator(
        &mut self,
        lhs: Expr,
        operator: Operator,
        operator_position: SourceLocation,
        context_precedence: usize,
    ) -> Result<Expr> {
        let _t = self.trace();

        let computed_precedence = if operator.is_right_associative() {
            operator.precedence() - 1
        } else {
            operator.precedence()
        };

        if computed_precedence > context_precedence {
            match operator {
                Operator::Select => {
                    let lhs = self.parse_select_operator(lhs)?;
                    self.parse_expr_infix(lhs, context_precedence)
                }

                Operator::Tuple => {
                    self.parse_tuple_expression(lhs, operator_position, context_precedence)
                }

                _ => self.parse_operator_default(
                    lhs,
                    operator,
                    operator_position,
                    context_precedence,
                    computed_precedence,
                ),
            }
        } else {
            // Symmetrical with the consume call before entering parse_operator.
            // I would like these two to be in the same spot
            self.unconsume()?;
            Ok(lhs)
        }
    }

    fn parse_tuple_expression(
        &mut self,
        lhs: Expr,
        operator_position: SourceLocation,
        context_precedence: usize,
    ) -> Result<Expr> {
        let rhs = self.parse_expression(context_precedence)?;
        self.parse_expr_infix(
            Expr::Tuple(
                ParseInfo::from_position(operator_position),
                Tuple {
                    elements: vec![lhs.into(), rhs.into()],
                },
            ),
            context_precedence,
        )
    }

    fn parse_select_operator(&mut self, lhs: Expr) -> Result<Expr> {
        let _t = self.trace();

        if let Expr::Variable(pi, id) = &lhs
            && !matches!(self.peek()?.kind, TokenKind::Literal(..))
        {
            self.parse_identifier_path(*pi, id.clone())
        } else {
            self.parse_projection(lhs)
        }
    }

    fn parse_identifier_path(&mut self, pi: ParseInfo, lhs: IdentifierPath) -> Result<Expr> {
        let _t = self.trace();

        let (_, rhs) = self.identifier()?;
        Ok(Expr::Variable(pi, lhs.with_suffix(rhs.as_str())))
    }

    fn parse_projection(&mut self, lhs: Expr) -> Result<Expr> {
        let _t = self.trace();

        let rhs = match self.remains() {
            [
                Token {
                    kind: TokenKind::Identifier(id),
                    ..
                },
                ..,
            ] => ast::ProductElement::Name(Identifier::from_str(id)),

            [
                Token {
                    kind: TokenKind::Literal(Literal::Integer(id)),
                    ..
                },
                ..,
            ] => ast::ProductElement::Ordinal(*id as usize),

            otherwise => panic!("{otherwise:?}"),
        };

        // The Id or Int literal
        self.advance(1);

        let parse_info = *lhs.parse_info();
        let projection = Projection {
            base: lhs.into(),
            select: rhs,
        };

        Ok(Expr::Project(parse_info, projection))
    }

    fn parse_operator_default(
        &mut self,
        lhs: Expr,
        operator: Operator,
        operator_position: SourceLocation,
        context_precedence: usize,
        computed_precedence: usize,
    ) -> Result<Expr> {
        let _t = self.trace();

        let apply_lhs = Expr::Apply(
            ParseInfo::from_position(*lhs.position()),
            Apply {
                function: Expr::Variable(
                    ParseInfo::from_position(operator_position),
                    IdentifierPath::new(operator.name()),
                )
                .into(),
                argument: lhs.into(),
            },
        );

        let rhs = self.parse_expression(computed_precedence)?;
        self.parse_expr_infix(
            Expr::Apply(
                ParseInfo::from_position(*rhs.position()),
                Apply {
                    function: apply_lhs.into(),
                    argument: rhs.into(),
                },
            ),
            context_precedence,
        )
    }

    fn parse_type_signature(&mut self) -> Result<TypeSignature> {
        let _t = self.trace();

        let quantifiers = self.parse_forall_clause()?;
        let body = self.parse_type_expression()?;

        Ok(TypeSignature {
            universal_quantifiers: quantifiers,
            body,
            phase: PhantomData,
        })
    }

    fn parse_coproduct(&mut self) -> Result<CoproductDeclarator<ParseInfo>> {
        let _t = self.trace();

        let mut constructors = vec![self.parse_coproduct_constructor()?];

        while self.peek()?.kind == TokenKind::Pipe {
            // |
            self.advance(1);
            constructors.push(self.parse_coproduct_constructor()?);
        }

        Ok(CoproductDeclarator { constructors })
    }

    fn parse_coproduct_constructor(&mut self) -> Result<CoproductConstructor<ParseInfo>> {
        let _t = self.trace();

        let (_, id) = self.identifier()?;

        let mut signature = vec![];

        while matches!(
            self.peek()?.kind,
            TokenKind::Identifier(..) | TokenKind::LeftParen
        ) {
            if self.peek()?.is_identifier() {
                let (pos, id) = self.identifier()?;
                let pi = ParseInfo::from_position(pos);
                signature.push(if is_lowercase(&id) {
                    TypeExpression::Parameter(pi, Identifier::from_str(&id))
                } else {
                    TypeExpression::Constructor(pi, IdentifierPath::new(&id))
                });
            } else {
                signature.push(self.parse_type_expression()?);
            }
        }

        Ok(CoproductConstructor {
            name: Identifier::from_str(&id),
            signature,
        })
    }

    fn parse_deconstruct_into(&mut self) -> Result<Expr> {
        let _t = self.trace();
        // deconstruct
        let _deconstruct = *self.consume()?.location();

        let scrutinee = self.parse_block(|parser| parser.parse_expression(0))?;

        self.expect(TokenKind::Keyword(Keyword::Into))?;

        // Annoying
        if self.peek()?.is_indent() {
            self.advance(1);
        }

        let mut match_clauses = vec![self.parse_match_clause()?];
        println!("parse_deconstruct_into: parsed match clause");

        // Annoying
        if self.peek()?.is_dedent() {
            self.advance(1);
        }

        let is_match_clause_separator = |remains: &[Token]| match remains {
            [
                Token {
                    kind: TokenKind::Pipe,
                    ..
                },
                ..,
            ] => Some(1),

            [
                t,
                Token {
                    kind: TokenKind::Pipe,
                    ..
                },
                ..,
            ] if t.is_layout() => Some(2),

            _ => None,
        };

        while let Some(separator) = is_match_clause_separator(self.remains()) {
            // |
            self.advance(separator);
            match_clauses.push(self.parse_match_clause()?);
        }

        Ok(Expr::Deconstruct(
            *scrutinee.parse_info(),
            Deconstruct {
                scrutinee: scrutinee.into(),
                match_clauses,
            },
        ))
    }

    fn parse_match_clause(&mut self) -> Result<MatchClause> {
        let _t = self.trace();

        let pattern = self.parse_pattern()?;

        self.expect(TokenKind::Arrow)?;
        let consequent = self.parse_expression(0)?;
        Ok(MatchClause {
            pattern,
            consequent: consequent.into(),
        })
    }

    fn parse_pattern(&mut self) -> Result<Pattern> {
        let _t = self.trace();

        let prefix = self.parse_pattern_prefix()?;
        self.parse_pattern_infix(prefix)
    }

    fn parse_pattern_prefix(&mut self) -> Result<Pattern> {
        let _t = self.trace();

        // 1. Coproduct: Constructor pat1 pat2 pat3
        // 2. Record: { field1; field2: pat1 }
        // 3. Tuple: patt1, patt2, patt3
        // 4. Literal: "foo" 1
        // 5. Bind: pat1
        match self.remains() {
            [
                Token {
                    kind: TokenKind::Identifier(id),
                    ..
                },
                ..,
            ] if is_capital_case(id) => self.parse_constructor_pattern(),

            [
                Token {
                    kind: TokenKind::Identifier(..),
                    ..
                },
                ..,
            ] => self.parse_pattern_binder(),

            [
                Token {
                    kind: TokenKind::LeftBrace,
                    ..
                },
                ..,
            ] => self.parse_struct_pattern(),

            [
                Token {
                    kind: TokenKind::Literal(literal),
                    position,
                },
                ..,
            ] => self.parse_literal_pattern(*position, literal),

            otherwise => panic!("{otherwise:?}"),
        }
    }

    fn parse_pattern_infix(&mut self, lhs: Pattern) -> Result<Pattern> {
        let _t = self.trace();

        match self.remains() {
            [t, ..] if t.kind == TokenKind::Comma => {
                // ,
                self.advance(1);
                let rhs = self.parse_pattern()?;
                self.parse_pattern_infix(Pattern::Tuple(
                    ParseInfo::from_position(*t.location()),
                    TuplePattern {
                        elements: vec![lhs, rhs],
                    },
                ))
            }

            _otherwise => Ok(lhs),
        }
    }

    fn parse_constructor_pattern(&mut self) -> Result<Pattern> {
        let _t = self.trace();

        // There are nullary constructors
        let (pos, id) = self.identifier()?;
        let mut arguments = vec![];

        while !matches!(
            self.peek()?.kind,
            TokenKind::Arrow | TokenKind::Comma | TokenKind::RightBrace
        ) {
            arguments.push(self.parse_pattern_prefix()?);
        }

        Ok(Pattern::Coproduct(
            ParseInfo::from_position(pos),
            ConstructorPattern {
                constructor: IdentifierPath::new(&id),
                arguments,
            },
        ))
    }

    fn parse_literal_pattern(
        &mut self,
        position: SourceLocation,
        literal: &Literal,
    ) -> Result<Pattern> {
        let _t = self.trace();

        // the literal
        self.advance(1);
        Ok(Pattern::Literally(
            ParseInfo::from_position(position),
            literal.clone().into(),
        ))
    }

    fn parse_pattern_binder(&mut self) -> Result<Pattern> {
        let _t = self.trace();

        let (pos, id) = self.identifier()?;
        Ok(Pattern::Bind(
            ParseInfo::from_position(pos),
            IdentifierPath::new(&id),
        ))
    }

    fn parse_struct_pattern(&mut self) -> Result<Pattern> {
        let _t = self.trace();

        // {
        let brace_location = *self.consume()?.location();

        let mut fields = vec![self.parse_struct_pattern_field()?];

        while matches!(self.peek()?.kind, TokenKind::Semicolon) {
            // ;
            self.advance(1);
            fields.push(self.parse_struct_pattern_field()?);
        }

        self.expect(TokenKind::RightBrace)?;

        fields.sort_by(|t, u| t.0.cmp(&u.0));

        Ok(Pattern::Struct(
            ParseInfo::from_position(brace_location),
            StructPattern { fields },
        ))
    }

    fn parse_struct_pattern_field(&mut self) -> Result<(Identifier, Pattern)> {
        let _t = self.trace();

        let (_pos, label) = self.identifier()?;
        self.expect(TokenKind::Colon)?;
        let pattern = self.parse_pattern()?;
        Ok((Identifier::from_str(&label), pattern))
    }
}

fn is_lowercase(id: &str) -> bool {
    id.chars().all(char::is_lowercase)
}

fn is_capital_case(id: &str) -> bool {
    id.chars().nth(0).is_some_and(|c| c.is_uppercase())
}

impl Pattern {
    pub fn normalize(&self) -> Pattern {
        match self {
            Self::Coproduct(
                pi,
                ConstructorPattern {
                    constructor,
                    arguments,
                },
            ) => Self::Coproduct(
                *pi,
                ConstructorPattern {
                    constructor: constructor.clone(),
                    arguments: arguments.iter().map(|p| p.normalize()).collect(),
                },
            ),

            Self::Tuple(pi, TuplePattern { elements }) => Self::Tuple(
                *pi,
                TuplePattern {
                    elements: unspine_tuple_pattern(elements.clone()),
                },
            ),

            Self::Struct(pi, StructPattern { fields }) => Self::Struct(
                *pi,
                StructPattern {
                    fields: fields
                        .iter()
                        .map(|(field, pattern)| (field.clone(), pattern.normalize()))
                        .collect(),
                },
            ),

            Self::Literally(..) | Self::Bind(..) => self.clone(),
        }
    }
}

fn unspine_tuple_pattern(elements: Vec<Pattern>) -> Vec<Pattern> {
    elements
        .into_iter()
        .flat_map(|p| match p {
            Pattern::Tuple(_, pattern) => pattern.elements,
            atom => vec![atom],
        })
        .collect()
}

impl TypeExpression {
    fn is_applicable(&self) -> bool {
        matches!(self, Self::Constructor(..) | Self::Apply(..))
    }
}

impl From<Literal> for ast::Literal {
    fn from(value: Literal) -> Self {
        match value {
            Literal::Integer(x) => ast::Literal::Int(x),
            Literal::Text(x) => ast::Literal::Text(x),
            Literal::Bool(x) => ast::Literal::Bool(x),
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

//impl<'a> fmt::Display for TraceLogEntry<'a> {
//    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//        let Self { step, remains } = self;
//        write!(
//            f,
//            "{} -->{:<pad$}",
//            step,
//            remains
//                .iter()
//                .map(|t| t.to_string())
//                .take(10)
//                .collect::<Vec<_>>()
//                .join(", ")
//            pad = 40
//        )
//    }
//}

#[cfg(test)]
mod tests {
    use crate::{lexer::LexicalAnalyzer, parser::Parser};

    #[test]
    fn type_expressions() {
        let mut lexer = LexicalAnalyzer::default();
        let input = include_str!("../examples/type-expression.txt");

        let tokens = lexer.tokenize(&input.chars().collect::<Vec<_>>());

        for t in tokens {
            println!("{t}")
        }

        let mut p = Parser::from_tokens(tokens);
        let x = p.parse_type_expression().unwrap();
        println!("{x}")
    }

    #[test]
    fn parsington() {
        let mut lexer = LexicalAnalyzer::default();
        let input = include_str!("../examples/4.txt");

        let tokens = lexer.tokenize(&input.chars().collect::<Vec<_>>());

        for t in tokens {
            println!("{t}")
        }

        let mut p = Parser::from_tokens(tokens);
        let x = p.parse_compilation_unit().unwrap();
        println!("{x}")
    }
}
