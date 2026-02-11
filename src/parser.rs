use std::{
    cell::Cell,
    fmt,
    hash::{DefaultHasher, Hash, Hasher},
    marker::PhantomData,
    result, vec,
};

use backtrace::Backtrace;
use thiserror::Error;

use crate::{
    ast::{
        self, ApplyTypeExpr, ArrowTypeExpr, ConstraintDeclaration, CoproductConstructor,
        Declaration, FieldDeclarator, ModuleDeclaration, ModuleDeclarator, Tree, TupleTypeExpr,
        TypeDeclaration, TypeDeclarator, UseDeclaration, ValueDeclaration, ValueDeclarator,
        WitnessDeclaration, namer::QualifiedName,
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
pub type IfThenElse = ast::IfThenElse<ParseInfo, IdentifierPath>;
pub type Interpolate = ast::Interpolate<ParseInfo, IdentifierPath>;
pub type TypeAscription = ast::TypeAscription<ParseInfo, IdentifierPath>;
pub type RecordDeclarator = ast::RecordDeclarator<ParseInfo>;
pub type CoproductDeclarator = ast::CoproductDeclarator<ParseInfo>;

pub type Segment = ast::Sequence<ParseInfo, IdentifierPath>;
pub type Pattern = ast::pattern::Pattern<ParseInfo, IdentifierPath>;
pub type MatchClause = ast::pattern::MatchClause<ParseInfo, IdentifierPath>;

pub type ConstructorPattern = ast::pattern::ConstructorPattern<ParseInfo, IdentifierPath>;
pub type TuplePattern = ast::pattern::TuplePattern<ParseInfo, IdentifierPath>;
pub type StructPattern = ast::pattern::StructPattern<ParseInfo, IdentifierPath>;
pub type TypeExpression = ast::TypeExpression<ParseInfo, IdentifierPath>;
pub type TypeSignature = ast::TypeSignature<ParseInfo, IdentifierPath>;

pub type ConstraintExpression = ast::ConstraintExpression<ParseInfo, IdentifierPath>;

impl<Id> ast::Expr<ParseInfo, Id> {
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

// Rewrite to be in terms of Identifier instead, that way
// we get ParseInfo everywhere
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

    pub fn try_into_parent(mut self) -> Option<Self> {
        if self.tail.pop().is_some() {
            Some(self)
        } else {
            None
        }
    }

    pub fn last(&self) -> &str {
        self.tail.last().unwrap_or_else(|| &self.head)
    }

    pub fn in_module(&self, module: &IdentifierPath) -> Self {
        if self.head != module.head {
            IdentifierPath {
                head: module.head.clone(),
                tail: {
                    let mut new_tail = module.tail.to_vec();
                    new_tail.push(self.head.clone());
                    new_tail.extend_from_slice(&self.tail);

                    new_tail
                },
            }
        } else {
            self.clone()
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
            Some(Identifier::from_str(&self.head))
        } else {
            None
        }
    }

    pub fn element(&self, ix: usize) -> Option<&str> {
        if ix == 0 {
            Some(&self.head)
        } else {
            self.tail.get(ix - 1).map(|s| s.as_str())
        }
    }

    pub fn len(&self) -> usize {
        self.tail.len() + 1
    }
}

// What about ParseInfo?
#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub struct Identifier {
    image: String,
}

impl Identifier {
    pub fn from_str(id: &str) -> Self {
        Self {
            image: id.to_owned(),
        }
    }

    pub fn as_str(&self) -> &str {
        &self.image
    }
}

#[derive(Debug, Error)]
pub enum ParseError {
    #[error("unexpected overflow")]
    UnexpectedOverflow,

    #[error("unexpected underflow")]
    UnexpectedUnderflow,

    #[error("{position}: expected {expected}\nfound: {found}")]
    Expected {
        expected: TokenKind,
        found: TokenKind,
        position: SourceLocation,
    },

    #[error("expected a parameter list")]
    ExpectedParameterList,

    #[error("expected an identifier\nfound: {0}")]
    ExpectedIdentifier(Token),

    #[error("expected a type constructor (Capitalized name.)")]
    ExpectedTypeConstructor,
}

type Result<A> = result::Result<A, ParseError>;

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

impl Interpolate {
    pub fn begin(pi: ParseInfo, prelude: Literal) -> Self {
        Self(vec![ast::Segment::Literal(pi, prelude.into())])
    }

    pub fn expression(&mut self, expr: Expr) {
        self.0.push(ast::Segment::Expression(expr.into()));
    }

    pub fn literal(&mut self, pi: ParseInfo, literal: Literal) {
        self.0.push(ast::Segment::Literal(pi, literal.into()));
    }
}

enum TypeExprOperator {
    Apply,
    Arrow,
    Tuple,
}

impl TypeExprOperator {
    fn precedence(&self) -> usize {
        match self {
            Self::Apply => 3,
            Self::Arrow => 2,
            Self::Tuple => 1,
        }
    }

    fn is_right_associative(&self) -> bool {
        matches!(self, Self::Arrow)
    }
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
        const REMAINS_COL: usize = 120;

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
            let parts = caller_name.split("::").collect::<Vec<_>>();
            let step = parts
                .get(parts.len().saturating_sub(2))
                .unwrap_or(&caller_name.as_str())
                .to_string();

            let remains = self
                .remains()
                .iter()
                .take(8)
                .map(|t| t.to_string())
                .collect::<Vec<_>>()
                .join(" ");

            let remains = remains.chars().collect::<Vec<_>>();

            let remains = if remains.len() > REMAINS_COL {
                &remains[..REMAINS_COL]
            } else {
                &remains
            };

            let indent = depth * 2;

            println!(
                "{:<width$}{}{}",
                remains.into_iter().collect::<String>(),
                " ".repeat(indent),
                step,
                width = REMAINS_COL
            );
        } else {
            println!("Unknown caller.");
        }

        TraceGuard::enter()
    }

    fn peek(&self) -> Result<&Token> {
        self.remains().first().ok_or(ParseError::UnexpectedOverflow)
    }

    fn expect(&mut self, expected: TokenKind) -> Result<&Token> {
        match self.remains() {
            [token, ..] if token.kind == expected => {
                self.advance(1);
                Ok(token)
            }

            [token, ..] => Err(ParseError::Expected {
                expected,
                found: token.kind.clone(),
                position: token.position,
            }),

            _ => Err(ParseError::UnexpectedUnderflow),
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
            Err(ParseError::ExpectedIdentifier(token.clone()))
        }
    }

    fn consume(&mut self) -> Result<&Token> {
        if let Some(the) = self.remains().first() {
            self.advance(1);
            Ok(the)
        } else {
            Err(ParseError::UnexpectedOverflow)
        }
    }

    fn unconsume(&mut self) -> Result<()> {
        if self.offset > 0 {
            self.offset -= 1;
            Ok(())
        } else {
            Err(ParseError::UnexpectedUnderflow)
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
            Err(ParseError::UnexpectedOverflow)
        }
    }

    //    pub fn parse_compilation_unit(&mut self) -> Result<CompilationUnit<ParseInfo>> {
    //        let _t = self.trace();
    //
    //        let decls = self.parse_declaration_list()?;
    //
    //        Ok(CompilationUnit::from_declarations(decls))
    //    }

    pub fn parse_declaration_list(&mut self) -> Result<Vec<Declaration<ParseInfo>>> {
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

        Ok(decls)
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
                    kind: TokenKind::Assign         // Function or value
                        | TokenKind::TypeAssign     // Type
                        | TokenKind::TypeAscribe    // Type signature
                        | TokenKind::Colon, // Module
                    ..
                },
                ..
            ] | [
                Token {
                    kind: TokenKind::Layout(Layout::Newline),
                    ..
                },
                ..
            ] | [
                Token {
                    kind: TokenKind::Keyword(
                        Keyword::Module | Keyword::Use | Keyword::Signature | Keyword::Witness
                    ),
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

            [
                t,
                Token {
                    kind: TokenKind::Identifier(name),
                    position,
                },
                Token {
                    kind: TokenKind::Colon,
                    ..
                },
                ..,
            ] if t.is_keyword(Keyword::Module) => {
                // <module> <id> <:>
                self.advance(3);

                Ok(Declaration::Module(
                    ParseInfo::from_position(*position),
                    ModuleDeclaration {
                        name: Identifier::from_str(name),
                        declarator: self.parse_block(|parser| parser.parse_module_declarator())?,
                    },
                ))
            }

            [
                t,
                Token {
                    kind: TokenKind::Identifier(name),
                    position,
                },
                Token {
                    kind: TokenKind::Period,
                    ..
                },
                ..,
            ] if t.is_keyword(Keyword::Module) => {
                // <module> <id> <.>
                self.advance(3);

                let name = Identifier::from_str(name);
                Ok(Declaration::Module(
                    ParseInfo::from_position(*position),
                    ModuleDeclaration {
                        name: name.clone(),
                        declarator: ast::ModuleDeclarator::External(name),
                    },
                ))
            }

            [
                t,
                Token {
                    kind: TokenKind::Identifier(name),
                    position,
                },
                ..,
            ] if t.is_keyword(Keyword::Use) => {
                // <module> <id> <.>
                self.advance(3);

                let name = Identifier::from_str(name);
                Ok(Declaration::Use(
                    ParseInfo::from_position(*position),
                    UseDeclaration {
                        qualified_binder: None,
                        module: ModuleDeclaration {
                            name: name.clone(),
                            declarator: ast::ModuleDeclarator::External(name),
                        },
                    },
                ))
            }

            [
                t,
                Token {
                    kind: TokenKind::Identifier(name),
                    position,
                },
                ..,
            ] if t.is_keyword(Keyword::Signature) => {
                // constraint <id> <::=>
                self.advance(3);

                Ok(Declaration::Constraint(
                    ParseInfo::from_position(*position),
                    ConstraintDeclaration {
                        name: Identifier::from_str(name),
                        type_parameters: self.parse_forall_clause()?,
                        declarator: if let TypeDeclarator::Record(_, record) =
                            self.parse_block(|parser| parser.parse_type_declarator())?
                        {
                            record
                        } else {
                            Err(ParseError::Expected {
                                expected: TokenKind::LeftBrace,
                                found: self.peek()?.kind.clone(),
                                position: *position,
                            })?
                        },
                    },
                ))
            }

            [t, ..] if t.is_keyword(Keyword::Witness) => {
                // witness
                self.advance(1);

                let type_signature = self.parse_type_signature()?;
                let hasher = &mut DefaultHasher::default();
                type_signature.to_string().hash(hasher);

                let hash = hasher.finish();

                // <:=>
                self.advance(1);

                let body = self.parse_block(|parser| parser.parse_record())?;

                Ok(Declaration::Witness(
                    ParseInfo::from_position(*&t.position),
                    WitnessDeclaration {
                        type_signature,
                        implementation: body,
                    },
                ))
            }

            otherwise => panic!("{otherwise:?}"),
        }
    }

    fn parse_module_declarator(&mut self) -> Result<ModuleDeclarator<ParseInfo>> {
        let _t = self.trace();

        Ok(ModuleDeclarator::Inline(self.parse_declaration_list()?))
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
                params.push(self.identifier().map(|(_, id)| Identifier { image: id })?);
            }

            if params.is_empty() {
                Err(ParseError::ExpectedIdentifier(self.peek()?.clone()))?;
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
                .parse_block(|parser| parser.parse_sequence())
                .map(|body| {
                    if let Expr::Lambda(pi, lambda) = body {
                        Expr::RecursiveLambda(
                            pi,
                            SelfReferential {
                                own_name,
                                lambda: lambda.into(),
                            },
                        )
                    } else {
                        body
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
    fn parse_record_type_decl(&mut self) -> Result<RecordDeclarator> {
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
        let type_signature = self.parse_type_expression(0)?;
        Ok(FieldDeclarator {
            // It could really keep this Identifier instead of cloning it
            name: Identifier::from_str(&label),
            type_signature,
        })
    }

    fn parse_type_expression(&mut self, precedence: usize) -> Result<TypeExpression> {
        let _t = self.trace();

        let prefix = self.parse_type_expr_prefix()?;
        self.parse_type_expr_infix(prefix, precedence)
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
            ] => self.parse_simple_type_expr_term(id, position),

            [
                Token {
                    kind: TokenKind::LeftParen,
                    ..
                },
                ..,
            ] => {
                self.advance(1);
                let prefix = self.parse_type_expression(0);
                self.expect(TokenKind::RightParen)?;
                prefix
            }

            // parens
            otherwise => panic!("{otherwise:?}"),
        }
    }

    fn peek_type_expr_operator(&self, lhs: &TypeExpression) -> Option<TypeExprOperator> {
        match self.remains() {
            [
                Token {
                    kind: TokenKind::Identifier(_) | TokenKind::LeftParen,
                    ..
                },
                ..,
            ] if lhs.is_applicable() => Some(TypeExprOperator::Apply),

            [
                Token {
                    kind: TokenKind::Arrow,
                    ..
                },
                ..,
            ] => Some(TypeExprOperator::Arrow),

            [
                Token {
                    kind: TokenKind::Comma,
                    ..
                },
                ..,
            ] => Some(TypeExprOperator::Tuple),

            _ => None,
        }
    }

    // This ought to be able to parse identifiers with dots in them
    fn parse_simple_type_expr_term(
        &mut self,
        id: &String,
        position: &SourceLocation,
    ) -> Result<ast::TypeExpression<ParseInfo, IdentifierPath>> {
        let _t = self.trace();

        let parse_info = ParseInfo::from_position(*position);
        if is_lowercase(id) {
            self.advance(1);
            Ok(TypeExpression::Parameter(
                parse_info,
                Identifier::from_str(id),
            ))
        } else {
            let id = self.parse_identifier_path()?;
            Ok(TypeExpression::Constructor(parse_info, id))
        }
    }

    fn parse_type_expr_infix(
        &mut self,
        lhs: TypeExpression,
        context_precedence: usize,
    ) -> Result<TypeExpression> {
        let _t = self.trace();

        let operator = match self.peek_type_expr_operator(&lhs) {
            Some(op) if op.precedence() > context_precedence => op,
            _ => return Ok(lhs),
        };

        match operator {
            TypeExprOperator::Apply => {
                let rhs = self.parse_type_expr_prefix()?;
                self.parse_type_expr_infix(
                    TypeExpression::Apply(
                        ParseInfo::default(),
                        ApplyTypeExpr {
                            function: lhs.into(),
                            argument: rhs.into(),
                            phase: PhantomData,
                        },
                    ),
                    context_precedence,
                )
            }

            TypeExprOperator::Arrow => {
                let position = self.consume()?.position;
                let computed_precedence = if operator.is_right_associative() {
                    operator.precedence() - 1
                } else {
                    operator.precedence()
                };

                let rhs = self.parse_type_expression(computed_precedence)?;
                self.parse_type_expr_infix(
                    TypeExpression::Arrow(
                        ParseInfo::from_position(position),
                        ArrowTypeExpr {
                            domain: lhs.into(),
                            codomain: rhs.into(),
                        },
                    ),
                    context_precedence,
                )
            }

            TypeExprOperator::Tuple => {
                let position = self.consume()?.position;
                let rhs = self.parse_type_expression(operator.precedence())?;

                let tuple = match lhs {
                    TypeExpression::Tuple(pi, TupleTypeExpr(mut elements)) => {
                        elements.push(rhs);
                        TypeExpression::Tuple(pi, TupleTypeExpr(elements))
                    }

                    lhs => TypeExpression::Tuple(
                        ParseInfo::from_position(position),
                        TupleTypeExpr(vec![lhs, rhs]),
                    ),
                };

                self.parse_type_expr_infix(tuple, context_precedence)
            }
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
        let binder = IdentifierPath::new(&binder);
        self.expect(TokenKind::Equals)?;
        let bound = self.parse_block(|parser| parser.parse_sequence())?;
        let bound = if let Expr::Lambda(pi, lambda) = bound {
            Expr::RecursiveLambda(
                pi,
                SelfReferential {
                    own_name: binder.clone(),
                    lambda,
                },
            )
        } else {
            bound
        };
        if self.peek()?.is_newline() {
            self.consume()?;
        }
        self.expect(TokenKind::Keyword(Keyword::In))?;
        if self.peek()?.is_newline() {
            self.consume()?;
        }
        let body = self.parse_block(|parser| parser.parse_sequence())?;
        Ok(Expr::Let(
            ParseInfo { location },
            Binding {
                binder,
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
            Err(ParseError::ExpectedIdentifier(self.peek()?.clone()))?;
        }

        self.expect(TokenKind::Period)?;

        let body = self.parse_block(|parser| parser.parse_sequence())?;

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

        match self.remains() {
            [t, u, v, ..]
                if t.is_sequence_separator()
                    && Self::is_expr_prefix(&u.kind)
                    && Self::is_expr_prefix(&v.kind) =>
            {
                println!("parse_sequence(1)");
                self.consume()?;
                self.parse_subsequent(prefix)
            }

            // If the previous expression ends in a Dedent "back to" sequence level
            [t, u, ..]
                if t.is_dedent()
                    && Self::is_expr_prefix(&u.kind)
                    && u.location().is_same_block(&prefix.parse_info().location) =>
            {
                println!("parse_sequence(2)");
                self.consume()?;
                self.parse_subsequent(prefix)
            }

            [t, u, ..]
                if Self::is_expr_prefix(&t.kind)
                    && t.location().is_same_block(&prefix.parse_info().location)
                    && u.kind != TokenKind::End =>
            {
                println!("parse_sequence(3)");
                self.parse_subsequent(prefix)
            }

            _ => Ok(prefix),
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

            [t, ..] if t.is_keyword(Keyword::If) => self.parse_if_then_else(),

            [
                Token {
                    kind: TokenKind::Interpolate(Interpolation::Interlude(prelude)),
                    position,
                },
                ..,
            ] => self.parse_interpolated_text(*position, prelude.clone()),

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
            TokenKind::Layout(..)
                | TokenKind::TypeAscribe
                | TokenKind::TypeAssign
                | TokenKind::Assign
                | TokenKind::Colon
                | TokenKind::RightBrace
                | TokenKind::Pipe
                | TokenKind::End
                | TokenKind::Keyword(
                    Keyword::And
                        | Keyword::Or
                        | Keyword::Xor
                        | Keyword::Then
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
            TokenKind::Assign,
            TokenKind::TypeAssign,
            TokenKind::Layout(Layout::Dedent),
            TokenKind::Keyword(Keyword::Let),
            TokenKind::Keyword(Keyword::In),
            TokenKind::Keyword(Keyword::Into),
            TokenKind::Keyword(Keyword::Then),
            TokenKind::Keyword(Keyword::Else),
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
                self.advance(1); //the indent
                self.parse_juxtaposed(lhs, context_precedence)
            }

            // f x
            [t, u, ..]
                if Self::is_expr_prefix(&t.kind)
                    && !matches!(
                        u.kind,
                        TokenKind::Assign | TokenKind::TypeAscribe | TokenKind::TypeAssign
                    )
                    && Operator::Juxtaposition.precedence() > context_precedence =>
            {
                self.parse_juxtaposed(lhs, context_precedence)
            }

            _ => Ok(lhs),
        }
    }

    fn parse_interpolated_text(
        &mut self,
        position: SourceLocation,
        prelude: Literal,
    ) -> Result<Expr> {
        let pi = ParseInfo::from_position(position);
        let mut interpolator = Interpolate::begin(pi, prelude.into());
        self.advance(1);

        loop {
            interpolator.expression(self.parse_expression(0)?);
            // The backtick?
            self.advance(1);
            match self.consume()? {
                Token {
                    kind: TokenKind::Interpolate(Interpolation::Interlude(literal)),
                    position,
                } => interpolator
                    .literal(ParseInfo::from_position(*position), literal.clone().into()),

                Token {
                    kind: TokenKind::Interpolate(Interpolation::Epilogue(literal)),
                    position,
                } => {
                    let pi = ParseInfo::from_position(*position);
                    interpolator.literal(pi, literal.clone().into());
                    break Ok(Expr::Interpolate(pi, interpolator));
                }

                unexpected => panic!("{unexpected:?}"),
            }
        }
    }

    fn parse_juxtaposed(&mut self, lhs: Expr, context_precedence: usize) -> Result<Expr> {
        let _t = self.trace();

        println!("parse_juxtaposed: about take rhs");
        let rhs = self.parse_expression(Operator::Juxtaposition.precedence())?;

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
                Operator::Ascribe => {
                    let type_signature = self
                        .parse_type_signature()?
                        .map_names(&|name| QualifiedName::new(name, "<<smuggler>>"));

                    // Have to hack type_signature because its name type
                    // here is IdentiferPath but Expr requires that it be
                    // QualifiedName because Expr is not parameterized
                    // over type name types.
                    //
                    // I could mangle a QualifiedName with a bogus contents
                    // that can be turned into an IdentifierPath in the
                    // resolution stage, so that it might be correctly
                    // qualified.

                    Ok(Expr::Ascription(
                        *lhs.parse_info(),
                        TypeAscription {
                            ascribed_tree: lhs.into(),
                            type_signature,
                        },
                    ))
                }

                Operator::Select => {
                    let lhs = self.parse_select_operator(lhs)?;
                    self.parse_expr_infix(lhs, context_precedence)
                }

                Operator::Tuple => self.parse_tuple_expression(
                    lhs,
                    operator_position,
                    computed_precedence,
                    context_precedence,
                ),

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
        computed_precedence: usize,
        context_precedence: usize,
    ) -> Result<Expr> {
        let rhs = self.parse_expression(computed_precedence)?;
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
            self.parse_identifier_path_expr(*pi, id.clone())
        } else {
            self.parse_projection(lhs)
        }
    }

    fn parse_identifier_path(&mut self) -> Result<IdentifierPath> {
        let _t = self.trace();

        let (_, head) = self.identifier()?;
        let mut tail = vec![];
        loop {
            match self.remains() {
                [
                    Token {
                        kind: TokenKind::Period,
                        ..
                    },
                    Token {
                        kind: TokenKind::Identifier(id),
                        ..
                    },
                    ..,
                ] => {
                    self.advance(2);
                    tail.push(id.clone())
                }
                _ => {
                    break Ok(IdentifierPath { head, tail });
                }
            }
        }
    }

    fn parse_identifier_path_expr(&mut self, pi: ParseInfo, lhs: IdentifierPath) -> Result<Expr> {
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

        let universal_quantifiers = self.parse_forall_clause()?;
        let constraints = if self.has_type_constraints() {
            self.parse_constraint_clause()?
        } else {
            Vec::default()
        };
        let body = self.parse_type_expression(0)?;

        Ok(TypeSignature {
            universal_quantifiers,
            constraints,
            body,
            phase: PhantomData,
        })
    }

    fn parse_constraint_clause(&mut self) -> Result<Vec<ConstraintExpression>> {
        let _t = self.trace();

        // Foo bar + Baz quux Int |-
        // So if there is a |- before :=, then there constraints
        let mut constraints = vec![self.parse_type_constraint()?];

        while self.peek()?.kind == TokenKind::Plus {
            self.advance(1);
            constraints.push(self.parse_type_constraint()?);
        }

        self.expect(TokenKind::TypeConstraint)?;

        Ok(constraints)
    }

    fn has_type_constraints(&mut self) -> bool {
        self.remains()
            .iter()
            .position(|t| t.kind == TokenKind::Assign)
            .is_some_and(|p| {
                self.remains()[..p]
                    .iter()
                    .position(|t| t.kind == TokenKind::TypeConstraint)
                    .is_some()
            })
    }

    fn parse_type_constraint(&mut self) -> Result<ConstraintExpression> {
        let _t = self.trace();

        let (pos, id) = self.identifier()?;

        let mut arguments = vec![];

        while matches!(
            self.peek()?.kind,
            TokenKind::Identifier(..) | TokenKind::LeftParen
        ) {
            if self.peek()?.is_identifier() {
                let (pos, id) = self.identifier()?;
                let pi = ParseInfo::from_position(pos);
                arguments.push(if is_lowercase(&id) {
                    TypeExpression::Parameter(pi, Identifier::from_str(&id))
                } else {
                    TypeExpression::Constructor(pi, IdentifierPath::new(&id))
                });
            } else {
                self.expect(TokenKind::LeftParen)?;
                arguments.push(self.parse_type_expression(0)?);
                self.expect(TokenKind::RightParen)?;
            }
        }

        Ok(ConstraintExpression {
            annotation: ParseInfo::from_position(pos),
            class: IdentifierPath::new(&id),
            parameters: arguments,
        })
    }

    fn parse_coproduct(&mut self) -> Result<CoproductDeclarator> {
        let _t = self.trace();

        let mut constructors = vec![self.parse_coproduct_constructor()?];

        if self.peek()?.is_dedent() {
            self.consume()?;
        }

        let is_constructor_separator = |remains: &[Token]| match remains {
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

        while let Some(separator) = is_constructor_separator(self.remains()) {
            // |
            self.advance(separator);
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
                self.expect(TokenKind::LeftParen)?;
                signature.push(self.parse_type_expression(0)?);
                self.expect(TokenKind::RightParen)?;
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
        let consequent = self.parse_block(|parser| parser.parse_sequence())?;
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

    fn parse_if_then_else(&mut self) -> Result<Expr> {
        let _t = self.trace();

        let position = self.expect(TokenKind::Keyword(Keyword::If))?.position;

        let predicate = self.parse_block(|parser| parser.parse_sequence())?;

        self.parse_block(|parser| {
            if parser.peek()?.is_newline() {
                parser.advance(1);
            }
            parser.expect(TokenKind::Keyword(Keyword::Then))?;

            let consequent = parser.parse_block(|parser| parser.parse_sequence())?;

            if parser.peek()?.is_newline() {
                parser.advance(1);
            }

            parser.expect(TokenKind::Keyword(Keyword::Else))?;

            let alternate = parser.parse_block(|parser| parser.parse_sequence())?;

            Ok(Expr::If(
                ParseInfo::from_position(position),
                IfThenElse {
                    predicate: predicate.into(),
                    consequent: consequent.into(),
                    alternate: alternate.into(),
                },
            ))
        })
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
            Literal::Unit => ast::Literal::Unit,
        }
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { image } = self;
        write!(f, "{image}")
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

impl fmt::Display for ParseInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { location } = self;
        write!(f, "{location}")
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
        let x = p.parse_type_expression(0).unwrap();
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
        let x = p.parse_declaration_list().unwrap();
        println!("{x:?}")
    }
}
