use std::{cell::Cell, fmt, hash::Hash, marker::PhantomData, result, vec};

use backtrace::Backtrace;
use thiserror::Error;

use crate::{
    ast::{
        self, Apply, ApplyTypeExpr, Array, ArrowTypeExpr, Binding, ConfinementModifier,
        ConstraintExpression, Declaration, Deconstruct, FieldDeclarator, ForeignDeclaration,
        IdentifierPattern, IfThenElse, Interpolate, Kind, Lambda, ModuleDeclaration,
        ModuleDeclarator, Projection, Record, SelfReferential, Sequence, SignatureDeclaration,
        Tree, Tuple, TupleTypeExpr, TypeAscription, TypeDeclaration, TypeDeclarator,
        TypeExpression, TypeSignature, TypeVariable, UseDeclaration, ValueDeclaration,
        ValueDeclarator, WitnessDeclaration,
        namer::{QualifiedName, TypeOrigin},
        pattern::{ConstructorPattern, MatchClause, Pattern, StructPattern, TuplePattern},
    },
    lexer::{
        BindingOperator, Interpolation, Keyword, Layout, Literal, Operator, SourceLocation, Token,
        TokenKind,
    },
    phase, source_map,
};

pub struct Parsed;

impl phase::Phase for Parsed {
    type Annotation = ParseInfo;
    type TermId = IdentifierPattern<ParseInfo>;
    type TypeId = IdentifierPath;
}

pub type Expr = phase::Expr<Parsed>;
type RecordDeclarator = ast::RecordDeclarator<ParseInfo>;
type CoproductDeclarator = ast::CoproductDeclarator<ParseInfo>;
type CoproductConstructor = ast::CoproductConstructor<ParseInfo>;

#[derive(Clone, Copy)]
struct ExpressionContext {
    precedence: usize,
    anchor_column: u32,
}

impl ExpressionContext {
    fn from_prefix(prefix: &Expr, precedence: usize) -> Self {
        Self {
            precedence,
            anchor_column: prefix.parse_info().location.column,
        }
    }
}

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
    /// One past the node's last character. A node whose extent nobody recorded --
    /// anything the parser did not build, and anything built before its children
    /// were parsed -- has `end == location`, which reads as "somewhere here" and is
    /// what every position in the tree used to mean.
    pub end: SourceLocation,
    /// The source file these tokens came from, resolvable via [`crate::source_map`].
    /// Stamped from the file being parsed; `FileId::UNKNOWN` for synthetic nodes.
    pub file: source_map::FileId,
}

impl ParseInfo {
    /// Build a `ParseInfo` for a node at `location`, tagging it with the file
    /// currently being parsed (see [`crate::source_map::with_current`]).
    pub fn from_position(location: SourceLocation) -> Self {
        Self {
            location,
            end: location,
            file: source_map::current(),
        }
    }

    /// A node that runs from `location` up to (not including) `end`.
    pub fn spanning(location: SourceLocation, end: SourceLocation) -> Self {
        Self {
            location,
            end,
            file: source_map::current(),
        }
    }

    /// Whether `location` falls inside this node -- start inclusive, end exclusive,
    /// and a point span holds only itself.
    pub fn contains(&self, location: SourceLocation) -> bool {
        let after_start =
            (self.location.row, self.location.column) <= (location.row, location.column);
        let before_end = (location.row, location.column) < (self.end.row, self.end.column);
        after_start && (before_end || self.location == self.end && self.location == location)
    }

    /// How wide this node is, for choosing the narrowest of several that contain a
    /// position. Rows count for much more than columns, so a node spanning lines is
    /// never narrower than one inside a line.
    pub fn width(&self) -> u64 {
        let rows = u64::from(self.end.row.saturating_sub(self.location.row));
        let columns = u64::from(self.end.column) + rows * 100_000;
        columns.saturating_sub(u64::from(self.location.column))
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
        self.tail.last().unwrap_or(&self.head)
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
/// A name as written. Shared rather than owned: a compiler copies names
/// constantly -- every symbol table key, every resolved variable, every
/// qualified name a substitution passes through -- and copying the characters
/// each time was one of the larger allocation costs in a check. `Arc` because a
/// language server holds an elaborated table behind a lock shared with its
/// message loop.
#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub struct Identifier {
    image: std::sync::Arc<str>,
}

impl Identifier {
    pub fn from_str(id: &str) -> Self {
        Self {
            image: std::sync::Arc::from(id),
        }
    }

    pub fn as_str(&self) -> &str {
        &self.image
    }
}

/// The name of the enclosing function, for a [`ParseError::Fault`]. Rust has no
/// stable way to ask for it, so this names a local `fn` and reads the path back out
/// of its type name -- the usual trick. Deriving it beats writing the name out by
/// hand, which would rot silently the first time a parse function is renamed.
macro_rules! parser_name {
    () => {{
        fn marker() {}
        fn path_of<A>(_: A) -> &'static str {
            std::any::type_name::<A>()
        }
        $crate::parser::trim_parser_path(path_of(marker))
    }};
}

/// `lukas::parser::Parser<'_>::parse_expr_prefix::marker` -> `parse_expr_prefix`.
/// Closures are transparent here: a fault raised inside one should still name the
/// parse function that owns it.
#[doc(hidden)]
pub fn trim_parser_path(path: &'static str) -> &'static str {
    let mut path = path.strip_suffix("::marker").unwrap_or(path);
    while let Some(enclosing) = path.strip_suffix("::{{closure}}") {
        path = enclosing;
    }
    path.rsplit("::").next().unwrap_or(path)
}

/// Quote the offending source line beneath a fault, with a caret under the column --
/// the same treatment name and type errors get through `Located`'s `Display`.
fn quoted_line(at: &ParseInfo) -> String {
    source_map::snippet(at.file, at.location.row, at.location.column)
        .map_or_else(String::new, |snippet| format!("\n{snippet}"))
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

    #[error("{position}: confinement modifiers apply to foreign types, not foreign terms")]
    ConfinementModifierOnForeignTerm { position: SourceLocation },

    #[error("{position}: a requirement set cannot be empty; omit `[]` instead")]
    EmptyRequirementSet { position: SourceLocation },

    #[error("{position}: duplicate requirement `{requirement}`")]
    DuplicateRequirement {
        position: SourceLocation,
        requirement: IdentifierPath,
    },

    #[error("{position}: requirement sets apply to foreign values, not foreign types")]
    RequirementSetOnForeignType { position: SourceLocation },

    #[error(
        "{position}: unexpected input; the parser stopped here with tokens left over.\n\
         A declaration above likely failed to parse, or the layout desynced (a stray \
         indent/dedent). Everything from here on -- possibly including `start` -- was \
         dropped.\nfound: {found}"
    )]
    UnconsumedInput {
        found: TokenKind,
        position: SourceLocation,
    },

    /// A parse function ran out of alternatives. These arms mark syntax the parser
    /// does not handle *yet* as much as they mark bad input, so the message says
    /// which function gave up -- that is what tells the two apart -- and quotes the
    /// tokens ahead, where a layout desync shows up as a stray `<Ind>`/`<Ded>`.
    #[error(
        "{at}: `{parser}` has no rule for this input\n\
         found: {found}\n\
         next:  {lookahead}{}",
        quoted_line(.at)
    )]
    Fault {
        parser: &'static str,
        at: ParseInfo,
        found: TokenKind,
        lookahead: String,
    },
}

type Result<A> = result::Result<A, ParseError>;

/// How many upcoming tokens a fault quotes. Enough to show the shape of what the
/// parser choked on -- a whole short declaration, usually -- without a wall of text.
const FAULT_LOOKAHEAD: usize = 8;

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

impl phase::Interpolate<Parsed> {
    pub fn begin(pi: ParseInfo, prelude: Literal) -> Self {
        Self(vec![ast::Segment::Literal(pi, prelude.into())])
    }

    pub fn expression(&mut self, expr: Expr) {
        let expr = Expr::Apply(
            *expr.parse_info(),
            Apply {
                function: Expr::Variable(
                    *expr.parse_info(),
                    IdentifierPattern::from_atom(*expr.parse_info(), "display"),
                )
                .into(),
                argument: expr.into(),
            },
        );
        self.0.push(ast::Segment::Expression(expr.into()));
    }

    pub fn literal(&mut self, pi: ParseInfo, literal: Literal) {
        self.0.push(ast::Segment::Literal(pi, literal.into()));
    }
}

enum TypeExprOperator {
    Apply,
    ConfinementAscription,
    Arrow,
    Tuple,
}

impl TypeExprOperator {
    fn precedence(&self) -> usize {
        match self {
            Self::Apply => 4,
            Self::ConfinementAscription => 3,
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
    /// Indent columns of the blocks currently open through [`parse_block`], outermost
    /// first. Lets a block tell its *own* closing `Dedent` (which returns to the
    /// enclosing block's column) from a `Dedent` that dedents further out because the
    /// body already consumed this block's closer -- e.g. a coproduct whose `|`
    /// alternatives dedent back before the bar, eating the type body's dedent.
    indent_columns: Vec<u32>,
    /// How many `(` are open around the expression being parsed. Inside parentheses
    /// there is no enclosing block for a line break to belong to, so an `Indent` there
    /// continues the expression instead of opening one -- see `parse_expr_infix`.
    paren_depth: usize,
}

impl<'a> Parser<'a> {
    pub fn from_tokens(remains: &'a [Token]) -> Self {
        Self {
            remains,
            offset: 0,
            indent_columns: Vec::new(),
            paren_depth: 0,
        }
    }

    pub fn remains(&self) -> &'a [Token] {
        &self.remains[self.offset..]
    }

    fn advance(&mut self, by: usize) {
        self.offset += by;
    }

    fn trace(&mut self) -> TraceGuard {
        const REMAINS_COL: usize = 120;

        // Everything below builds ONE trace line and is otherwise pure -- and it
        // starts by capturing and symbolising a backtrace, per parse function call.
        // Unwinding, demangling and dyld section lookups were the top self-time
        // entries in a sampling profile of a stdlib parse; skip the lot unless
        // someone is actually listening at TRACE.
        if !tracing::enabled!(tracing::Level::TRACE) {
            return TraceGuard::enter();
        }

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

            //tracing::trace!(
            //    "{:<width$}{}{}",
            //    remains.into_iter().collect::<String>(),
            //    " ".repeat(indent),
            //    step,
            //    width = REMAINS_COL
            //);
        } else {
            tracing::trace!("Unknown caller.");
        }

        TraceGuard::enter()
    }

    /// A fault at the next token: the parser is standing on input it has no rule
    /// for. `parser` comes from [`parser_name!`] at the call site.
    fn fault(&self, parser: &'static str) -> ParseError {
        match self.remains() {
            [found, rest @ ..] => Self::fault_with(
                parser,
                ParseInfo::spanning(found.position, found.end),
                found.kind.clone(),
                rest,
            ),

            // Nothing left to stand on: report at the last token consumed, so the
            // caret still lands in the file instead of at 1:1.
            [] => Self::fault_with(
                parser,
                ParseInfo::from_position(self.last_position()),
                TokenKind::End,
                &[],
            ),
        }
    }

    /// A fault at a token already consumed -- for a `match self.consume()?` that
    /// falls through, where the offending token is no longer what comes next.
    fn fault_at(
        &self,
        parser: &'static str,
        position: SourceLocation,
        found: TokenKind,
    ) -> ParseError {
        Self::fault_with(
            parser,
            ParseInfo::from_position(position),
            found,
            self.remains(),
        )
    }

    fn fault_with(
        parser: &'static str,
        at: ParseInfo,
        found: TokenKind,
        next: &[Token],
    ) -> ParseError {
        ParseError::Fault {
            parser,
            at,
            found,
            // By kind, not by `Token`'s `Display`: a row:col on every one of eight
            // consecutive tokens buries the shape of the input, which is the thing
            // worth reading here. The caret line carries the position.
            lookahead: next
                .iter()
                .take(FAULT_LOOKAHEAD)
                .map(|token| token.kind.to_string())
                .collect::<Vec<_>>()
                .join(" "),
        }
    }

    /// Where the last consumed token sat, for a fault raised at end of input.
    /// A node reaching from `start` to the end of whatever has been consumed since:
    /// call it once a production has taken all of its own tokens, and the node knows
    /// its extent.
    fn span_from(&self, start: SourceLocation) -> ParseInfo {
        ParseInfo::spanning(start, self.last_end())
    }

    /// One past the last *real* token consumed. Layout tokens are skipped: they are
    /// zero-width marks between lines, and a node does not reach into the next one.
    fn last_end(&self) -> SourceLocation {
        self.remains[..self.offset]
            .iter()
            .rev()
            .find(|token| !matches!(token.kind, TokenKind::Layout(..)))
            .map_or_else(SourceLocation::default, |token| token.end)
    }

    fn last_position(&self) -> SourceLocation {
        self.offset
            .checked_sub(1)
            .and_then(|previous| self.remains.get(previous))
            .map_or_else(SourceLocation::default, |token| token.position)
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
            ..
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

    /// Parse every declaration in the file, keeping going past one that fails.
    ///
    /// A syntax error costs the declaration it is in, not the file: the parser
    /// resynchronises on the next line that starts in column one -- which is where a
    /// top-level declaration starts, and is the same boundary the editor's grammar
    /// uses -- and carries on. What comes back is everything that parsed, and every
    /// error found on the way.
    pub fn parse_declaration_list_recovering(
        &mut self,
    ) -> (Vec<Declaration<ParseInfo>>, Vec<ParseError>) {
        let mut declarations = Vec::new();
        let mut errors = Vec::new();

        loop {
            while self.peek().is_ok_and(Token::is_newline) {
                self.advance(1);
            }
            match self.peek() {
                Ok(token) if token.is_end() => break,
                Err(..) => break,
                _ => {}
            }

            let started_at = self.offset;
            match self.parse_declaration() {
                Ok(declaration) => declarations.push(declaration),
                Err(error) => {
                    errors.push(error);
                    self.resynchronise(started_at);
                }
            }

            // A declaration that consumed nothing would loop forever.
            if self.offset == started_at {
                self.advance(1);
            }
        }

        (declarations, errors)
    }

    /// Skip to where the next declaration could start: the first token of a line, at
    /// the left margin. Never backwards, and never nowhere -- `at_least` is the
    /// declaration that just failed, so resynchronising always moves past it.
    fn resynchronise(&mut self, at_least: usize) {
        self.offset = self.offset.max(at_least + 1);

        while let Some(token) = self.remains().first() {
            let begins_a_declaration = token.position.column == 1
                && !matches!(token.kind, TokenKind::Layout(..))
                && !token.is_end();
            if begins_a_declaration || token.is_end() {
                break;
            }
            self.advance(1);
        }
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
                        Keyword::Module
                            | Keyword::Use
                            | Keyword::Signature
                            | Keyword::Witness
                            | Keyword::Foreign
                            | Keyword::Alias
                            // `opaque <id> ::=` -- without this, an opaque declaration
                            // after a binding whose body is on its own indented line
                            // (which ends in a Dedent, not a Newline separator) is not
                            // recognised as the next declaration, so the list stops
                            // early and the enclosing block reports "expected <Ded>".
                            | Keyword::Opaque
                            | Keyword::Confined
                            | Keyword::Unconfined
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
                modifier,
                opaque,
                Token {
                    kind: TokenKind::Identifier(name),
                    position,
                    ..
                },
                Token {
                    kind: TokenKind::TypeAssign,
                    ..
                },
                ..,
            ] if matches!(
                modifier.kind,
                TokenKind::Keyword(Keyword::Confined | Keyword::Unconfined)
            ) && opaque.is_keyword(Keyword::Opaque) =>
            {
                let confinement = if modifier.is_keyword(Keyword::Confined) {
                    ConfinementModifier::Confined
                } else {
                    ConfinementModifier::Unconfined
                };
                self.advance(4);

                Ok(Declaration::Type(
                    self.span_from(*position),
                    TypeDeclaration {
                        name: Identifier::from_str(name),
                        type_parameters: self.parse_forall_clause()?,
                        declarator: self.parse_block(|parser| parser.parse_type_declarator())?,
                        origin: TypeOrigin::UserDefined,
                        opaque: true,
                        confinement: Some(confinement),
                    },
                ))
            }

            [
                t,
                Token {
                    kind: TokenKind::Identifier(name),
                    position,
                    ..
                },
                Token {
                    kind: TokenKind::TypeAssign,
                    ..
                },
                ..,
            ] if t.is_keyword(Keyword::Alias) => {
                self.advance(3);
                let type_parameters = self.parse_forall_clause()?;
                let body = self.parse_block(|parser| parser.parse_type_expression(0))?;
                Ok(Declaration::Type(
                    self.span_from(*position),
                    TypeDeclaration {
                        name: Identifier::from_str(name),
                        type_parameters,
                        declarator: TypeDeclarator::Alias(self.span_from(*position), body),
                        origin: TypeOrigin::UserDefined,
                        opaque: false,
                        confinement: None,
                    },
                ))
            }

            [
                Token {
                    kind: TokenKind::Identifier(name),
                    position,
                    ..
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
                    self.span_from(*position),
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
                    ..
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
                self.expect(TokenKind::Assign)?;

                let own_name = IdentifierPath::new(name);

                Ok(Declaration::Value(
                    self.span_from(*position),
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
                    ..
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
                    self.span_from(*position),
                    TypeDeclaration {
                        name: Identifier::from_str(name),
                        // Move this to TypeDeclarator
                        type_parameters: self.parse_forall_clause()?,
                        declarator: self.parse_block(|parser| parser.parse_type_declarator())?,
                        origin: TypeOrigin::UserDefined,
                        opaque: false,
                        confinement: None,
                    },
                ))
            }

            [
                t,
                Token {
                    kind: TokenKind::Identifier(name),
                    position,
                    ..
                },
                Token {
                    kind: TokenKind::TypeAssign,
                    ..
                },
                ..,
            ] if t.is_keyword(Keyword::Opaque) => {
                // <opaque> <id> <::=>
                self.advance(3);

                Ok(Declaration::Type(
                    self.span_from(*position),
                    TypeDeclaration {
                        name: Identifier::from_str(name),
                        type_parameters: self.parse_forall_clause()?,
                        declarator: self.parse_block(|parser| parser.parse_type_declarator())?,
                        origin: TypeOrigin::UserDefined,
                        opaque: true,
                        confinement: None,
                    },
                ))
            }

            [
                t,
                Token {
                    kind: TokenKind::Identifier(name),
                    position,
                    ..
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
                    self.span_from(*position),
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
                    ..
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
                    self.span_from(*position),
                    ModuleDeclaration {
                        name: name.clone(),
                        declarator: ast::ModuleDeclarator::External(name),
                    },
                ))
            }

            [
                t,
                Token {
                    kind: TokenKind::Identifier(_),
                    position,
                    ..
                },
                ..,
            ] if t.is_keyword(Keyword::Use) => {
                let position = *position;
                self.advance(1); // past `use`
                let path = self.parse_module_path()?;
                Ok(Declaration::Use(
                    self.span_from(position),
                    UseDeclaration::new(None, path),
                ))
            }

            [
                t,
                Token {
                    kind: TokenKind::Identifier(name),
                    position,
                    ..
                },
                ..,
            ] if t.is_keyword(Keyword::Signature) => {
                // constraint <id> <::=>
                self.advance(3);

                let type_parameters = self.parse_forall_clause()?;
                // Optional supersignature context: `Eq α + Show α |- { … }`.
                // Reuses the witness/method constraint parser. `has_type_constraints`
                // looks for a `|-` before the block-opening layout, so a method-level
                // `|-` inside `{ … }` is out of range.
                let constraints = if self.has_type_constraints() {
                    self.parse_constraint_clause()?
                } else {
                    Vec::default()
                };

                Ok(Declaration::Signature(
                    self.span_from(*position),
                    SignatureDeclaration {
                        name: Identifier::from_str(name),
                        type_parameters,
                        constraints,
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

                // <:=>
                self.advance(1);

                let implementation = self.parse_block(|parser| parser.parse_record())?;

                Ok(Declaration::Witness(
                    self.span_from(t.position),
                    WitnessDeclaration {
                        type_signature,
                        implementation,
                    },
                ))
            }

            [t, ..] if t.is_keyword(Keyword::Foreign) => {
                // foreign
                self.advance(1);

                let requirements = self.parse_requirement_set()?;

                let (pos, id) = self.identifier()?;

                if matches!(
                    self.remains(),
                    [
                        Token {
                            kind: TokenKind::TypeAscribe,
                            ..
                        },
                        ..
                    ]
                ) {
                    // foreign value: `foreign [ <requirements> ] <id> :: <signature>`
                    self.expect(TokenKind::TypeAscribe)?;

                    let type_signature = self.parse_type_signature()?;

                    tracing::trace!("parse_declaration: type signature {type_signature}");

                    Ok(Declaration::Foreign(
                        self.span_from(pos),
                        ForeignDeclaration {
                            name: Identifier::from_str(&id),
                            requirements,
                            type_signature,
                        },
                    ))
                } else {
                    if !requirements.is_empty() {
                        return Err(ParseError::RequirementSetOnForeignType { position: pos });
                    }
                    Ok(Declaration::Type(
                        self.span_from(pos),
                        TypeDeclaration {
                            name: Identifier::from_str(&id),
                            type_parameters: Vec::new(),
                            declarator: TypeDeclarator::Coproduct(
                                self.span_from(pos),
                                CoproductDeclarator {
                                    constructors: Vec::new(),
                                },
                            ),
                            origin: TypeOrigin::Foreign,
                            opaque: false,
                            confinement: None,
                        },
                    ))
                }
            }

            [modifier, foreign, ..]
                if matches!(
                    modifier.kind,
                    TokenKind::Keyword(Keyword::Confined | Keyword::Unconfined)
                ) && foreign.is_keyword(Keyword::Foreign) =>
            {
                let confinement = if modifier.is_keyword(Keyword::Confined) {
                    ConfinementModifier::Confined
                } else {
                    ConfinementModifier::Unconfined
                };
                self.advance(2);
                let (pos, id) = self.identifier()?;
                if matches!(self.peek()?.kind, TokenKind::TypeAscribe) {
                    return Err(ParseError::ConfinementModifierOnForeignTerm {
                        position: modifier.position,
                    });
                }
                Ok(Declaration::Type(
                    self.span_from(pos),
                    TypeDeclaration {
                        name: Identifier::from_str(&id),
                        type_parameters: Vec::new(),
                        declarator: TypeDeclarator::Coproduct(
                            self.span_from(pos),
                            CoproductDeclarator {
                                constructors: Vec::new(),
                            },
                        ),
                        origin: TypeOrigin::Foreign,
                        opaque: false,
                        confinement: Some(confinement),
                    },
                ))
            }

            _ => Err(self.fault(parser_name!())),
        }
    }

    /// Parse the optional capability set in
    /// `foreign [ Browser; Dom ] document_title :: Unit -> Text`.
    ///
    /// This syntax is deliberately confined to foreign *values*. The caller
    /// diagnoses a following foreign type after it has seen whether `::` exists.
    fn parse_requirement_set(&mut self) -> Result<Vec<ast::Requirement<ParseInfo>>> {
        if self.peek()?.kind != TokenKind::LeftBracket {
            return Ok(Vec::new());
        }

        let opening = *self.consume()?.location();
        self.strip_layout()?;
        if self.peek()?.kind == TokenKind::RightBracket {
            return Err(ParseError::EmptyRequirementSet { position: opening });
        }

        let mut requirements = Vec::<ast::Requirement<ParseInfo>>::new();
        loop {
            let position = *self.peek()?.location();
            let name = self.parse_identifier_path()?;
            if requirements
                .iter()
                .any(|requirement| requirement.name == name)
            {
                return Err(ParseError::DuplicateRequirement {
                    position,
                    requirement: name,
                });
            }
            requirements.push(ast::Requirement {
                annotation: self.span_from(position),
                name,
            });

            self.strip_layout()?;
            match self.peek()?.kind {
                TokenKind::RightBracket => {
                    self.advance(1);
                    return Ok(requirements);
                }
                TokenKind::Semicolon => {
                    self.advance(1);
                    self.strip_layout()?;
                    // A semicolon separates two requirements; it is not a
                    // trailing delimiter.
                    if self.peek()?.kind == TokenKind::RightBracket {
                        return Err(self.fault(parser_name!()));
                    }
                }
                _ => {
                    return Err(ParseError::Expected {
                        expected: TokenKind::RightBracket,
                        found: self.peek()?.kind.clone(),
                        position: *self.peek()?.location(),
                    });
                }
            }
        }
    }

    fn parse_module_declarator(&mut self) -> Result<ModuleDeclarator<ParseInfo>> {
        let _t = self.trace();

        Ok(ModuleDeclarator::Inline(self.parse_declaration_list()?))
    }

    fn parse_module_path(&mut self) -> Result<IdentifierPath> {
        let _t = self.trace();

        let head = match self.remains() {
            [
                Token {
                    kind: TokenKind::Identifier(name),
                    ..
                },
                ..,
            ] => Ok(name.clone()),
            [t, ..] => Err(ParseError::ExpectedIdentifier(t.clone())),
            [] => Err(ParseError::UnexpectedUnderflow),
        }?;
        self.advance(1);

        let mut path = IdentifierPath::new(&head);
        while let [
            Token {
                kind: TokenKind::Period,
                ..
            },
            Token {
                kind: TokenKind::Identifier(segment),
                ..
            },
            ..,
        ] = self.remains()
        {
            let segment = segment.clone();
            self.advance(2);
            path.push(&segment);
        }

        // Consume the terminating `.`.
        self.expect(TokenKind::Period)?;
        Ok(path)
    }

    // preceed with parse_block, but it has to lookahead to see
    // that there is a forall in there, or it will erroneously
    // consume the type body block tokens.
    fn parse_forall_clause(&mut self) -> Result<Vec<TypeVariable>> {
        let _t = self.trace();

        if self.peek()?.is_keyword(Keyword::Forall) {
            // forall
            self.advance(1);

            let mut params = vec![];
            while self.peek()?.is_identifier() {
                let id = self.identifier();

                params.push(if matches!(self.peek()?.kind, TokenKind::Colon) {
                    // :
                    self.advance(1);

                    let kind = self.parse_kind_specifier()?;
                    id.map(|(_, image)| {
                        TypeVariable::with_kind(Identifier::from_str(&image), kind)
                    })?
                } else {
                    id.map(|(_, image)| TypeVariable::star(Identifier::from_str(&image)))?
                });
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

    fn parse_kind_specifier(&mut self) -> Result<Kind> {
        let prefix = self.parse_kind_spec_prefix()?;
        self.parse_kind_spec_infix(prefix)
    }

    fn parse_kind_spec_prefix(&mut self) -> Result<Kind> {
        match self.remains() {
            [
                Token {
                    kind: TokenKind::LeftParen,
                    ..
                },
                ..,
            ] => {
                // (
                self.advance(1);

                let kind = self.parse_kind_specifier()?;
                self.expect(TokenKind::RightParen)?;

                Ok(kind)
            }

            [
                Token {
                    kind: TokenKind::Star,
                    ..
                },
                ..,
            ] => {
                // *
                self.advance(1);

                Ok(Kind::star())
            }

            _ => Err(self.fault(parser_name!())),
        }
    }

    fn parse_kind_spec_infix(&mut self, prefix: Kind) -> Result<Kind> {
        match self.remains() {
            [
                Token {
                    kind: TokenKind::Arrow,
                    ..
                },
                Token {
                    kind: TokenKind::Star,
                    ..
                },
                ..,
            ] => {
                // -> *
                self.advance(2);
                self.parse_kind_spec_infix(Kind::Arrow(prefix.into(), Kind::star().into()))
            }

            [
                Token {
                    kind: TokenKind::Arrow,
                    ..
                },
                Token {
                    kind: TokenKind::LeftParen,
                    ..
                },
                ..,
            ] => {
                // -> (
                self.advance(2);

                let kind = Kind::Arrow(prefix.into(), self.parse_kind_specifier()?.into());
                self.expect(TokenKind::RightParen)?;

                if self.peek()?.kind == TokenKind::Arrow {
                    self.parse_kind_spec_infix(kind)
                } else {
                    Ok(kind)
                }
            }

            _otherwise => Ok(prefix),
        }
    }

    fn parse_value_declarator(
        &mut self,
        type_signature: Option<phase::TypeSignature<Parsed>>,
        own_name: IdentifierPath,
    ) -> Result<ValueDeclarator<ParseInfo>> {
        let _t = self.trace();

        Ok(ValueDeclarator {
            type_signature,
            body: self.parse_expression_block().map(|body| {
                if let Expr::Lambda(pi, lambda) = body {
                    Expr::RecursiveLambda(
                        pi,
                        SelfReferential {
                            own_name: IdentifierPattern::from_path(pi, own_name),
                            lambda,
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

            _ => Err(self.fault(parser_name!())),
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

        let (at, label) = self.identifier()?;
        let at = self.span_from(at);
        self.expect(TokenKind::TypeAscribe)?;
        let type_signature = self.parse_type_signature()?;
        Ok(FieldDeclarator {
            at,
            // It could really keep this Identifier instead of cloning it
            name: Identifier::from_str(&label),
            type_signature,
        })
    }

    fn parse_type_expression(
        &mut self,
        precedence: usize,
    ) -> Result<phase::TypeExpression<Parsed>> {
        let _t = self.trace();

        let prefix = self.parse_type_expr_prefix()?;
        self.parse_type_expr_infix(prefix, precedence)
    }

    fn parse_type_expr_prefix(&mut self) -> Result<phase::TypeExpression<Parsed>> {
        let _t = self.trace();

        match self.remains() {
            [
                Token {
                    kind: TokenKind::Identifier(id),
                    position,
                    ..
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
            _ => Err(self.fault(parser_name!())),
        }
    }

    fn peek_type_expr_operator(
        &self,
        lhs: &phase::TypeExpression<Parsed>,
    ) -> Option<TypeExprOperator> {
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
                    kind: TokenKind::Colon,
                    ..
                },
                Token {
                    kind: TokenKind::Keyword(Keyword::Confined | Keyword::Unconfined),
                    ..
                },
                ..,
            ] => Some(TypeExprOperator::ConfinementAscription),

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
        id: &str,
        position: &SourceLocation,
    ) -> Result<ast::TypeExpression<ParseInfo, IdentifierPath>> {
        let _t = self.trace();

        let parse_info = self.span_from(*position);
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
        lhs: phase::TypeExpression<Parsed>,
        context_precedence: usize,
    ) -> Result<phase::TypeExpression<Parsed>> {
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
                        self.span_from(position),
                        ArrowTypeExpr {
                            capture: ast::Confinement::fresh(),
                            domain: lhs.into(),
                            codomain: rhs.into(),
                        },
                    ),
                    context_precedence,
                )
            }

            TypeExprOperator::ConfinementAscription => {
                let position = self.consume()?.position;
                let keyword = self.consume()?;
                let (keyword_position, keyword_kind) = (keyword.position, keyword.kind.clone());
                let confinement = match keyword_kind {
                    TokenKind::Keyword(Keyword::Confined) => ConfinementModifier::Confined,
                    TokenKind::Keyword(Keyword::Unconfined) => ConfinementModifier::Unconfined,
                    // `peek_type_expr_operator` only reports an ascription when a
                    // capability keyword follows the `:`. A fault rather than an
                    // assertion, so that if the two ever disagree the parser says so
                    // instead of taking the process down.
                    found => return Err(self.fault_at(parser_name!(), keyword_position, found)),
                };
                self.parse_type_expr_infix(
                    TypeExpression::ConfinementAscription(
                        self.span_from(position),
                        lhs.into(),
                        confinement,
                    ),
                    context_precedence,
                )
            }

            TypeExprOperator::Tuple => {
                // Gather the comma-separated element types into one flat tuple, mirroring the
                // value and pattern sides. Each element is parsed at tuple precedence so a `,`
                // ends it, and a parenthesised group arrives as a single element -- so
                // `((Int, Int), Int)` stays nested rather than collapsing to `(Int, Int, Int)`.
                let position = self.consume()?.position;
                let mut elements = vec![lhs, self.parse_type_expression(operator.precedence())?];
                while matches!(self.peek()?.kind, TokenKind::Comma) {
                    self.consume()?; // the `,`
                    elements.push(self.parse_type_expression(operator.precedence())?);
                }
                self.parse_type_expr_infix(
                    TypeExpression::Tuple(self.span_from(position), TupleTypeExpr(elements)),
                    context_precedence,
                )
            }
        }
    }

    // The skeleton of an indented block: consume the opening `Indent`, parse the body, then
    // close. A `)` closes a block sitting inside parens -- its last statement's line ends with
    // the `)`, so the lexer emits no `Dedent` there.
    fn parse_block<F, A>(&mut self, parse_body: F) -> Result<A>
    where
        F: FnOnce(&mut Parser<'a>) -> Result<A>,
    {
        let _t = self.trace();

        if self.peek()?.is_indent() {
            // The column this block returns to when it closes -- the enclosing block's
            // indent (or column 1 at the top level).
            let enclosing_base = self.indent_columns.last().copied().unwrap_or(1);
            let indent_column = self.peek()?.position.column;
            self.consume()?; // the opening Indent
            self.indent_columns.push(indent_column);
            let body = parse_body(self)?;
            self.indent_columns.pop();

            let token = self.peek()?;
            match token.kind {
                // The body already consumed this block's own closing `Dedent` (its
                // matching level was eaten mid-parse, e.g. by a coproduct's `|`
                // continuation). The `Dedent` we see now returns *past* our enclosing
                // level, so it belongs to an outer block -- leave it for that block to
                // close on, rather than stealing it and swallowing following siblings.
                TokenKind::Layout(Layout::Dedent) if token.position.column < enclosing_base => {
                    Ok(body)
                }
                TokenKind::Layout(Layout::Dedent) | TokenKind::End => {
                    self.advance(1);
                    Ok(body)
                }
                TokenKind::RightParen => Ok(body),
                // An operator continuation on the body's last line consumed this block's
                // closing `Dedent` (double duty: continue the expression and close the block).
                // We are already back at the enclosing level, so the block is closed -- leave
                // the enclosing-level separator for the caller.
                TokenKind::Layout(Layout::Newline) => Ok(body),
                _ => Err(ParseError::Expected {
                    expected: TokenKind::Layout(Layout::Dedent),
                    found: token.kind.clone(),
                    position: token.position,
                }),
            }
        } else {
            parse_body(self)
        }
    }

    // A block whose body is a sequence of expressions.
    fn parse_expression_block(&mut self) -> Result<Expr> {
        self.parse_block(|parser| parser.parse_sequence())
    }

    fn parse_local_binding(&mut self, binding_operator: BindingOperator) -> Result<Expr> {
        let _t = self.trace();

        let let_token = self.consume()?;
        let position = let_token.position;
        let binder = self
            .parse_pattern()
            .map(|p| p.normalize())
            .map(IdentifierPattern::from)?;

        self.expect(TokenKind::Equals)?;
        let bound = self.parse_expression_block()?;

        // Could introduce a little rec keyword
        let bound = if let Expr::Lambda(pi, lambda) = bound {
            Expr::RecursiveLambda(
                pi,
                SelfReferential {
                    own_name: binder.clone().into(),
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
        let body = self.parse_expression_block()?;
        let body = self.extend_let_body(body, position)?;
        Ok(Expr::Let(
            self.span_from(position),
            Binding {
                binder,
                operator: binding_operator,
                bound: bound.into(),
                body: body.into(),
            },
        ))
    }

    // A `let` owns its own column: after `in`, everything to the end of the enclosing
    // block is the body, and the bound name stays in scope throughout. When the immediate
    // body is inline or lands on a following line at the `let`'s column, `parse_sequence`
    // already absorbs the whole tail (its reference column is the body's own column, which
    // equals the `let`'s). The gap is an *indented* body: `parse_block` closes at its
    // `Dedent`, so a continuation dedented back to the `let`'s column would otherwise become
    // a sibling of the whole `let` and lose sight of the binding. Here we fold any such
    // continuation back into the body, comparing against the `let`'s column rather than the
    // (deeper) body block's.
    fn extend_let_body(&mut self, body: Expr, let_position: SourceLocation) -> Result<Expr> {
        let continues = match self.remains() {
            // The closing `Dedent` of the indented body doubled as the separator, so the
            // continuation sits directly at the `let`'s column with no separator token.
            remains @ [t, ..]
                if self.is_expr_start(&t.kind)
                    && t.location().is_same_block(&let_position)
                    && !self.is_toplevel_start(remains) =>
            {
                true
            }
            // An explicit separator (`;` or a surviving newline) precedes the continuation.
            remains @ [t, u, ..]
                if t.is_sequence_separator()
                    && self.is_expr_start(&u.kind)
                    && u.location().is_same_block(&let_position)
                    && !self.is_toplevel_start(&remains[1..]) =>
            {
                self.advance(1);
                true
            }
            _ => false,
        };

        if continues {
            let and_then = self.parse_sequence()?;
            Ok(Expr::Sequence(
                *body.parse_info(),
                Sequence {
                    this: body.into(),
                    and_then: and_then.into(),
                },
            ))
        } else {
            Ok(body)
        }
    }

    fn parse_record(&mut self) -> Result<Expr> {
        let _t = self.trace();

        // The record starts at its `{`, not at the first thing inside it: a cursor on
        // the brace is on the record, and a diagnostic about the record should not
        // point past its own opening.
        let position = *self.peek()?.location();
        self.advance(1);
        self.strip_layout()?;

        // `{ base: Field := value }` is a record update.  A construction still
        // starts with the field label immediately followed by `:=`.
        let is_construction = matches!(
            self.remains(),
            [
                Token {
                    kind: TokenKind::Identifier(_),
                    ..
                },
                Token {
                    kind: TokenKind::Assign,
                    ..
                },
                ..
            ]
        );
        let base = if is_construction || self.peek()?.kind == TokenKind::RightBrace {
            None
        } else {
            let base = self.parse_expression(0)?;
            self.expect(TokenKind::Colon)?;
            self.strip_layout()?;
            Some(base)
        };

        // An update collects paths; a construction collects labelled initializers,
        // which keep the label's position.
        let mut fields = vec![];
        let mut initializers = vec![];
        while self.peek()?.kind != TokenKind::RightBrace {
            if base.is_some() {
                fields.push(self.parse_record_update_field()?);
            } else {
                initializers.push(self.parse_field_init()?);
            }
            self.strip_layout()?;
            if self.peek()?.kind == TokenKind::Semicolon {
                self.consume()?;
                self.strip_layout()?;
            }
        }

        self.expect(TokenKind::RightBrace)?;

        let info = self.span_from(position);
        Ok(match base {
            Some(base) => Expr::RecordUpdate(
                info,
                ast::RecordUpdate {
                    base: base.into(),
                    fields,
                    field_order: Vec::new(),
                },
            ),
            None => Expr::Record(info, Record::from_fields(&initializers)),
        })
    }

    fn parse_record_update_field(
        &mut self,
    ) -> Result<ast::RecordUpdateField<ParseInfo, IdentifierPattern<ParseInfo>>> {
        let (at, first) = self.identifier()?;
        let mut path = vec![Identifier::from_str(&first)];
        let mut path_at = vec![self.span_from(at)];
        while self.peek()?.kind == TokenKind::Period {
            self.consume()?;
            let (at, field) = self.identifier()?;
            path.push(Identifier::from_str(&field));
            path_at.push(self.span_from(at));
        }
        self.expect(TokenKind::Assign)?;
        // The value may drop onto an indented block, exactly as a declaration's
        // does: `Field :=` and then the value on the next line.
        let value = self.parse_block(|parser| parser.parse_expression(0))?;
        Ok(ast::RecordUpdateField {
            path,
            path_at,
            indices: Vec::new(),
            arities: Vec::new(),
            value: value.into(),
        })
    }

    fn parse_array(&mut self) -> Result<Expr> {
        let _t = self.trace();

        // The array starts at its `[`, for the same reason a record starts at its
        // brace.
        let position = *self.peek()?.location();
        self.advance(1);
        self.strip_layout()?;

        let mut elements = Vec::default();

        // Not sure this is entirely correct yet
        while self.peek()?.kind != TokenKind::RightBracket {
            let element = self.parse_expression(0)?;
            self.strip_layout()?;

            elements.push(element.into());

            if self.peek()?.kind == TokenKind::Semicolon {
                self.consume()?;
                self.strip_layout()?;
            }
        }

        self.expect(TokenKind::RightBracket)?;
        Ok(Expr::Array(self.span_from(position), Array { elements }))
    }

    /// A field initializer `Label := value`, with the label's own position: an
    /// editor asked about a label needs somewhere to point.
    fn parse_field_init(
        &mut self,
    ) -> Result<(
        ParseInfo,
        Identifier,
        Tree<ParseInfo, IdentifierPattern<ParseInfo>>,
    )> {
        let _t = self.trace();

        let (at, label) = self.identifier()?;
        let at = self.span_from(at);
        self.expect(TokenKind::Assign)?;

        // A field's value may drop onto an indented block of its own, the same way
        // a declaration's may: `Power :=` and then the value on the next line. It
        // is a block and not merely layout to strip, because what is written there
        // can consult the indentation it sits at -- a `deconstruct`'s arms line up
        // under it.
        let expr = self.parse_block(|parser| parser.parse_expression(0))?;

        Ok((at, Identifier::from_str(&label), expr.into()))
    }

    fn parse_lambda(&mut self) -> Result<Expr> {
        let _t = self.trace();

        self.expect(TokenKind::Keyword(Keyword::Lambda))?;

        let params = self.parse_parameter_list()?;

        let body = self.parse_block(|parser| parser.parse_sequence())?;

        let lambda = params.into_iter().rfold(body, |body, (pos, param)| {
            let parse_info = self.span_from(pos);
            Expr::Lambda(
                parse_info,
                Lambda {
                    parameter: param.into(),
                    body: body.into(),
                },
            )
        });

        Ok(lambda)
    }

    fn parse_parameter_list(
        &mut self,
    ) -> Result<Vec<(SourceLocation, Pattern<ParseInfo, IdentifierPath>)>> {
        let mut params = vec![];

        loop {
            match self.peek()?.clone() {
                Token {
                    kind: TokenKind::LeftParen,
                    position,
                    ..
                } => {
                    // (
                    self.advance(1);
                    params.push((position, self.parse_pattern()?.normalize()));
                    self.expect(TokenKind::RightParen)?;
                }

                Token {
                    kind: TokenKind::Identifier(id),
                    position,
                    ..
                } => {
                    self.advance(1);
                    params.push((
                        position,
                        Pattern::Bind(self.span_from(position), IdentifierPath::new(&id)),
                    ));
                }

                _otherwise => break,
            }
        }

        if params.is_empty() {
            Err(ParseError::ExpectedIdentifier(self.peek()?.clone()))?;
        }
        self.expect(TokenKind::Period)?;
        Ok(params)
    }

    /// Run `parse` with the parenthesis relaxation suspended.
    ///
    /// `(` delimits an expression, so layout inside it is noise and a continuation may
    /// hang left (see `parse_expr_infix`). `[` and `{` are different: their contents are
    /// newline-separated, so layout inside THEM is significant again, even when they sit
    /// inside parentheses.
    fn within_own_layout<T>(&mut self, parse: impl Fn(&mut Self) -> Result<T>) -> Result<T> {
        let outer = std::mem::take(&mut self.paren_depth);
        let parsed = parse(self);
        self.paren_depth = outer;
        parsed
    }

    fn is_expr_start(&self, t: &TokenKind) -> bool {
        matches!(
            t,
            TokenKind::Hole
                | TokenKind::Literal(..)
                | TokenKind::Identifier(..)
                | TokenKind::LeftBrace
                | TokenKind::LeftParen
                | TokenKind::Keyword(
                    Keyword::Lambda | Keyword::Let(..) | Keyword::Deconstruct | Keyword::If
                )
                | TokenKind::Interpolate(Interpolation::Interlude(..))
        )
    }

    fn is_toplevel_start(&self, remains: &[Token]) -> bool {
        match remains {
            [
                t,
                Token {
                    kind: TokenKind::Assign | TokenKind::TypeAscribe | TokenKind::TypeAssign,
                    ..
                },
                ..,
            ] if t.is_identifier() => true,
            _ => false,
        }
    }

    fn parse_sequence(&mut self) -> Result<Expr> {
        let _t = self.trace();

        let prefix = self.parse_expression(0)?;

        //tracing::trace!(
        //    "parse_sequence: prefix {prefix} @ {}--- remains {}",
        //    prefix.annotation().location,
        //    display_list(" ", &self.remains().iter().take(5).collect::<Vec<_>>())
        //);

        match self.remains() {
            remains @ [t, u, ..]
                if (t.is_sequence_separator()/*|| t.is_dedent()*/)
                    && self.is_expr_start(&u.kind)
                    && u.location().is_same_block(&prefix.parse_info().location)
                    && !self.is_toplevel_start(&remains[1..]) =>
            {
                // <NL> or ;
                self.advance(1);
                self.parse_subsequent(prefix)
            }

            // if ; then we cannot look at the column
            remains @ [t, u, ..]
                if (t.kind == TokenKind::Semicolon/*|| t.is_dedent()*/)
                    && self.is_expr_start(&u.kind)
                    && !self.is_toplevel_start(&remains[1..]) =>
            {
                // <NL> or ;
                self.advance(1);
                self.parse_subsequent(prefix)
            }

            remains @ [t, u, ..]
                if self.is_expr_start(&t.kind)
                    && t.location().is_same_block(&prefix.parse_info().location)
                    && !self.is_toplevel_start(&remains) =>
            {
                self.parse_subsequent(prefix)
            }

            _ => Ok(prefix),
        }
    }

    fn parse_subsequent(&mut self, this: Expr) -> Result<Expr> {
        let _t = self.trace();

        let and_then = self.parse_sequence()?;

        //tracing::trace!(
        //    "parse_subsequent: this {}, and_then {}",
        //    this.parse_info().location,
        //    and_then.parse_info().location
        //);

        Ok(Expr::Sequence(
            *this.parse_info(),
            Sequence {
                this: this.into(),
                and_then: and_then.into(),
            },
        ))
    }

    fn parse_expression(&mut self, precedence: usize) -> Result<Expr> {
        let _t = self.trace();

        let prefix = self.parse_expr_prefix()?;
        let expr_context = ExpressionContext::from_prefix(&prefix, precedence);
        self.parse_expr_infix(prefix, expr_context)
    }

    fn parse_expr_prefix(&mut self) -> Result<Expr> {
        let _t = self.trace();

        match self.remains() {
            [
                Token {
                    kind: TokenKind::Hole,
                    position,
                    ..
                },
                ..,
            ] => {
                let position = *position;
                self.advance(1);
                let info = self.span_from(position);
                // Keep the hole's span on the call: native panic lowering uses it
                // together with the enclosing-term metadata for runtime context.
                let file = crate::source_map::path_of(info.file)
                    .map(|path| path.display().to_string())
                    .unwrap_or_else(|| "<unknown>".to_owned());
                let message = format!(
                    "Unimplemented hole ??? at {file}:{}:{}",
                    position.row, position.column
                );
                Ok(Expr::Apply(
                    info,
                    Apply {
                        function: Expr::Variable(
                            info,
                            IdentifierPattern::from_path(
                                info,
                                IdentifierPath::new("Prelude").with_suffix("omg_wtf_bbq"),
                            ),
                        )
                        .into(),
                        argument: Expr::Constant(info, ast::Literal::Text(message)).into(),
                    },
                ))
            }
            [
                Token {
                    kind: TokenKind::Literal(literal),
                    position,
                    ..
                },
                ..,
            ] => {
                self.advance(1);
                self.parse_literal(literal, position)
            }

            [
                Token {
                    kind: TokenKind::Identifier(id),
                    position,
                    ..
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
            ] => self.within_own_layout(Self::parse_record),

            [
                Token {
                    kind: TokenKind::LeftBracket,
                    ..
                },
                ..,
            ] => self.within_own_layout(Self::parse_array),

            [t, ..] if t.is_keyword(Keyword::Lambda) => self.parse_lambda(),

            [
                Token {
                    kind: TokenKind::Keyword(Keyword::Let(op)),
                    ..
                },
                ..,
            ] => self.parse_local_binding(*op),

            [t, ..] if t.is_keyword(Keyword::Deconstruct) => self.parse_deconstruct_into(),

            [t, ..] if t.is_keyword(Keyword::If) => self.parse_if_then_else(),

            [
                Token {
                    kind: TokenKind::Keyword(Keyword::Not),
                    position,
                    ..
                },
                ..,
            ] => {
                // `not` is the sole prefix operator: `not e` desugars to an application
                // of the like-named builtin. The operand binds at `not`'s own precedence,
                // so tighter operators (`=`, comparisons, arithmetic) are drawn into it
                // while the looser `and`/`or`/`xor` stay outside (`not a and b` = `(not a) and b`).
                let position = *position;
                self.advance(1);
                let parse_info = self.span_from(position);
                let operand = self.parse_expression(Operator::Not.precedence())?;
                Ok(Expr::Apply(
                    parse_info,
                    Apply {
                        function: Expr::Variable(
                            parse_info,
                            IdentifierPattern::from_atom(parse_info, Operator::Not.term_name()),
                        )
                        .into(),
                        argument: operand.into(),
                    },
                ))
            }

            [
                Token {
                    kind: TokenKind::Minus,
                    position,
                    ..
                },
                ..,
            ] => {
                // Unary minus: prefix `-e` desugars to `negate e`. Only prefix position
                // reaches here -- a `-` after an operand is consumed as binary subtraction
                // by `parse_expr_infix` -- so the two never conflict. The operand binds at
                // `-`'s precedence, so `-a * b` = `-(a * b)` and `-a - b` = `(-a) - b`.
                let position = *position;
                self.advance(1);
                let parse_info = self.span_from(position);
                let operand = self.parse_expression(Operator::Minus.precedence())?;
                Ok(Expr::Apply(
                    parse_info,
                    Apply {
                        function: Expr::Variable(
                            parse_info,
                            IdentifierPattern::from_atom(parse_info, "negate"),
                        )
                        .into(),
                        argument: operand.into(),
                    },
                ))
            }

            [
                Token {
                    kind: TokenKind::Interpolate(Interpolation::Interlude(prelude)),
                    position,
                    ..
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
                self.paren_depth += 1;
                let expr = self.parse_expression(0);
                self.paren_depth -= 1;
                self.expect(TokenKind::RightParen)?;
                expr
            }

            _ => Err(self.fault(parser_name!())),
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
                | TokenKind::RightBracket
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

    /// Recognise an infix operator which continues on the following laid-out line.
    ///
    /// Keep this separate from precedence: the ordinary infix parser only accepts an
    /// operator which outranks its current context, while the tuple parser also needs
    /// to see another comma at the *same* precedence so it can extend one flat tuple.
    /// The boolean says that the layout token opened an indentation level which the
    /// caller must balance after parsing the continuation.
    fn laid_out_infix(
        &self,
        expr_context: ExpressionContext,
    ) -> Option<(Operator, SourceLocation, bool)> {
        let [layout, operator_token, operand, ..] = self.remains() else {
            return None;
        };

        let is_continuation_layout =
            layout.is_dedent() || layout.is_newline() || layout.is_indent();
        if !is_continuation_layout
            || operator_token.location().column >= expr_context.anchor_column
            || !Self::is_expr_prefix(&operand.kind)
        {
            return None;
        }

        Operator::try_from(&operator_token.kind)
            .map(|operator| (operator, *operator_token.location(), layout.is_indent()))
    }

    // All infices must be right of lhs.
    fn parse_expr_infix(&mut self, lhs: Expr, expr_context: ExpressionContext) -> Result<Expr> {
        let _t = self.trace();

        let terminals = [
            TokenKind::RightParen,
            TokenKind::Semicolon,
            TokenKind::Pipe,
            TokenKind::Assign,
            TokenKind::TypeAssign,
            TokenKind::Layout(Layout::Dedent),
            TokenKind::Keyword(Keyword::Let(BindingOperator::Applicative)),
            TokenKind::Keyword(Keyword::Let(BindingOperator::Monadic)),
            TokenKind::Keyword(Keyword::Let(BindingOperator::Identity)),
            TokenKind::Keyword(Keyword::In),
            TokenKind::Keyword(Keyword::Into),
            TokenKind::Keyword(Keyword::Then),
            TokenKind::Keyword(Keyword::Else),
            // A following declaration terminates the expression -- none of these
            // keywords can appear inside one. `Signature` was already here; the
            // rest were missing, so an expression directly before e.g. an `opaque`
            // declaration ran past it into the prefix parser's `otherwise` panic.
            TokenKind::Keyword(Keyword::Signature),
            TokenKind::Keyword(Keyword::Opaque),
            TokenKind::Keyword(Keyword::Module),
            TokenKind::Keyword(Keyword::Witness),
            TokenKind::Keyword(Keyword::Foreign),
            TokenKind::Keyword(Keyword::Confined),
            TokenKind::Keyword(Keyword::Unconfined),
            TokenKind::Keyword(Keyword::Use),
            TokenKind::End,
        ];

        let is_terminal = |t| terminals.contains(t);

        if let Some((operator, operator_position, borrowed_indent)) =
            self.laid_out_infix(expr_context)
            && operator.precedence() > expr_context.precedence
        {
            self.advance(2); // the layout token and the operator

            if !borrowed_indent {
                return self.parse_operator(lhs, operator, operator_position, expr_context);
            }

            let folded = self.parse_operator(lhs, operator, operator_position, expr_context)?;
            if self.peek()?.is_dedent() {
                self.advance(1); // balance the borrowed Indent
            }
            return self.parse_expr_infix(folded, expr_context);
        }

        match self.remains() {
            [t, ..] if t.is_dedent() && t.location().is_same_block(&lhs.parse_info().location) => {
                // Ded, paired with this:
                // self.advance(1); //the indent
                self.advance(1);
                Ok(lhs)
            }

            [t, ..] if is_terminal(&t.kind) => Ok(lhs),

            [t, u, ..] if t.is_layout() && is_terminal(&u.kind) => Ok(lhs),

            [t, ..] if let Some(operator) = Operator::try_from(&t.kind) => {
                // the operator
                self.advance(1);
                self.parse_operator(lhs, operator, *t.location(), expr_context)
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
                    && Operator::Juxtaposition.precedence() > expr_context.precedence
                    && (u.position.is_descendant_of(lhs.position())
                        // Inside parentheses the bracket already delimits the
                        // expression, so the offside rule does not have to: a
                        // continuation may hang LEFT of the function it applies to.
                        // This is what let a multi-line argument list be written
                        // `f (g\n  [ a\n    b\n  ]) h` instead of being bounced out to a
                        // `let`.
                        //
                        // `Indent` only. A `Newline` at the same level separates
                        // statements in a block that is genuinely there -- a lambda body
                        // inside parens -- and juxtaposing across it would turn two
                        // statements into an application.
                        || (t.is_indent() && self.paren_depth > 0)) =>
            {
                self.advance(1); //the indent
                self.parse_juxtaposed(lhs, expr_context)
            }

            // f x
            [t, u, ..]
                if Self::is_expr_prefix(&t.kind)
                    && t.position.is_descendant_of(lhs.position())
                    && Operator::Juxtaposition.precedence() > expr_context.precedence =>
            {
                self.parse_juxtaposed(lhs, expr_context)
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
        let mut interpolator = Interpolate::begin(pi, prelude);
        self.advance(1);

        loop {
            interpolator.expression(self.parse_expression(0)?);
            // The backtick?
            self.advance(1);
            let segment = self.consume()?.clone();
            let here = self.last_end();
            match &segment {
                Token {
                    kind: TokenKind::Interpolate(Interpolation::Interlude(literal)),
                    position,
                    ..
                } => interpolator.literal(ParseInfo::spanning(*position, here), literal.clone()),

                Token {
                    kind: TokenKind::Interpolate(Interpolation::Epilogue(literal)),
                    position,
                    ..
                } => {
                    let pi = ParseInfo::spanning(*position, here);
                    interpolator.literal(pi, literal.clone());
                    break Ok(Expr::Interpolate(pi, interpolator));
                }

                // Already consumed, so the fault has to be told what it was.
                unexpected => {
                    let (position, found) = (unexpected.position, unexpected.kind.clone());
                    break Err(self.fault_at(parser_name!(), position, found));
                }
            }
        }
    }

    fn parse_juxtaposed(&mut self, lhs: Expr, expr_context: ExpressionContext) -> Result<Expr> {
        let _t = self.trace();

        let rhs = self.parse_expression(Operator::Juxtaposition.precedence())?;

        // The application reaches from the function to the end of its argument. It
        // keeps the function's *start*, which is what the tree has always been keyed
        // on, and gains the extent of the whole call -- which is what a diagnostic
        // about the call should underline.
        let at = self.span_from(lhs.parse_info().location);

        self.parse_expr_infix(
            Expr::Apply(
                at,
                ast::Apply {
                    function: lhs.into(),
                    argument: rhs.into(),
                },
            ),
            expr_context,
        )
    }

    fn parse_literal(&mut self, literal: &Literal, position: &SourceLocation) -> Result<Expr> {
        Ok(Expr::Constant(
            self.span_from(*position),
            literal.clone().into(),
        ))
    }

    fn parse_variable(&mut self, id: &str, position: &SourceLocation) -> Result<Expr> {
        let parse_info = self.span_from(*position);
        Ok(Expr::Variable(
            parse_info,
            IdentifierPattern::from_atom(parse_info, id),
        ))
    }

    fn parse_operator(
        &mut self,
        lhs: Expr,
        operator: Operator,
        operator_position: SourceLocation,
        expr_context: ExpressionContext,
    ) -> Result<Expr> {
        let _t = self.trace();

        let computed_precedence = if operator.is_right_associative() {
            operator.precedence() - 1
        } else {
            operator.precedence()
        };

        if operator.precedence() > expr_context.precedence {
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
                    self.parse_expr_infix(lhs, expr_context)
                }

                Operator::Tuple => self.parse_tuple_expression(
                    lhs,
                    operator_position,
                    computed_precedence,
                    expr_context,
                ),

                _ => self.parse_operator_default(
                    lhs,
                    operator,
                    operator_position,
                    expr_context,
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
        expr_context: ExpressionContext,
    ) -> Result<Expr> {
        // The first `,` has already been consumed. Gather the comma-separated elements into one
        // flat tuple, each element parsed just tight enough that a `,` ends it (`computed_precedence`
        // is below tuple level). A parenthesised group arrives as one complete prefix and so counts
        // as a single element -- which is what keeps `1, (2, 3)` distinct from the flat `1, 2, 3`.
        let first_rhs = self.parse_expression(computed_precedence)?;
        let mut last_anchor_column = first_rhs.parse_info().location.column;
        let mut elements = vec![lhs.into(), first_rhs.into()];

        loop {
            let borrowed_indent = if matches!(self.peek()?.kind, TokenKind::Comma) {
                self.advance(1); // the `,`
                false
            } else {
                let element_context = ExpressionContext {
                    precedence: computed_precedence,
                    anchor_column: last_anchor_column,
                };
                let Some((Operator::Tuple, _operator_position, borrowed_indent)) =
                    self.laid_out_infix(element_context)
                else {
                    break;
                };
                self.advance(2); // the layout token and the `,`
                borrowed_indent
            };

            let element = self.parse_expression(computed_precedence)?;
            last_anchor_column = element.parse_info().location.column;
            elements.push(element.into());

            if borrowed_indent && self.peek()?.is_dedent() {
                self.advance(1); // balance the borrowed Indent
            }
        }
        self.parse_expr_infix(
            Expr::Tuple(self.span_from(operator_position), Tuple { elements }),
            expr_context,
        )
    }

    fn parse_select_operator(&mut self, lhs: Expr) -> Result<Expr> {
        let _t = self.trace();

        if let Expr::Variable(pi, id) = &lhs
            && !matches!(self.peek()?.kind, TokenKind::Literal(..))
        {
            self.parse_identifier_path_expr(*pi, id)
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

    fn parse_identifier_path_expr(
        &mut self,
        pi: ParseInfo,
        lhs: &IdentifierPattern<ParseInfo>,
    ) -> Result<Expr> {
        let _t = self.trace();

        let (_, rhs) = self.identifier()?;

        // The path grew, so its extent grows with it: `p.X.Y` is one name written
        // across three segments, and a cursor in any of them is inside all of it.
        // (The namer splits this into projections later, each keeping this span.)
        Ok(Expr::Variable(
            self.span_from(pi.location),
            lhs.with_appended_path_segment(rhs.as_str()),
        ))
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

            _ => return Err(self.fault(parser_name!())),
        };

        // The Id or Int literal
        self.advance(1);

        // The projection reaches from its base to the end of the field just read. It
        // keeps the base's *start*, which is what the tree has always been keyed on
        // -- `self.Requires.Strength` is two projections at one position -- and gains
        // the extent of the whole thing, which is what a cursor inside it is inside.
        let parse_info = self.span_from(lhs.parse_info().location);
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
        expr_context: ExpressionContext,
        computed_precedence: usize,
    ) -> Result<Expr> {
        let _t = self.trace();

        let parse_info = self.span_from(*lhs.position());
        let apply_lhs = Expr::Apply(
            parse_info,
            Apply {
                function: Expr::Variable(
                    self.span_from(operator_position),
                    IdentifierPattern::from_atom(parse_info, operator.term_name()),
                )
                .into(),
                argument: lhs.into(),
            },
        );

        let rhs = self.parse_expression(computed_precedence)?;
        self.parse_expr_infix(
            Expr::Apply(
                self.span_from(*rhs.position()),
                Apply {
                    function: apply_lhs.into(),
                    argument: rhs.into(),
                },
            ),
            expr_context,
        )
    }

    fn parse_type_signature(&mut self) -> Result<phase::TypeSignature<Parsed>> {
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

    fn parse_constraint_clause(&mut self) -> Result<Vec<phase::ConstraintExpression<Parsed>>> {
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
            .position(|t| matches!(t.kind, TokenKind::Assign | TokenKind::Layout(..)))
            .is_some_and(|p| {
                self.remains()[..p]
                    .iter()
                    .any(|t| t.kind == TokenKind::TypeConstraint)
            })
    }

    fn parse_type_constraint(&mut self) -> Result<phase::ConstraintExpression<Parsed>> {
        let _t = self.trace();

        let (pos, id) = self.identifier()?;

        let mut arguments = vec![];

        while matches!(
            self.peek()?.kind,
            TokenKind::Identifier(..) | TokenKind::LeftParen
        ) {
            if self.peek()?.is_identifier() {
                let (pos, id) = self.identifier()?;
                let pi = self.span_from(pos);
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
            annotation: self.span_from(pos),
            class: IdentifierPath::new(&id),
            parameters: arguments,
        })
    }

    fn parse_coproduct(&mut self) -> Result<CoproductDeclarator> {
        let _t = self.trace();

        let mut constructors = vec![self.parse_coproduct_constructor()?];

        // NB: do *not* unconditionally swallow a trailing `Dedent` here. When the
        // first constructor is indented and a `|` alternative dedents back before the
        // bar, the `is_constructor_separator` `Some(2)` case below already consumes the
        // `[<Dedent> |]` pair. A `Dedent` that is *not* followed by a bar instead closes
        // an enclosing block -- e.g. when this coproduct is the last member of an inline
        // `module X:` block -- and eating it would make that block never see its closer,
        // absorbing every following sibling declaration as one of its own members.
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

    fn parse_coproduct_constructor(&mut self) -> Result<CoproductConstructor> {
        let _t = self.trace();

        let (at, id) = self.identifier()?;
        let at = self.span_from(at);

        let mut signature = vec![];

        while matches!(
            self.peek()?.kind,
            TokenKind::Identifier(..) | TokenKind::LeftParen
        ) {
            signature.push(self.parse_type_expr_prefix()?);
        }

        Ok(CoproductConstructor {
            at,
            name: Identifier::from_str(&id),
            signature,
        })
    }

    fn parse_deconstruct_into(&mut self) -> Result<Expr> {
        let _t = self.trace();
        // deconstruct
        let _deconstruct = *self.consume()?.location();

        let scrutinee = self.parse_expression_block()?;

        self.expect(TokenKind::Keyword(Keyword::Into))?;

        // The clauses of one `deconstruct` all align their patterns at this column.
        // Prefer the opening `Indent`, which the lexer puts at the column the clause's
        // *line* began -- a leading comment (`(* why *) Cons x xs -> ...`) shifts the
        // first pattern token right without moving the clause. Falling back to the
        // token is for an unindented single-line `deconstruct`, and either way it is
        // taken from a token rather than the parsed pattern's annotation, since a tuple
        // pattern is annotated at its comma, not its start (`Cons x xs, Cons y ys`
        // would otherwise anchor on the comma).
        let opening = self.peek()?;
        let indent_column = opening.is_indent().then_some(opening.location().column);
        if indent_column.is_some() {
            self.advance(1);
        }
        let clause_column = match indent_column {
            Some(column) => column,
            None => self.peek()?.location().column,
        };

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
            // A `|` alternative whose pattern dedents to a shallower column than the
            // first clause belongs to an *enclosing* `deconstruct`: when a nested match
            // is the last thing inside an outer clause, the outer match's next `|`
            // arrives here as `[<Dedent> |]` and would otherwise be swallowed as one of
            // the inner match's clauses (turning an outer catch-all into a redundant
            // inner one). Stop so the outer parser claims it. The pattern token sits
            // just past the `|` (and any leading layout).
            let dedented_to_enclosing = self
                .remains()
                .get(separator)
                .is_some_and(|pattern_start| pattern_start.location().column < clause_column);
            if dedented_to_enclosing {
                break;
            }

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

    fn parse_match_clause(
        &mut self,
    ) -> Result<MatchClause<ParseInfo, IdentifierPattern<ParseInfo>>> {
        let _t = self.trace();

        let pattern = self.parse_pattern()?.normalize();

        self.expect(TokenKind::Arrow)?;
        let consequent = self.parse_expression_block()?;
        let parse_info = *pattern.annotation();
        Ok(MatchClause {
            pattern: pattern.map_id(&|id| IdentifierPattern::from_path(parse_info, id)),
            consequent: consequent.into(),
        })
    }

    fn parse_pattern(&mut self) -> Result<Pattern<ParseInfo, IdentifierPath>> {
        let _t = self.trace();

        let prefix = self.parse_pattern_prefix()?;
        self.parse_pattern_infix(prefix)
    }

    fn parse_pattern_prefix(&mut self) -> Result<Pattern<ParseInfo, IdentifierPath>> {
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
                    kind: TokenKind::LeftParen,
                    ..
                },
                ..,
            ] => {
                // (
                self.advance(1);

                let pattern = self.parse_pattern()?.normalize();
                self.expect(TokenKind::RightParen)?;
                Ok(pattern)
            }
            [
                Token {
                    kind: TokenKind::Literal(literal),
                    position,
                    ..
                },
                ..,
            ] => self.parse_literal_pattern(*position, literal),

            _ => Err(self.fault(parser_name!())),
        }
    }

    fn parse_pattern_infix(
        &mut self,
        lhs: Pattern<ParseInfo, IdentifierPath>,
    ) -> Result<Pattern<ParseInfo, IdentifierPath>> {
        let _t = self.trace();

        match self.remains() {
            [t, ..] if t.kind == TokenKind::Comma => {
                // Gather the comma-separated sub-patterns into one flat tuple, mirroring the value
                // side (`parse_tuple_expression`). A parenthesised group is a single prefix, so
                // `(a, b), c` binds the pair against a nested tuple rather than being flattened.
                let position = *t.location();
                let mut elements = vec![lhs];
                while matches!(self.peek()?.kind, TokenKind::Comma) {
                    self.advance(1); // the `,`
                    elements.push(self.parse_pattern_prefix()?);
                }
                Ok(Pattern::Tuple(
                    self.span_from(position),
                    TuplePattern { elements },
                ))
            }

            _otherwise => Ok(lhs),
        }
    }

    fn parse_constructor_pattern(&mut self) -> Result<Pattern<ParseInfo, IdentifierPath>> {
        let _t = self.trace();

        // There are nullary constructors
        let pos = *self.peek()?.location();
        let constructor = self.parse_identifier_path()?;
        let mut arguments = vec![];

        while !matches!(
            self.peek()?.kind,
            TokenKind::Arrow
                | TokenKind::Comma
                | TokenKind::RightBrace
                | TokenKind::Equals
                | TokenKind::RightParen
                | TokenKind::Semicolon
        ) {
            arguments.push(self.parse_pattern_prefix()?);
        }

        Ok(Pattern::Coproduct(
            self.span_from(pos),
            ConstructorPattern {
                constructor,
                arguments,
            },
        ))
    }

    fn parse_literal_pattern(
        &mut self,
        position: SourceLocation,
        literal: &Literal,
    ) -> Result<Pattern<ParseInfo, IdentifierPath>> {
        let _t = self.trace();

        // the literal
        self.advance(1);
        Ok(Pattern::Literally(
            self.span_from(position),
            literal.clone().into(),
        ))
    }

    fn parse_pattern_binder(&mut self) -> Result<Pattern<ParseInfo, IdentifierPath>> {
        let _t = self.trace();

        let (pos, id) = self.identifier()?;
        Ok(Pattern::Bind(self.span_from(pos), IdentifierPath::new(&id)))
    }

    fn parse_struct_pattern(&mut self) -> Result<Pattern<ParseInfo, IdentifierPath>> {
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

        fields.sort_by(|t, u| t.1.cmp(&u.1));

        Ok(Pattern::Struct(
            self.span_from(brace_location),
            StructPattern { fields },
        ))
    }

    fn parse_struct_pattern_field(
        &mut self,
    ) -> Result<(ParseInfo, Identifier, Pattern<ParseInfo, IdentifierPath>)> {
        let _t = self.trace();

        let (at, label) = self.identifier()?;
        let at = self.span_from(at);
        self.expect(TokenKind::Colon)?;
        let pattern = self.parse_pattern()?.normalize();
        Ok((at, Identifier::from_str(&label), pattern))
    }

    fn parse_if_then_else(&mut self) -> Result<Expr> {
        let _t = self.trace();

        let position = self.expect(TokenKind::Keyword(Keyword::If))?.position;

        let predicate = self.parse_expression_block()?;

        self.parse_block(|parser| {
            if parser.peek()?.is_newline() {
                parser.advance(1);
            }
            parser.expect(TokenKind::Keyword(Keyword::Then))?;

            let consequent = parser.parse_expression_block()?;

            if parser.peek()?.is_newline() {
                parser.advance(1);
            }

            parser.expect(TokenKind::Keyword(Keyword::Else))?;

            let alternate = parser.parse_expression_block()?;

            Ok(Expr::If(
                parser.span_from(position),
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
    id.chars().next().is_some_and(|c| c.is_uppercase())
}

impl Pattern<ParseInfo, IdentifierPath> {
    pub fn normalize(&self) -> Pattern<ParseInfo, IdentifierPath> {
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
                    elements: elements.iter().map(|p| p.normalize()).collect(),
                },
            ),

            Self::Struct(pi, StructPattern { fields }) => Self::Struct(
                *pi,
                StructPattern {
                    fields: fields
                        .iter()
                        .map(|(at, field, pattern)| (*at, field.clone(), pattern.normalize()))
                        .collect(),
                },
            ),

            Self::Literally(..) | Self::Bind(..) => self.clone(),
        }
    }
}

impl phase::TypeExpression<Parsed> {
    fn is_applicable(&self) -> bool {
        matches!(
            self,
            Self::Parameter(..) | Self::Constructor(..) | Self::Apply(..)
        )
    }
}

impl From<Literal> for ast::Literal {
    fn from(value: Literal) -> Self {
        match value {
            Literal::Integer(x) => ast::Literal::Int(x),
            Literal::Float(x) => ast::Literal::Float(x),
            Literal::Text(x) => ast::Literal::Text(x),
            Literal::Bool(x) => ast::Literal::Bool(x),
            Literal::Unit => ast::Literal::Unit,
            Literal::Char(x) => ast::Literal::Char(x),
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
        // File-free by design: this is also printed inside inferred-type dumps.
        // The file is surfaced only on the error path (see `Located`'s `Display`).
        let Self {
            location,
            end: _,
            file: _,
        } = self;
        write!(f, "{location}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::LexicalAnalyzer;

    fn parsed_value_bodies(source: &str) -> Vec<String> {
        let characters = source.chars().collect::<Vec<_>>();
        let mut lexer = LexicalAnalyzer::default();
        let tokens = lexer.tokenize(&characters);
        Parser::from_tokens(tokens)
            .parse_declaration_list()
            .expect("parses")
            .iter()
            .filter_map(|declaration| match declaration {
                Declaration::Value(_, value) => Some(value.declarator.body.to_string()),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn pipeline_and_composition_have_their_intended_associativity() {
        let bodies = parsed_value_bodies(
            "pipe := x |> f |> g\nforward := f >> g >> h\nbackward := f ∘ g ∘ h\n",
        );

        assert_eq!(
            bodies,
            vec![
                "((pipe_forward ((pipe_forward x) f)) g)",
                "((compose_forward ((compose_forward f) g)) h)",
                "((compose f) ((compose g) h))",
            ]
        );
    }

    #[test]
    fn pipeline_and_composition_rhs_align_under_their_first_operand() {
        let bodies = parsed_value_bodies(
            "result :=\n     input\n  |> decode\n  |> render\npipeline :=\n     decode\n  >> validate\n  >> render\ncomposition :=\n    render\n  ∘ validate\n  ∘ decode\n",
        );

        assert_eq!(bodies.len(), 3);
        assert!(bodies[0].contains("pipe_forward"));
        assert!(bodies[1].contains("compose_forward"));
        assert!(bodies[2].contains("compose"));
    }

    #[test]
    fn leading_commas_extend_one_flat_tuple() {
        let bodies = parsed_value_bodies(
            "flat :=\n     first\n  , second\n  , third\nnested :=\n     (first, second)\n  , third\n",
        );

        assert_eq!(
            bodies,
            vec!["(first, second, third)", "((first, second), third)"]
        );
    }

    #[test]
    fn malformed_constraint_separator_reports_expected_assignment() {
        let source =
            "insert :: ∀α β. Eq α. α -> β -> List (α, β) :=\n  λkey value. Cons (key, value)\n";
        let characters = source.chars().collect::<Vec<_>>();
        let mut lexer = LexicalAnalyzer::default();
        let tokens = lexer.tokenize(&characters);
        let mut parser = Parser::from_tokens(tokens);

        let error = parser.parse_declaration_list().unwrap_err();

        assert!(matches!(
            error,
            ParseError::Expected {
                expected: TokenKind::Assign,
                found: TokenKind::Period,
                ..
            }
        ));
    }

    /// A node knows how far it reaches, not only where it began -- which is what
    /// lets a diagnostic underline the call that failed rather than the name at the
    /// front of it, and what lets an editor answer about an expression a cursor is
    /// inside of.
    #[test]
    fn a_node_spans_what_it_was_parsed_from() {
        let source = "start :: Int -> Unit := λ_.\n  print_endline (add 1 2)\n";
        let characters = source.chars().collect::<Vec<_>>();
        let mut lexer = LexicalAnalyzer::default();
        let tokens = lexer.tokenize(&characters);
        let declarations = Parser::from_tokens(tokens)
            .parse_declaration_list()
            .expect("parses");

        // Walk to the outermost application of the body: `print_endline (add 1 2)`.
        let mut spans = Vec::new();
        for declaration in &declarations {
            if let Declaration::Value(_, value) = declaration {
                value.declarator.body.walk(&mut |node| {
                    if let Expr::Apply(at, _) = node {
                        spans.push((at.location, at.end));
                    }
                });
            }
        }

        let widest = spans
            .iter()
            .max_by_key(|(start, end)| end.column - start.column)
            .expect("an application");

        // `  print_endline (add 1 2)` -- from the `p` (column 3) to just past the
        // closing paren (column 26).
        assert_eq!(
            (widest.0.row, widest.0.column, widest.1.row, widest.1.column),
            (2, 3, 2, 26),
            "an application reaches from its function to the end of its argument"
        );
    }

    /// `p.X.Y` is not parsed as a projection -- it is one *name*, a dotted path, that
    /// the namer splits into projections later, each keeping this node's extent. So
    /// the extent has to cover the whole path: a cursor on any segment is inside the
    /// expression the path stands for, and an editor that replaced only the segment
    /// it sat on would write `p.X.deconstruct Y into`.
    #[test]
    fn a_dotted_path_spans_all_of_itself() {
        let source = "f :: Point -> Int := λp.\n  p.X.Y\n";
        let characters = source.chars().collect::<Vec<_>>();
        let mut lexer = LexicalAnalyzer::default();
        let tokens = lexer.tokenize(&characters);
        let declarations = Parser::from_tokens(tokens)
            .parse_declaration_list()
            .expect("parses");

        let mut widest = None;
        for declaration in &declarations {
            if let Declaration::Value(_, value) = declaration {
                value.declarator.body.walk(&mut |node| {
                    if let Expr::Variable(at, _) = node {
                        let span = (at.location.column, at.end.column);
                        if widest.is_none_or(|(_, end)| span.1 > end) {
                            widest = Some(span);
                        }
                    }
                });
            }
        }

        // `  p.X.Y` runs from column 3 to just past the `Y`.
        assert_eq!(widest, Some((3, 8)), "the path knows how far it reaches");
    }

    /// A syntax error costs its own declaration and no more: the parser picks up at
    /// the next one, so a file with two mistakes reports two.
    #[test]
    fn parsing_recovers_at_the_next_declaration() {
        let source = concat!(
            "first :: Int := 1 +\n",
            "\n",
            "second :: Int := 2\n",
            "\n",
            "third :: Text := \"ok\" ++\n",
            "\n",
            "fourth :: Int := 4\n",
        );
        let characters = source.chars().collect::<Vec<_>>();
        let mut lexer = LexicalAnalyzer::default();
        let tokens = lexer.tokenize(&characters);
        let (declarations, errors) =
            Parser::from_tokens(tokens).parse_declaration_list_recovering();

        assert_eq!(
            errors.len(),
            2,
            "one error per broken declaration: {errors:?}"
        );

        // What parsed is still there. `second` follows the first mistake and
        // `fourth` follows the second, so both sides of both errors were recovered.
        let names = declarations
            .iter()
            .filter_map(|declaration| match declaration {
                Declaration::Value(_, value) => Some(value.name.as_str().to_owned()),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(
            names.contains(&"second".to_owned()) && names.contains(&"fourth".to_owned()),
            "the declarations after each error still parsed: {names:?}"
        );
    }

    /// Lex and parse a declaration list, expecting it to fail.
    fn parse_failure(source: &str) -> ParseError {
        let characters = source.chars().collect::<Vec<_>>();
        let mut lexer = LexicalAnalyzer::default();
        let tokens = lexer.tokenize(&characters);
        Parser::from_tokens(tokens)
            .parse_declaration_list()
            .expect_err("expected this source to fail to parse")
    }

    #[test]
    fn parses_requirements_on_foreign_values() {
        let source = concat!(
            "foreign [ Browser; Platform.Dom ] document_title :: Unit -> Text\n",
            "foreign parse_int :: Text -> Int\n",
        );
        let characters = source.chars().collect::<Vec<_>>();
        let mut lexer = LexicalAnalyzer::default();
        let tokens = lexer.tokenize(&characters);
        let declarations = Parser::from_tokens(tokens)
            .parse_declaration_list()
            .expect("foreign values parse");

        let Declaration::Foreign(_, document_title) = &declarations[0] else {
            panic!("expected a foreign value");
        };
        assert_eq!(
            document_title
                .requirements
                .iter()
                .map(|requirement| requirement.name.to_string())
                .collect::<Vec<_>>(),
            ["Browser", "Platform.Dom"]
        );
        assert_eq!(
            declarations[0].to_string(),
            "foreign [ Browser; Platform.Dom ] document_title :: (Unit -> Text)"
        );

        let Declaration::Foreign(_, parse_int) = &declarations[1] else {
            panic!("expected a foreign value");
        };
        assert!(parse_int.requirements.is_empty());
    }

    #[test]
    fn rejects_empty_or_duplicate_requirement_sets() {
        assert!(matches!(
            parse_failure("foreign [] now :: Unit -> Int\n"),
            ParseError::EmptyRequirementSet { .. }
        ));
        assert!(matches!(
            parse_failure("foreign [ Timer; Timer ] now :: Unit -> Int\n"),
            ParseError::DuplicateRequirement { requirement, .. }
                if requirement == IdentifierPath::new("Timer")
        ));
    }

    #[test]
    fn rejects_requirements_on_foreign_types() {
        assert!(matches!(
            parse_failure("foreign [ MMap ] Raw_Mmap\n"),
            ParseError::RequirementSetOnForeignType { .. }
        ));
    }

    #[test]
    fn syntax_with_no_rule_faults_instead_of_panicking() {
        // Each of these lands in a different parse function's catch-all arm. The
        // point of the fault is that it *names* that function: these arms mark
        // syntax the parser does not handle as much as they mark bad input, and
        // the name is what tells a reader which of the two they are looking at.
        let cases = [
            ("declaration", ":= 3\n", "parse_declaration"),
            ("expression", "bad :: Int := :=\n", "parse_expr_prefix"),
            ("type", "bad :: := := 3\n", "parse_type_expr_prefix"),
            ("type declarator", "Bad ::= :=\n", "parse_type_declarator"),
            ("projection", "bad :: Int := (1, 2).+\n", "parse_projection"),
            (
                "pattern",
                "bad :: Int := deconstruct 1 into := -> 2\n",
                "parse_pattern_prefix",
            ),
        ];

        for (what, source, expected) in cases {
            match parse_failure(source) {
                ParseError::Fault { parser, .. } => {
                    assert_eq!(parser, expected, "wrong parse function named for {what}");
                }
                otherwise => panic!("{what}: expected a fault, got {otherwise:?}"),
            }
        }
    }

    #[test]
    fn a_fault_reports_where_it_is_and_what_follows() {
        let error = parse_failure("bad :: Int := :=\nnext :: Int := 1\n");

        let ParseError::Fault {
            at,
            found,
            lookahead,
            ..
        } = &error
        else {
            panic!("expected a fault, got {error:?}");
        };

        assert_eq!((at.location.row, at.location.column), (1, 15));
        assert_eq!(*found, TokenKind::Assign);
        // The tokens after the offending one, by kind -- enough of them to show the
        // shape of what the parser was standing in front of.
        assert!(
            lookahead.starts_with("<NL> next :: Int"),
            "unhelpful lookahead: {lookahead}"
        );
    }

    #[test]
    fn qualified_coproduct_payload_does_not_need_parentheses() {
        let source = "Wrapper ::= Make_Wrapper Namespace.Member\n";
        let characters = source.chars().collect::<Vec<_>>();
        let mut lexer = LexicalAnalyzer::default();
        let tokens = lexer.tokenize(&characters);
        let mut parser = Parser::from_tokens(tokens);

        let declarations = parser.parse_declaration_list().unwrap();

        assert_eq!(
            declarations[0].to_string(),
            "type Wrapper ::= Make_Wrapper(Namespace.Member)"
        );
    }

    #[test]
    fn parses_confinement_modifiers_on_representation_types() {
        let source = "confined foreign Raw_Buffer\nunconfined foreign Raw_Bytes\nunconfined opaque Locked ::= Locked Raw_Buffer\n";
        let characters = source.chars().collect::<Vec<_>>();
        let mut lexer = LexicalAnalyzer::default();
        let tokens = lexer.tokenize(&characters);
        let mut parser = Parser::from_tokens(tokens);

        let declarations = parser.parse_declaration_list().unwrap();
        let modifiers = declarations
            .iter()
            .map(|declaration| match declaration {
                Declaration::Type(_, declaration) => declaration.confinement,
                _ => panic!("expected type declaration"),
            })
            .collect::<Vec<_>>();

        assert_eq!(
            modifiers,
            vec![
                Some(ConfinementModifier::Confined),
                Some(ConfinementModifier::Unconfined),
                Some(ConfinementModifier::Unconfined),
            ]
        );
    }

    #[test]
    fn confinement_ascription_binds_tighter_than_type_arrow() {
        let source = "spawn :: ∀a. (IO a) : unconfined -> IO a := spawn_impl\n";
        let characters = source.chars().collect::<Vec<_>>();
        let mut lexer = LexicalAnalyzer::default();
        let tokens = lexer.tokenize(&characters);
        let mut parser = Parser::from_tokens(tokens);

        let declarations = parser.parse_declaration_list().unwrap();
        let Declaration::Value(_, declaration) = &declarations[0] else {
            panic!("expected value declaration");
        };
        let signature = declaration.declarator.type_signature.as_ref().unwrap();
        let TypeExpression::Arrow(_, arrow) = &signature.body else {
            panic!("expected outer function arrow");
        };
        assert!(matches!(
            arrow.domain.as_ref(),
            TypeExpression::ConfinementAscription(_, _, ConfinementModifier::Unconfined)
        ));
    }

    #[test]
    fn parses_record_update_with_semicolon_or_layout_fields() {
        let source = r#"
f := λr. { r: x := 10; y := 20 }
g := λr.
  { r:
      x := 30
      nested.y := 40
  }
"#;
        let characters = source.chars().collect::<Vec<_>>();
        let mut lexer = LexicalAnalyzer::default();
        let tokens = lexer.tokenize(&characters);
        let mut parser = Parser::from_tokens(tokens);

        let declarations = parser.parse_declaration_list().unwrap();
        assert_eq!(declarations.len(), 2);
        assert!(declarations[0].to_string().contains(": x :="));
        assert!(declarations[1].to_string().contains("nested.y := 40"));
    }

    /// A field's value may drop onto an indented block, the same way a
    /// declaration's may. It is a *block* and not merely layout to be discarded,
    /// because what is written there consults the indentation it sits at: the arms
    /// of the `deconstruct` below line up under the field that holds it.
    #[test]
    fn parses_a_field_whose_value_opens_a_block() {
        let source = r#"
origin :=
  { X :=
      2
    Power :=
      { Strength := 7
        Vitality := 9
      }
    Chosen := λn.
      deconstruct n into
        0 -> 100
      | _ -> n
  }
updated := λr.
  { r: Depth :=
      41 + 1
  }
"#;
        let characters = source.chars().collect::<Vec<_>>();
        let mut lexer = LexicalAnalyzer::default();
        let tokens = lexer.tokenize(&characters);
        let mut parser = Parser::from_tokens(tokens);

        let declarations = parser.parse_declaration_list().unwrap();
        assert_eq!(declarations.len(), 2);

        let record = declarations[0].to_string();
        for field in ["X: 2", "Power: {", "Strength: 7", "Chosen: λn.", "0 -> 100"] {
            assert!(record.contains(field), "lost `{field}` from {record}");
        }
        assert!(declarations[1].to_string().contains("Depth"));
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
