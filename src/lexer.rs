use std::fmt;

#[derive(Debug)]
pub struct LexicalAnalyzer {
    location: SourceLocation,
    indentation_level: u32,
    indentation: Vec<u32>,
    output: Vec<Token>,
}

impl LexicalAnalyzer {
    pub fn tokens(&self) -> &[Token] {
        &self.output
    }

    pub fn tokenize(&mut self, mut input: &[char]) -> &[Token] {
        loop {
            input = match input {
                [c, ..] if c.is_whitespace() => self.scan_whitespace(input),
                ['(', '*', ..] => self.scan_block_comment(input),
                [c, remains @ ..] if is_special_symbol(*c) => {
                    self.emit(1, TokenKind::decode_reserved_words(c.to_string()), remains)
                }
                prefix @ [c, ..] if is_identifier_prefix(*c) => self.scan_identifier(prefix),
                prefix @ [c, ..] if is_number_prefix(*c) => self.scan_number(prefix),
                ['"', remains @ ..] => self.scan_text_literal(remains),

                [':', ':', '=', remains @ ..] => self.emit(3, TokenKind::TypeAssign, remains),
                [':', '=', remains @ ..] => self.emit(2, TokenKind::Assign, remains),
                [':', ':', remains @ ..] => self.emit(2, TokenKind::TypeAscribe, remains),
                ['-', '>', remains @ ..] => self.emit(2, TokenKind::Arrow, remains),
                ['|', '-', remains @ ..] => self.emit(2, TokenKind::TypeConstraint, remains),

                ['>', '=', remains @ ..] => self.emit(2, TokenKind::Gte, remains),
                ['<', '=', remains @ ..] => self.emit(2, TokenKind::Lte, remains),
                ['>', remains @ ..] => self.emit(1, TokenKind::Gt, remains),
                ['<', remains @ ..] => self.emit(1, TokenKind::Lt, remains),

                ['=', remains @ ..] => self.emit(1, TokenKind::Equals, remains),
                [',', remains @ ..] => self.emit(1, TokenKind::Comma, remains),
                ['(', ')', remains @ ..] => {
                    self.emit(2, TokenKind::Literal(Literal::Unit), remains)
                }
                ['(', remains @ ..] => self.emit(1, TokenKind::LeftParen, remains),
                [')', remains @ ..] => self.emit(1, TokenKind::RightParen, remains),
                ['{', remains @ ..] => self.emit(1, TokenKind::LeftBrace, remains),
                ['}', remains @ ..] => self.emit(1, TokenKind::RightBrace, remains),
                ['_', remains @ ..] => self.emit(1, TokenKind::Underscore, remains),
                ['|', remains @ ..] => self.emit(1, TokenKind::Pipe, remains),
                [';', remains @ ..] => self.emit(1, TokenKind::Semicolon, remains),
                [':', remains @ ..] => self.emit(1, TokenKind::Colon, remains),
                ['.', remains @ ..] => self.emit(1, TokenKind::Period, remains),

                ['+', remains @ ..] => self.emit(1, TokenKind::Plus, remains),
                ['-', remains @ ..] => self.emit(1, TokenKind::Minus, remains),
                ['*', remains @ ..] => self.emit(1, TokenKind::Star, remains),
                ['/', remains @ ..] => self.emit(1, TokenKind::Slash, remains),
                ['%', remains @ ..] => self.emit(1, TokenKind::Percent, remains),

                [c, ..] => panic!("{c}"),

                [] => {
                    self.emit(0, TokenKind::End, &[]);
                    break &self.output;
                }
            };
        }
    }

    fn scan_block_comment<'a>(&mut self, mut remains: &'a [char]) -> &'a [char] {
        while let Some(pos) = remains.iter().position(|&c| c == '*') {
            if remains[pos..].len() > 1 {
                self.compute_location(remains, pos);
                if remains[pos + 1] == ')' {
                    return &remains[(pos + 2)..];
                }
                remains = &remains[pos + 2..];
            }
        }

        &remains[..0]
    }

    fn compute_location(&mut self, remains: &[char], pos: usize) {
        let new_location = self.compute_next_location(&remains[..=pos + 1]);
        self.update_location(new_location);
    }

    fn scan_identifier<'a>(&mut self, input: &'a [char]) -> &'a [char] {
        let (prefix, remains) = if let Some(end) = input[1..]
            .iter()
            .position(|c| !is_identifier_continuation(*c))
        {
            input.split_at(end + 1)
        } else {
            (input, &input[..0])
        };

        let identifier = prefix.iter().collect::<String>();
        self.emit(
            identifier.len() as u32,
            TokenKind::decode_reserved_words(identifier),
            remains,
        )
    }

    fn scan_text_literal<'a>(&mut self, input: &'a [char]) -> &'a [char] {
        // This pattern repeats itself a lot.
        // Can I use split?
        let (prefix, mut remains) =
            if let Some(end) = input.iter().position(|&c| c == '"' || c == '`') {
                input.split_at(end)
            } else {
                (input, &input[..0])
            };

        let mut image = prefix.iter().collect::<String>();
        let mut length = image.len() as u32;

        if matches!(remains, ['"', ..]) {
            self.emit(
                length,
                TokenKind::Literal(Literal::Text(image)),
                &remains[1..],
            )
        } else {
            loop {
                if remains.is_empty() {
                    break remains;
                } else {
                    println!("scan_text_literal: {:?}", &remains[..4]);
                }

                remains = self.emit(
                    length,
                    TokenKind::Interpolate(Interpolation::Interlude(Literal::Text(image))),
                    &remains[1..],
                );

                let (quoted_expression, remains1) =
                    if let Some(end) = remains.iter().position(|&c| c == '`') {
                        (&remains[..end], &remains[end + 1..])
                    } else {
                        (remains, &remains[..0])
                    };

                self.tokenize(quoted_expression);

                let (literal, remains1) =
                    if let Some(end) = remains1.iter().position(|&c| c == '"' || c == '`') {
                        remains1.split_at(end)
                    } else {
                        (remains1, &remains1[..0])
                    };

                image = literal.iter().collect::<String>();
                length = image.len() as u32;

                if matches!(remains1, ['"', ..]) {
                    break self.emit(
                        image.len() as u32,
                        TokenKind::Interpolate(Interpolation::Epilogue(Literal::Text(image))),
                        &remains1[1..],
                    );
                }

                remains = remains1;
            }
        }
    }

    fn emit<'a>(&mut self, length: u32, token_type: TokenKind, remains: &'a [char]) -> &'a [char] {
        self.output.push(Token {
            kind: token_type,
            position: self.location,
        });
        self.location.move_right(length);
        remains
    }

    // This ought to merge itself with comments
    fn scan_whitespace<'a>(&mut self, input: &'a [char]) -> &'a [char] {
        let (whitespace_prefix, remains) =
            input.split_at(input.iter().take_while(|c| c.is_whitespace()).count());

        let next_location = self.compute_next_location(whitespace_prefix);
        self.update_location(next_location);

        remains
    }

    fn compute_next_location(&self, whitespace: &[char]) -> SourceLocation {
        let mut next_location = self.location;

        for c in whitespace {
            match c {
                '\n' => next_location.new_line(),
                _c => next_location.move_right(1),
            }
        }

        next_location
    }

    fn update_location(&mut self, next: SourceLocation) {
        if next.is_below(&self.location) {
            if next.is_left_of(self.indentation_level) {
                self.dedent_and_emit(next);
                // Yes?
                //                self.emit_layout(next, Layout::Newline);
            } else if next.is_right_of(self.indentation_level) {
                self.indent_and_emit(next);
            } else {
                self.emit_layout(next, Layout::Newline);
            }
        }

        self.location = next;
    }

    fn dedent_and_emit(&mut self, next: SourceLocation) {
        if next.is_left_of(self.indentation_level) {
            self.indentation_level = self.indentation.pop().unwrap();
            self.emit_layout(next.at_column(self.indentation_level), Layout::Dedent);
            self.dedent_and_emit(next);
        }
    }

    fn indent_and_emit(&mut self, next: SourceLocation) {
        self.indentation.push(self.indentation_level);
        self.indentation_level = next.column;
        self.emit_layout(next, Layout::Indent);
    }

    // Which location is the location of an Indent or Dedent?
    fn emit_layout(&mut self, location: SourceLocation, indentation: Layout) {
        if let Some(last) = self.output.last_mut() {
            if last.kind == TokenKind::Layout(Layout::Newline) {
                *last = Token {
                    kind: TokenKind::Layout(indentation),
                    position: location,
                };
            } else {
                self.output.push(Token {
                    kind: TokenKind::Layout(indentation),
                    position: location,
                });
            }
        }
    }

    fn scan_number<'a>(&mut self, prefix: &'a [char]) -> &'a [char] {
        let (prefix, remains) =
            prefix.split_at(prefix.iter().take_while(|c| c.is_ascii_digit()).count());

        // This has to be able to fail the tokenization here
        let num = prefix.iter().collect::<String>().parse().unwrap();

        self.emit(
            prefix.len() as u32,
            TokenKind::Literal(Literal::Integer(num)),
            remains,
        );

        remains
    }
}

const fn is_special_symbol(c: char) -> bool {
    matches!(c, '∀' | 'λ')
}

const fn is_number_prefix(c: char) -> bool {
    c.is_ascii_digit()
}

fn is_identifier_prefix(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

fn is_identifier_continuation(c: char) -> bool {
    c.is_alphabetic() || c == '_' || c.is_numeric()
}

impl Default for LexicalAnalyzer {
    fn default() -> Self {
        let location = SourceLocation::default();
        Self {
            location,
            indentation_level: location.column,
            indentation: Vec::default(),
            output: Vec::default(), // This could actually be something a lot bigger.
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct SourceLocation {
    pub row: u32,
    pub column: u32,
}

impl SourceLocation {
    pub const fn new(row: u32, column: u32) -> Self {
        Self { row, column }
    }

    const fn move_right(&mut self, delta: u32) {
        self.column += delta;
    }

    const fn at_column(self, column: u32) -> Self {
        Self {
            row: self.row,
            column,
        }
    }

    const fn new_line(&mut self) {
        self.row += 1;
        self.column = 1;
    }

    pub const fn is_left_of(&self, indentation_level: u32) -> bool {
        self.column < indentation_level
    }

    pub const fn is_right_of(&self, indentation_level: u32) -> bool {
        self.column > indentation_level
    }

    pub const fn is_below(&self, rhs: &Self) -> bool {
        self.row > rhs.row
    }

    pub const fn is_same_block(&self, rhs: &Self) -> bool {
        self.column == rhs.column
    }

    pub const fn is_descendant_of(&self, rhs: &Self) -> bool {
        self.column > rhs.column && self.row >= rhs.row
    }
}

impl Default for SourceLocation {
    fn default() -> Self {
        Self { row: 1, column: 1 }
    }
}

// Flatten this?
// What does this hierarchy buy me?
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    Equals,         // =
    TypeAssign,     // ::=
    TypeAscribe,    // ::
    TypeConstraint, // |-
    Assign,         // :=
    Arrow,          // ->
    Comma,          // ,
    LeftParen,      // (
    RightParen,     // )
    LeftBrace,      // {
    RightBrace,     // }
    Underscore,     // _
    Pipe,           // |
    DoubleQuote,    // "
    SingleQuote,    // '
    Colon,          // :
    Semicolon,      // ;
    Period,         // .
    Plus,           // +
    Minus,          // -
    Star,           // *
    Slash,          // /
    Percent,        // %
    Gte,            // >=
    Lte,            // <=
    Gt,             // >
    Lt,             // <

    Identifier(String),

    Keyword(Keyword),
    Literal(Literal),

    Interpolate(Interpolation),

    Layout(Layout),
    End,
}

impl TokenKind {
    fn decode_reserved_words(id: String) -> Self {
        Keyword::try_from_identifier(&id).map_or_else(
            || {
                id.parse::<bool>().map_or_else(
                    |_| Self::Identifier(id),
                    |x| Self::Literal(Literal::Bool(x)),
                )
            },
            Self::Keyword,
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Interpolation {
    Interlude(Literal),
    Epilogue(Literal),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Operator {
    Plus,
    Minus,
    Times,
    Division,
    Modulo,

    Equals,
    Gte,
    Lte,
    Gt,
    Lt,

    Tuple,
    Select,

    And,
    Or,
    Xor,

    Not,

    Juxtaposition,

    Ascribe,
}

impl Operator {
    pub const fn is_defined(token: &TokenKind) -> bool {
        Self::try_from(token).is_some()
    }

    pub const fn try_from(token: &TokenKind) -> Option<Self> {
        match token {
            TokenKind::Equals => Some(Self::Equals),
            TokenKind::Plus => Some(Self::Plus),
            TokenKind::Minus => Some(Self::Minus),
            TokenKind::Star => Some(Self::Times),
            TokenKind::Slash => Some(Self::Division),
            TokenKind::Percent => Some(Self::Modulo),
            TokenKind::Gte => Some(Self::Gte),
            TokenKind::Lte => Some(Self::Lte),
            TokenKind::Gt => Some(Self::Gt),
            TokenKind::Lt => Some(Self::Lt),
            TokenKind::Comma => Some(Self::Tuple),
            TokenKind::Period => Some(Self::Select),
            TokenKind::Keyword(Keyword::And) => Some(Self::And),
            TokenKind::Keyword(Keyword::Or) => Some(Self::Or),
            TokenKind::Keyword(Keyword::Xor) => Some(Self::Xor),
            TokenKind::Keyword(Keyword::Not) => Some(Self::Not),
            TokenKind::TypeAscribe => Some(Self::Ascribe),
            _otherwise => None,
        }
    }

    pub const fn is_right_associative(&self) -> bool {
        matches!(self, Self::Tuple)
    }

    pub const fn precedence(&self) -> usize {
        match self {
            Self::Select => 26,
            Self::Juxtaposition => 25,

            Self::Times | Self::Division | Self::Modulo => 16,
            Self::Plus | Self::Minus => 15,

            Self::Tuple => 14,

            Self::Equals | Self::Gte | Self::Lte | Self::Gt | Self::Lt => 13,
            Self::Not => 12,

            Self::And => 11,
            Self::Xor | Self::Or => 10,

            Self::Ascribe => 8,
        }
    }

    pub const fn name(&self) -> &str {
        // These mappings are highly dubious
        match self {
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Times => "*",
            Self::Division => "/",
            Self::Modulo => "%",

            Self::Equals => "=",
            Self::Gte => ">=",
            Self::Lte => "<=",
            Self::Gt => ">",
            Self::Lt => "<",

            Self::Tuple => ",",
            Self::Select => ".",

            Self::And => "and",
            Self::Or => "or",
            Self::Xor => "xor",
            Self::Not => "not",

            Self::Juxtaposition => "ap",
            Self::Ascribe => "::",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Layout {
    Indent,
    Dedent,
    Newline,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Keyword {
    Let,
    In,

    If,
    Then,
    Else,

    Struct,
    Coproduct,
    Alias,
    Module,
    Use,

    Lambda,
    Forall,

    Deconstruct,
    Into,

    And,
    Or,
    Xor,
    Not,

    Where,

    Signature,
    Witness,
}

impl Keyword {
    fn try_from_identifier(id: &str) -> Option<Self> {
        match id {
            "let" => Some(Self::Let),
            "in" => Some(Self::In),
            "if" => Some(Self::If),
            "then" => Some(Self::Then),
            "else" => Some(Self::Else),
            "struct" => Some(Self::Struct),
            "coproduct" => Some(Self::Coproduct),
            "alias" => Some(Self::Alias),
            "module" => Some(Self::Module),
            "use" => Some(Self::Use),
            "lambda" | "λ" => Some(Self::Lambda),
            "and" => Some(Self::And),
            "or" => Some(Self::Or),
            "xor" => Some(Self::Xor),
            "not" => Some(Self::Not),
            "forall" | "∀" => Some(Self::Forall),
            "deconstruct" => Some(Self::Deconstruct),
            "into" => Some(Self::Into),
            "where" => Some(Self::Where),
            "signature" => Some(Self::Signature),
            "witness" => Some(Self::Witness),
            _otherwise => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    Integer(i64),
    Text(String),
    Bool(bool),
    Unit,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub position: SourceLocation,
}

impl Token {
    pub const fn is_identifier(&self) -> bool {
        matches!(self.kind, TokenKind::Identifier(..))
    }

    pub const fn is_indent(&self) -> bool {
        matches!(self.kind, TokenKind::Layout(Layout::Indent))
    }

    pub const fn is_newline(&self) -> bool {
        matches!(self.kind, TokenKind::Layout(Layout::Newline))
    }

    pub const fn is_sequence_separator(&self) -> bool {
        matches!(
            self.kind,
            TokenKind::Layout(Layout::Newline) | TokenKind::Semicolon
        )
    }

    pub const fn is_dedent(&self) -> bool {
        matches!(self.kind, TokenKind::Layout(Layout::Dedent))
    }

    pub fn is_keyword(&self, keyword: Keyword) -> bool {
        self.kind == TokenKind::Keyword(keyword)
    }

    pub const fn location(&self) -> &SourceLocation {
        &self.position
    }

    pub const fn is_layout(&self) -> bool {
        matches!(self.kind, TokenKind::Layout(..))
    }

    pub const fn is_literal(&self) -> bool {
        matches!(self.kind, TokenKind::Literal(..))
    }

    pub const fn is_end(&self) -> bool {
        matches!(self.kind, TokenKind::End)
    }
}

impl fmt::Display for Layout {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Indent => write!(f, "<Ind>"),
            Self::Dedent => write!(f, "<Ded>"),
            Self::Newline => write!(f, "<NL>"),
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{} {}>", self.position, self.kind)
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Equals => write!(f, "="),
            Self::TypeAssign => write!(f, "::="),
            Self::TypeAscribe => write!(f, "::"),
            Self::TypeConstraint => write!(f, "|-"),
            Self::Assign => write!(f, ":="),
            Self::Arrow => write!(f, "->"),
            Self::Comma => write!(f, ","),
            Self::LeftParen => write!(f, "("),
            Self::RightParen => write!(f, ")"),
            Self::LeftBrace => write!(f, "{{"),
            Self::RightBrace => write!(f, "}}"),
            Self::Underscore => write!(f, "_"),
            Self::Pipe => write!(f, "|"),
            Self::DoubleQuote => write!(f, "\""),
            Self::SingleQuote => write!(f, "'"),
            Self::Colon => write!(f, ":"),
            Self::Semicolon => write!(f, ";"),
            Self::Period => write!(f, "."),
            Self::Plus => write!(f, "+"),
            Self::Minus => write!(f, "-"),
            Self::Star => write!(f, "*"),
            Self::Slash => write!(f, "/"),
            Self::Percent => write!(f, "%"),
            Self::Gte => write!(f, ">="),
            Self::Lte => write!(f, "<="),
            Self::Gt => write!(f, ">"),
            Self::Lt => write!(f, "<"),
            Self::Identifier(id) => write!(f, "{id}"),
            Self::Keyword(keyword) => write!(f, "{keyword}"),
            Self::Literal(literal) => write!(f, "{literal}"),
            Self::Interpolate(prefix) => write!(f, "{prefix}`"),
            Self::Layout(layout) => write!(f, "{layout}"),
            Self::End => write!(f, "°"),
        }
    }
}

impl fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { row, column } = self;
        write!(f, "{row}:{column}")
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Integer(x) => write!(f, "{x}"),
            Self::Text(x) => write!(f, "{x}"),
            Self::Bool(x) => write!(f, "{x}"),
            Self::Unit => write!(f, "()"),
        }
    }
}

impl fmt::Display for Interpolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Interlude(literal) => write!(f, "|{literal}"),
            Self::Epilogue(literal) => write!(f, "{literal}|"),
        }
    }
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Plus => write!(f, "+"),
            Self::Minus => write!(f, "-"),
            Self::Times => write!(f, "*"),
            Self::Division => write!(f, "/"),
            Self::Modulo => write!(f, "%"),

            Self::Equals => write!(f, "="),

            Self::Gte => write!(f, ">="),
            Self::Lte => write!(f, "<="),
            Self::Gt => write!(f, ">"),
            Self::Lt => write!(f, "<"),

            Self::Tuple => write!(f, ","),
            Self::Select => write!(f, "."),

            Self::And => write!(f, "and"),
            Self::Or => write!(f, "or"),
            Self::Xor => write!(f, "xor"),
            Self::Not => write!(f, "not"),

            Self::Juxtaposition => write!(f, "ap"),
            Self::Ascribe => write!(f, "::"),
        }
    }
}

impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Let => write!(f, "Let"),
            Self::In => write!(f, "In"),
            Self::If => write!(f, "If"),
            Self::Then => write!(f, "Then"),
            Self::Else => write!(f, "Else"),
            Self::Struct => write!(f, "Struct"),
            Self::Coproduct => write!(f, "Coproduct"),
            Self::Alias => write!(f, "Alias"),
            Self::Module => write!(f, "Module"),
            Self::Use => write!(f, "Use"),
            Self::Lambda => write!(f, "Lambda"),
            Self::And => write!(f, "And"),
            Self::Or => write!(f, "Or"),
            Self::Xor => write!(f, "Xor"),
            Self::Not => write!(f, "Not"),
            Self::Forall => write!(f, "Forall"),
            Self::Deconstruct => write!(f, "Deconstruct"),
            Self::Into => write!(f, "Into"),
            Self::Where => write!(f, "Where"),
            Self::Signature => write!(f, "Signature"),
            Self::Witness => write!(f, "Witness"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::LexicalAnalyzer;

    #[test]
    fn lexington() {
        let mut lexer = LexicalAnalyzer::default();
        let input = include_str!("../examples/3.txt");

        let tokens = lexer.tokenize(&input.chars().collect::<Vec<_>>());
        for crate::lexer::Token { kind, position } in tokens {
            println!("[{position}] {kind:?}");
        }
    }
}
