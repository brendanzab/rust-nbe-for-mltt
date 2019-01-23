use mltt_span::FileSpan;

/// A tag that makes it easier to remember what type of token this is
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Whitespace,
    LineComment,
    LineDoc,

    Keyword,
    Symbol,
    Identifier,
    StringLiteral,
    CharLiteral,
    IntLiteral,
    FloatLiteral,

    BSlash,
    Caret,
    Colon,
    Dot,
    Equals,
    RArrow,
    RFatArrow,

    Comma,
    Semicolon,

    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
}

/// A token in the source file, to be emitted by the `Lexer`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token<'file> {
    /// The token kind
    pub kind: TokenKind,
    /// The slice of source code that produced the token
    pub slice: &'file str,
    /// The span in the source code
    pub span: FileSpan,
}

impl Token<'_> {
    pub fn is_whitespace(&self) -> bool {
        self.kind == TokenKind::Whitespace || self.kind == TokenKind::LineComment
    }

    pub fn is_keyword(&self, slice: &str) -> bool {
        self.kind == TokenKind::Keyword && self.slice == slice
    }
}
