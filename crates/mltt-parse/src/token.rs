use mltt_concrete::SpannedString;
use mltt_span::{FileId, FileSpan, Span};
use std::fmt;

/// A kind of delimiter.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum DelimKind {
    /// A round parenthesis: `(` or `)`.
    Paren,
    /// A curly brace: `{` or `}`.
    Brace,
    /// A square bracket: `[` or `]`.
    Bracket,
}

/// A tag that makes it easier to remember what type of token this is.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Error,

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

    Caret,
    Colon,
    Dot,
    Equals,
    Question,
    RArrow,
    RFatArrow,

    Comma,
    Semicolon,

    Open(DelimKind),
    Close(DelimKind),
}

/// A token in the source file, to be emitted by the `Lexer`.
#[derive(Clone, PartialEq, Eq)]
pub struct Token<'file> {
    /// The token kind.
    pub kind: TokenKind,
    /// The source code that produced the token.
    pub src: SpannedString<'file>,
}

impl<'file> Token<'file> {
    pub fn span(&self) -> Span {
        self.src.span()
    }

    pub fn file_span(&self, file_id: FileId) -> FileSpan {
        FileSpan::new(file_id, self.span())
    }

    pub fn is_whitespace(&self) -> bool {
        self.kind == TokenKind::Whitespace || self.kind == TokenKind::LineComment
    }

    pub fn is_keyword(&self, slice: &str) -> bool {
        self.kind == TokenKind::Keyword && self.src.slice == slice
    }
}

impl fmt::Debug for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{kind:?}@{src:?}", kind = self.kind, src = self.src)
    }
}
