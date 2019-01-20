use mltt_span::FileSpan;

/// A tag that makes it easier to remember what type of token this is
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenTag {
    LineComment,
    LineDoc,
    Symbol,
    Delimiter,
    Identifier,
    StringLiteral,
    CharLiteral,
    IntLiteral,
    FloatLiteral,
}

/// A token in the source file, to be emitted by the `Lexer`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token<'file> {
    /// The token tag
    pub tag: TokenTag,
    /// The slice of source code that produced the token
    pub slice: &'file str,
    /// The span in the source code
    pub span: FileSpan,
}
