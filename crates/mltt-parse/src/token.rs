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

impl Token<'_> {
    pub fn is_delimiter(&self, slice: &str) -> bool {
        self.tag == TokenTag::Delimiter && self.slice == slice
    }

    pub fn is_symbol(&self, slice: &str) -> bool {
        self.tag == TokenTag::Symbol && self.slice == slice
    }

    pub fn is_identifier(&self, slice: &str) -> bool {
        self.tag == TokenTag::Identifier && self.slice == slice
    }
}
