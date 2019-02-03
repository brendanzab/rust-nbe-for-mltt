use pretty::{BoxDoc, Doc};

pub mod concrete;
pub mod raw;

/// The kind of literal
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LiteralKind {
    /// String literals
    String,
    /// Char literals
    Char,
    /// Integer literals
    Int,
    /// Floating point literals
    Float,
}

/// Concrete literals
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Literal {
    /// The kind of literal
    pub kind: LiteralKind,
    /// We use a string here, because we'll be using type information to do
    /// further parsing of these. For example we need to know the size of an
    /// integer literal before we can know whether the literal is overflowing.
    pub value: String,
}

impl Literal {
    pub fn to_doc(&self) -> Doc<BoxDoc<()>> {
        Doc::as_string(&self.value)
    }
}
