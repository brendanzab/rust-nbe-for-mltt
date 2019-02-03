pub mod concrete;
pub mod raw;

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
