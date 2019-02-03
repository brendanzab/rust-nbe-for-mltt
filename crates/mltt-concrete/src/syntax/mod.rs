pub mod concrete;
pub mod raw;

/// Concrete literals
///
/// We use strings here, because we'll be using type information to do further
/// parsing of these. For example we need to know the size of an integer literal
/// before we can know whether the literal is overflowing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    /// String literals
    String(String),
    /// Char literals
    Char(String),
    /// Integer literals
    Int(String),
    /// Floating point literals
    Float(String),
}
