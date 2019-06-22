//! The core type theory of the MLTT language.

#![warn(rust_2018_idioms)]

use std::fmt;
use std::rc::Rc;
use std::u16;

pub mod global;
pub mod meta;
pub mod var;

pub mod domain;
pub mod literal;
pub mod pretty;
pub mod prim;
pub mod syntax;

pub mod nbe;
pub mod validate;

/// Reference counted documentation string.
pub type DocString = Rc<str>;

/// A label. These are treated as significant when comparing terms for alpha
/// equivalence.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Label(pub String);

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// The application mode of a function.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AppMode {
    /// Explicit application mode.
    Explicit,
    /// Implicit application mode.
    Implicit(Label),
    /// Instance application mode.
    Instance(Label),
}

impl fmt::Display for AppMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AppMode::Explicit => write!(f, "_"),
            AppMode::Implicit(label) => write!(f, "{{{}}}", label),
            AppMode::Instance(label) => write!(f, "{{{{{}}}}}", label),
        }
    }
}

/// The level of a universe.
///
/// We allow room for `65535` levels, which should be more than enough for most
/// sane purposes!
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct UniverseLevel(pub u16);

impl UniverseLevel {
    /// The maximum universe level that can be represented.
    pub const MAX: UniverseLevel = UniverseLevel(u16::MAX);

    /// Shift the by the given amount, returning an error if maximum universe
    /// level has been reached.
    pub fn shift(self, shift: u16) -> Option<UniverseLevel> {
        Some(UniverseLevel(self.0.checked_add(shift)?))
    }
}

impl From<u16> for UniverseLevel {
    fn from(src: u16) -> UniverseLevel {
        UniverseLevel(src)
    }
}

impl fmt::Display for UniverseLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}
