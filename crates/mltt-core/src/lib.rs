//! The core type theory of the MLTT language.

#![warn(rust_2018_idioms)]

use std::fmt;
use std::ops;
use std::rc::Rc;

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
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct UniverseLevel(pub u32);

impl From<u32> for UniverseLevel {
    fn from(src: u32) -> UniverseLevel {
        UniverseLevel(src)
    }
}

impl ops::AddAssign<u32> for UniverseLevel {
    fn add_assign(&mut self, other: u32) {
        self.0 += other;
    }
}

impl ops::Add<u32> for UniverseLevel {
    type Output = UniverseLevel;

    fn add(mut self, other: u32) -> UniverseLevel {
        self += other;
        self
    }
}

impl fmt::Display for UniverseLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}
