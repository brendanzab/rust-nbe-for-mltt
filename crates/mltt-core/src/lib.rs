//! The core type theory of the MLTT language.

#![warn(rust_2018_idioms)]

use std::fmt;
use std::ops;
use std::rc::Rc;

pub mod env;
pub mod meta;

pub mod domain;
pub mod literal;
pub mod pretty;
pub mod prim;
pub mod syntax;

pub mod nbe;
pub mod validate;

/// Reference counted documentation string.
pub type DocString = Rc<str>;

/// De Bruijn level.
///
/// This counts the total number of binders that we encounter when running down
/// the syntax tree from the root.
///
/// De Bruijn levels are useful because unlike de Bruijn indices, they don't
/// need to be shifted while moving around terms under a specific scope. This
/// makes them ideal for representing values. We'll convert these back into
/// indices during read-back.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct VarLevel(pub u32);

impl From<u32> for VarLevel {
    fn from(src: u32) -> VarLevel {
        VarLevel(src)
    }
}

impl ops::AddAssign<u32> for VarLevel {
    fn add_assign(&mut self, other: u32) {
        self.0 += other;
    }
}

impl ops::Add<u32> for VarLevel {
    type Output = VarLevel;

    fn add(mut self, other: u32) -> VarLevel {
        self += other;
        self
    }
}

/// De Bruijn index.
///
/// This counts the number of binders we encounter when running up the syntax
/// tree to get to the binder that bound this variable. De Bruijn indices are
/// useful for being able to quickly looking up entries in an `Env` when deep in
/// a nested scope. They also provide easy access to alpha equality.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct VarIndex(pub u32);

impl From<u32> for VarIndex {
    fn from(src: u32) -> VarIndex {
        VarIndex(src)
    }
}

impl ops::AddAssign<u32> for VarIndex {
    fn add_assign(&mut self, other: u32) {
        self.0 += other;
    }
}

impl ops::Add<u32> for VarIndex {
    type Output = VarIndex;

    fn add(mut self, other: u32) -> VarIndex {
        self += other;
        self
    }
}

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
