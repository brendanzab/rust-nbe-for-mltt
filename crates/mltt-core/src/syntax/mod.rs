//! The various syntaxes of the language
//!
//! The core, domain, and normal syntaxes are mainly based off Mini-TT

use pretty::{BoxDoc, Doc};
use std::ops;

pub mod core;
pub mod domain;

/// De Bruijn level
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

/// De Bruijn index
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

/// An environment of entries that can be looked up based on a debruijn index.
#[derive(Debug, Clone, PartialEq)]
pub struct Env<T: Clone> {
    /// The entries in the environment
    entries: im::Vector<T>,
}

impl<T: Clone> Env<T> {
    /// Create a new, empty environment.
    pub fn new() -> Env<T> {
        Env {
            entries: im::Vector::new(),
        }
    }

    /// Lookup an entry in the environment.
    pub fn lookup_entry(&self, index: VarIndex) -> Option<&T> {
        self.entries.get(index.0 as usize)
    }

    /// Add a new entry to the environment.
    pub fn add_entry(&mut self, value: T) {
        self.entries.push_front(value)
    }
}

/// The level of a universe
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

/// Literals
#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum Literal {
    String(String),
    Char(char),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    S8(i8),
    S16(i16),
    S32(i32),
    S64(i64),
    F32(f32),
    F64(f64),
}

impl Literal {
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            Literal::String(value) => Doc::text(format!("{:?}", value)),
            Literal::Char(value) => Doc::text(format!("{:?}", value)),
            Literal::U8(value) => Doc::as_string(&value),
            Literal::U16(value) => Doc::as_string(&value),
            Literal::U32(value) => Doc::as_string(&value),
            Literal::U64(value) => Doc::as_string(&value),
            Literal::S8(value) => Doc::as_string(&value),
            Literal::S16(value) => Doc::as_string(&value),
            Literal::S32(value) => Doc::as_string(&value),
            Literal::S64(value) => Doc::as_string(&value),
            Literal::F32(value) => Doc::as_string(&value),
            Literal::F64(value) => Doc::as_string(&value),
        }
    }
}

/// A label
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Label(pub String);

/// The application mode of a function
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AppMode {
    /// Explicit application mode
    Explicit,
    /// Implicit application mode
    Implicit(Label),
}
