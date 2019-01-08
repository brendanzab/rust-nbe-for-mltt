//! The various syntaxes of the language
//!
//! The core, domain, and normal syntaxes are mainly based off Mini-TT

use std::ops;

pub mod core;
pub mod domain;
pub mod normal;

/// DeBruijn level
///
/// This counts the total number of binders that we encounter when running up
/// the syntax tree to the root, _not including free binders_.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DbLevel(pub u32);

impl From<u32> for DbLevel {
    fn from(src: u32) -> DbLevel {
        DbLevel(src)
    }
}

impl ops::AddAssign<u32> for DbLevel {
    fn add_assign(&mut self, other: u32) {
        self.0 += other;
    }
}

impl ops::Add<u32> for DbLevel {
    type Output = DbLevel;

    fn add(mut self, other: u32) -> DbLevel {
        self += other;
        self
    }
}

/// DeBruijn index
///
/// This counts the number of binders we encounter when running up the tree to
/// get to the binder that bound this variable.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DbIndex(pub u32);

impl From<u32> for DbIndex {
    fn from(src: u32) -> DbIndex {
        DbIndex(src)
    }
}

impl ops::AddAssign<u32> for DbIndex {
    fn add_assign(&mut self, other: u32) {
        self.0 += other;
    }
}

impl ops::Add<u32> for DbIndex {
    type Output = DbIndex;

    fn add(mut self, other: u32) -> DbIndex {
        self += other;
        self
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
