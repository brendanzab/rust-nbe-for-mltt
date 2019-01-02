//! The various syntaxes of the language
//!
//! The core, domain, and normal syntaxes are mainly based off Mini-TT

pub mod core;
pub mod domain;
pub mod normal;

/// DeBruijn level
///
/// This counts the total number of binders that we encounter when running up
/// the syntax tree to the root, _not including free binders_.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DbLevel(pub u32);

/// DeBruijn index
///
/// This counts the number of binders we encounter when running up the tree to
/// get to the binder that bound this variable.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DbIndex(pub u32);

/// The level of a universe
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct UniverseLevel(pub u32);
