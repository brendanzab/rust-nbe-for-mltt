pub mod concrete;
pub mod core;
pub mod domain;

/// The level of a universe
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct UniverseLevel(pub u32);

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
