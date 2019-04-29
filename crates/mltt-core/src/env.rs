use std::ops;

use crate::{VarIndex, VarLevel};

/// An environment of entries that can be looked up based on a debruijn index.
///
/// It is backed by an `im::Vector` to allow for efficient sharing between
/// multiple closures.
#[derive(Debug, Clone, PartialEq)]
pub struct Env<Entry: Clone> {
    /// The entries in the environment
    entries: im::Vector<Entry>,
}

impl<Entry: Clone> Env<Entry> {
    /// Create a new, empty environment.
    pub fn new() -> Env<Entry> {
        Env {
            entries: im::Vector::new(),
        }
    }

    /// Get the size of the environment.
    pub fn size(&self) -> EnvSize {
        EnvSize(self.entries.len() as u32)
    }

    /// Lookup an entry in the environment.
    pub fn lookup_entry(&self, index: VarIndex) -> Option<&Entry> {
        self.entries.get(index.0 as usize)
    }

    /// Add an entry in the environment.
    pub fn add_entry(&mut self, entry: Entry) {
        self.entries.push_front(entry);
    }
}

/// The size of the environment.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct EnvSize(pub u32);

impl EnvSize {
    /// Return the level of the next variable to be added to the environment.
    pub fn next_var_level(self) -> VarLevel {
        VarLevel(self.0)
    }

    /// Convert a variable level to a variable index in the current environment.
    pub fn var_index(self, level: VarLevel) -> VarIndex {
        VarIndex(self.0 - (level.0 + 1)) // FIXME: Check for over/underflow?
    }
}

impl From<u32> for EnvSize {
    fn from(src: u32) -> EnvSize {
        EnvSize(src)
    }
}

impl ops::AddAssign<u32> for EnvSize {
    fn add_assign(&mut self, other: u32) {
        self.0 += other;
    }
}

impl ops::Add<u32> for EnvSize {
    type Output = EnvSize;

    fn add(mut self, other: u32) -> EnvSize {
        self += other;
        self
    }
}
