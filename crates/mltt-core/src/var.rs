use std::fmt;
use std::ops;

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
    pub fn size(&self) -> Size {
        Size(self.entries.len() as u32)
    }

    /// Lookup an entry in the environment.
    pub fn lookup_entry(&self, index: Index) -> Option<&Entry> {
        self.entries.get(index.0 as usize)
    }

    /// Add an entry in the environment.
    pub fn add_entry(&mut self, entry: Entry) {
        self.entries.push_front(entry);
    }
}

/// The size of the environment.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Size(pub u32);

impl Size {
    /// Return the level of the next variable to be added to the environment.
    pub fn next_level(self) -> Level {
        Level(self.0)
    }

    /// Convert a variable level to a variable index in the current environment.
    pub fn index(self, level: Level) -> Index {
        Index(self.0 - (level.0 + 1)) // FIXME: Check for over/underflow?
    }
}

impl From<u32> for Size {
    fn from(src: u32) -> Size {
        Size(src)
    }
}

impl ops::AddAssign<u32> for Size {
    fn add_assign(&mut self, other: u32) {
        self.0 += other;
    }
}

impl ops::Add<u32> for Size {
    type Output = Size;

    fn add(mut self, other: u32) -> Size {
        self += other;
        self
    }
}

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
pub struct Level(pub u32);

impl From<u32> for Level {
    fn from(src: u32) -> Level {
        Level(src)
    }
}

impl ops::AddAssign<u32> for Level {
    fn add_assign(&mut self, other: u32) {
        self.0 += other;
    }
}

impl ops::Add<u32> for Level {
    type Output = Level;

    fn add(mut self, other: u32) -> Level {
        self += other;
        self
    }
}

impl std::fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "%{}", self.0)
    }
}

/// De Bruijn index.
///
/// This counts the number of binders we encounter when running up the syntax
/// tree to get to the binder that bound this variable. De Bruijn indices are
/// useful for being able to quickly looking up entries in an `Env` when deep in
/// a nested scope. They also provide easy access to alpha equality.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Index(pub u32);

impl From<u32> for Index {
    fn from(src: u32) -> Index {
        Index(src)
    }
}

impl ops::AddAssign<u32> for Index {
    fn add_assign(&mut self, other: u32) {
        self.0 += other;
    }
}

impl ops::Add<u32> for Index {
    type Output = Index;

    fn add(mut self, other: u32) -> Index {
        self += other;
        self
    }
}

impl std::fmt::Display for Index {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "@{}", self.0)
    }
}
