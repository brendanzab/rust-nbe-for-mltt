//! Normal forms

use std::rc::Rc;

use crate::syntax::{AppMode, DbIndex, Label, Literal, UniverseLevel};

#[derive(Debug, Clone, PartialEq)]
pub struct RcNormal {
    pub inner: Rc<Normal>,
}

impl From<Normal> for RcNormal {
    fn from(src: Normal) -> RcNormal {
        RcNormal {
            inner: Rc::new(src),
        }
    }
}

impl AsRef<Normal> for RcNormal {
    fn as_ref(&self) -> &Normal {
        self.inner.as_ref()
    }
}

impl RcNormal {
    /// Construct a variable
    pub fn var(index: impl Into<DbIndex>) -> RcNormal {
        RcNormal::from(Normal::var(index))
    }
}

/// Terms that are in _normal form_
///
/// These are terms that have been fully evaluated under binders.
///
/// We use debruijn indices to allow these terms to be trivially compared for
/// alpha equality.
#[derive(Debug, Clone, PartialEq)]
pub enum Normal {
    /// Neutral values
    ///
    /// Terms for which computation has stopped because of an attempt to
    /// evaluate a variable.
    ///
    /// These are known as _neutral values_ or _accumulators_.
    Neutral(Head, Spine),

    /// Literal values
    Literal(Literal),

    /// Dependent function types
    FunType(AppMode, RcNormal, RcNormal),
    /// Introduce a function
    FunIntro(AppMode, RcNormal),

    /// Dependent record types
    RecordType(Vec<(Label, RcNormal)>),
    /// Introduce a record
    RecordIntro(Vec<(Label, RcNormal)>),

    /// Universe of types
    Universe(UniverseLevel),
}

impl Normal {
    /// Construct a variable
    pub fn var(index: impl Into<DbIndex>) -> Normal {
        Normal::Neutral(Head::Var(index.into()), Vec::new())
    }
}

/// The head of a neutral term
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Head {
    /// Variables
    Var(DbIndex),
}

/// A spine of eliminators
pub type Spine = Vec<Elim>;

/// An eliminator
#[derive(Debug, Clone, PartialEq)]
pub enum Elim {
    /// Argument application
    FunApp(AppMode, RcNormal),
    /// Field projection
    RecordProj(Label),
}
