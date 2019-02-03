//! Normal forms

use std::rc::Rc;

use crate::syntax::{DbIndex, UniverseLevel};

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
    pub fn var(level: impl Into<DbIndex>) -> RcNormal {
        RcNormal::from(Normal::var(level))
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
    /// Neutral values, annotated with a type
    Neutral(RcNeutral),

    /// Dependent function types
    FunType(RcNormal, RcNormal),
    /// Introduce a function
    FunIntro(RcNormal),

    /// Dependent pair types
    PairType(RcNormal, RcNormal),
    /// Introduce a pair
    PairIntro(RcNormal, RcNormal),

    /// Universe of types
    Universe(UniverseLevel),
}

impl Normal {
    /// Construct a variable
    pub fn var(level: impl Into<DbIndex>) -> Normal {
        Normal::Neutral(RcNeutral::from(Neutral::Var(level.into())))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RcNeutral {
    pub inner: Rc<Neutral>,
}

impl From<Neutral> for RcNeutral {
    fn from(src: Neutral) -> RcNeutral {
        RcNeutral {
            inner: Rc::new(src),
        }
    }
}

impl AsRef<Neutral> for RcNeutral {
    fn as_ref(&self) -> &Neutral {
        self.inner.as_ref()
    }
}

/// Terms for which computation has stopped because of an attempt to evaluate a
/// variable
///
/// These are known as _neutral values_ or _accumulators_.
#[derive(Debug, Clone, PartialEq)]
pub enum Neutral {
    /// Variables
    Var(DbIndex),

    /// Apply a function to an argument
    FunApp(RcNeutral, RcNormal),

    /// Project the first element of a pair
    PairFst(RcNeutral),
    /// Project the second element of a pair
    PairSnd(RcNeutral),
}
