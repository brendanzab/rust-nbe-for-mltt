//! The surface syntax

use std::rc::Rc;

use syntax::{DbIndex, UniverseLevel};

pub type Env = im::Vector<RcTerm>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RcTerm {
    pub inner: Rc<Term>,
}

impl From<Term> for RcTerm {
    fn from(src: Term) -> RcTerm {
        RcTerm {
            inner: Rc::new(src),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// Variables
    Var(DbIndex),
    /// Let bindings
    Let(RcTerm, /* BINDS */ RcTerm),
    /// A term that is explicitly annotated with a type
    Check(RcTerm, RcTerm),

    /// Dependent function types
    FunType(RcTerm, /* BINDS */ RcTerm),
    /// Introduce a function
    FunIntro(/* BINDS */ RcTerm),
    /// Apply a function to an argument
    FunApp(RcTerm, RcTerm),

    /// Dependent par types
    PairType(RcTerm, /* BINDS */ RcTerm),
    /// Introduce a pair
    PairIntro(RcTerm, RcTerm),
    /// Project the first element of a pair
    PairFst(RcTerm),
    /// Project the second element of a pair
    PairSnd(RcTerm),

    /// Universe of types
    Universe(UniverseLevel),
}
