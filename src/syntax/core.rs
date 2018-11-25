//! The surface syntax

use std::rc::Rc;

use syntax::{DbIndex, IdentHint, UniverseLevel};

pub type Env = im::Vector<(IdentHint, RcTerm)>;

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
    Var(IdentHint, DbIndex),
    /// Let bindings
    Let(IdentHint, RcTerm, RcTerm),
    /// A term that is explicitly annotated with a type
    Check(RcTerm, RcTerm),

    /// Dependent function types
    FunType(IdentHint, RcTerm, RcTerm),
    /// Introduce a function
    FunIntro(IdentHint, RcTerm),
    /// Apply a function to an argument
    FunApp(RcTerm, RcTerm),

    /// Dependent pair types
    PairType(IdentHint, RcTerm, RcTerm),
    /// Introduce a pair
    PairIntro(RcTerm, RcTerm),
    /// Project the first element of a pair
    PairFst(RcTerm),
    /// Project the second element of a pair
    PairSnd(RcTerm),

    /// Universe of types
    Universe(UniverseLevel),
}
