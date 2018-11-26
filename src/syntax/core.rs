//! The surface syntax

use std::rc::Rc;

use syntax::normal::{Neutral, Normal, RcNeutral, RcNormal};
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

impl<'a> From<&'a RcNormal> for RcTerm {
    fn from(src: &'a RcNormal) -> RcTerm {
        match *src.inner {
            Normal::Neutral(ref neutral) => RcTerm::from(neutral),

            Normal::FunType(ref ident, ref param_ty, ref body_ty) => RcTerm::from(Term::FunType(
                ident.clone(),
                RcTerm::from(param_ty),
                RcTerm::from(body_ty),
            )),
            Normal::FunIntro(ref ident, ref body) => {
                RcTerm::from(Term::FunIntro(ident.clone(), RcTerm::from(body)))
            },

            Normal::PairType(ref ident, ref fst_ty, ref snd_ty) => RcTerm::from(Term::PairType(
                ident.clone(),
                RcTerm::from(fst_ty),
                RcTerm::from(snd_ty),
            )),
            Normal::PairIntro(ref fst, ref snd) => {
                RcTerm::from(Term::PairIntro(RcTerm::from(fst), RcTerm::from(snd)))
            },

            Normal::Universe(level) => RcTerm::from(Term::Universe(level)),
        }
    }
}

impl<'a> From<&'a RcNeutral> for RcTerm {
    fn from(src: &'a RcNeutral) -> RcTerm {
        match *src.inner {
            Neutral::Var(ref ident, index) => RcTerm::from(Term::Var(ident.clone(), index)),
            Neutral::FunApp(ref fun, ref arg) => {
                RcTerm::from(Term::FunApp(RcTerm::from(fun), RcTerm::from(arg)))
            },
            Neutral::PairFst(ref pair) => RcTerm::from(Term::PairFst(RcTerm::from(pair))),
            Neutral::PairSnd(ref pair) => RcTerm::from(Term::PairSnd(RcTerm::from(pair))),
        }
    }
}
