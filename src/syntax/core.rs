//! The surface syntax

use pretty::{BoxDoc, Doc};
use std::rc::Rc;

use crate::syntax::normal::{Neutral, Normal, RcNeutral, RcNormal};
use crate::syntax::{DbIndex, IdentHint, UniverseLevel};

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
            Neutral::Var(index) => RcTerm::from(Term::Var(index)),
            Neutral::FunApp(ref fun, ref arg) => {
                RcTerm::from(Term::FunApp(RcTerm::from(fun), RcTerm::from(arg)))
            },
            Neutral::PairFst(ref pair) => RcTerm::from(Term::PairFst(RcTerm::from(pair))),
            Neutral::PairSnd(ref pair) => RcTerm::from(Term::PairSnd(RcTerm::from(pair))),
        }
    }
}

impl RcTerm {
    /// Convert the term into a pretty-printable document
    pub fn to_doc(&self) -> Doc<BoxDoc<()>> {
        self.inner.to_doc()
    }
}

impl Term {
    /// Convert the term into a pretty-printable document
    pub fn to_doc(&self) -> Doc<BoxDoc<()>> {
        // Using precedence climbing (mirroring the language grammar) in
        // order to cut down on extraneous parentheses.

        fn to_doc_term(term: &Term) -> Doc<BoxDoc<()>> {
            match *term {
                Term::Check(ref term, ref ann) => Doc::nil()
                    .append(to_doc_expr(&*term.inner))
                    .append(Doc::space())
                    .append(":")
                    .append(Doc::space())
                    .append(to_doc_app(&*ann.inner)),
                _ => to_doc_expr(term),
            }
        }

        fn to_doc_expr(term: &Term) -> Doc<BoxDoc<()>> {
            match *term {
                Term::Let(_, ref def, ref body) => Doc::nil()
                    .append("let")
                    .append(Doc::space())
                    .append("_")
                    .append(Doc::space())
                    .append("=")
                    .append(Doc::space())
                    .append(to_doc_app(&*def.inner))
                    .append(Doc::space())
                    .append("in")
                    .append(Doc::space())
                    .append(to_doc_term(&*body.inner)),
                Term::FunIntro(_, ref body) => Doc::nil()
                    .append("\\")
                    .append("_")
                    .append(Doc::space())
                    .append("=>")
                    .append(Doc::space())
                    .append(to_doc_app(&*body.inner)),
                _ => to_doc_arrow(term),
            }
        }

        fn to_doc_arrow(term: &Term) -> Doc<BoxDoc<()>> {
            match *term {
                Term::FunType(_, ref param_ty, ref body_ty) => Doc::nil()
                    .append(Doc::group(
                        Doc::nil()
                            .append("(")
                            .append("_")
                            .append(Doc::space())
                            .append(":")
                            .append(Doc::space())
                            .append(to_doc_term(&*param_ty.inner))
                            .append(")"),
                    ))
                    .append(Doc::space())
                    .append("->")
                    .append(Doc::space())
                    .append(to_doc_app(&*body_ty.inner)),
                Term::PairType(_, ref fst_ty, ref snd_ty) => Doc::nil()
                    .append(Doc::group(
                        Doc::nil()
                            .append("(")
                            .append("_")
                            .append(Doc::space())
                            .append(":")
                            .append(Doc::space())
                            .append(to_doc_term(&*fst_ty.inner))
                            .append(")"),
                    ))
                    .append(Doc::space())
                    .append("*")
                    .append(Doc::space())
                    .append(to_doc_app(&*snd_ty.inner)),
                _ => to_doc_app(term),
            }
        }

        fn to_doc_app(term: &Term) -> Doc<BoxDoc<()>> {
            match *term {
                Term::FunApp(ref fun, ref arg) => Doc::nil()
                    .append(to_doc_term(&*fun.inner))
                    .append(Doc::space())
                    .append(to_doc_atomic(&*arg.inner)),
                _ => to_doc_atomic(term),
            }
        }

        fn to_doc_atomic(term: &Term) -> Doc<BoxDoc<()>> {
            match *term {
                Term::Var(DbIndex(index)) => Doc::as_string(format!("@{}", index)),
                Term::PairIntro(ref fst, ref snd) => Doc::nil()
                    .append("<")
                    .append(to_doc_term(&*fst.inner))
                    .append(",")
                    .append(Doc::space())
                    .append(to_doc_term(&*snd.inner))
                    .append(">"),
                Term::PairFst(ref pair) => to_doc_atomic(&*pair.inner).append(".1"),
                Term::PairSnd(ref pair) => to_doc_atomic(&*pair.inner).append(".2"),
                Term::Universe(UniverseLevel(level)) => {
                    Doc::text("Type^").append(Doc::as_string(level))
                },
                _ => Doc::text("(").append(to_doc_term(term)).append(")"),
            }
        }

        to_doc_term(self)
    }
}
