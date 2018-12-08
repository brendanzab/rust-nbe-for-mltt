//! The checked core syntax

use pretty::{BoxDoc, Doc};
use std::rc::Rc;

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

/// Core terms, explicitly annotated with types
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// Variables
    Var(DbIndex),
    /// Let bindings
    Let(IdentHint, RcTerm, RcTerm, RcTerm),

    /// Dependent function types
    FunType(IdentHint, RcTerm, RcTerm),
    /// Introduce a function
    FunIntro(IdentHint, RcTerm, RcTerm),
    /// Apply a function to an argument
    FunApp(RcTerm, RcTerm),

    /// Dependent pair types
    PairType(IdentHint, RcTerm, RcTerm),
    /// Introduce a pair
    PairIntro(RcTerm, RcTerm, IdentHint, RcTerm, RcTerm),
    /// Project the first element of a pair
    PairFst(RcTerm),
    /// Project the second element of a pair
    PairSnd(RcTerm),

    /// Universe of types
    Universe(UniverseLevel),
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
                Term::PairIntro(ref fst, ref snd, _, ref fst_ty, ref snd_ty) => Doc::nil()
                    .append("<")
                    .append(to_doc_term(&*fst.inner))
                    .append(",")
                    .append(Doc::space())
                    .append(to_doc_term(&*snd.inner))
                    .append(">")
                    .append(Doc::space())
                    .append(":")
                    .append(Doc::space())
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
                _ => to_doc_expr(term),
            }
        }

        fn to_doc_expr(term: &Term) -> Doc<BoxDoc<()>> {
            match *term {
                Term::Let(_, ref def, ref def_ty, ref body) => Doc::nil()
                    .append("let")
                    .append(Doc::space())
                    .append("_")
                    .append(Doc::space())
                    .append(":")
                    .append(Doc::space())
                    .append(to_doc_app(&*def_ty.inner))
                    .append(Doc::space())
                    .append("=")
                    .append(Doc::space())
                    .append(to_doc_app(&*def.inner))
                    .append(Doc::space())
                    .append("in")
                    .append(Doc::space())
                    .append(to_doc_term(&*body.inner)),
                Term::FunIntro(_, ref param_ty, ref body) => Doc::nil()
                    .append("\\")
                    .append("_")
                    .append(Doc::space())
                    .append(":")
                    .append(Doc::space())
                    .append(to_doc_app(&*param_ty.inner))
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
