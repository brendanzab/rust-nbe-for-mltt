//! The checked core syntax

use pretty::{BoxDoc, Doc};
use std::fmt;
use std::rc::Rc;

use crate::syntax::{normal, DbIndex, Literal, UniverseLevel};

pub type Env = im::Vector<RcTerm>;

/// Top-level items
#[derive(Debug, Clone, PartialEq)]
pub struct Item {
    pub doc: String,
    pub name: String,
    pub term_ty: RcTerm,
    pub term: RcTerm,
}

#[derive(Debug, Clone, PartialEq)]
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

impl AsRef<Term> for RcTerm {
    fn as_ref(&self) -> &Term {
        self.inner.as_ref()
    }
}

impl fmt::Display for RcTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

/// Core terms
// TODO: explicitly annotate with types
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// Variables
    Var(DbIndex),
    /// Literals
    Literal(Literal),
    /// Let bindings
    Let(RcTerm, /* RcTerm, */ RcTerm),

    /// Dependent function types
    FunType(RcTerm, RcTerm),
    /// Introduce a function
    FunIntro(/* RcTerm, */ RcTerm),
    /// Apply a function to an argument
    FunApp(RcTerm, RcTerm),

    /// Dependent pair types
    PairType(RcTerm, RcTerm),
    /// Introduce a pair
    PairIntro(RcTerm, RcTerm),
    /// Project the first element of a pair
    PairFst(RcTerm),
    /// Project the second element of a pair
    PairSnd(RcTerm),

    /// Universe of types
    Universe(UniverseLevel),
}

impl RcTerm {
    /// Convert the term into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        self.inner.to_doc()
    }
}

impl Term {
    /// Convert the term into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        // Using precedence climbing (mirroring the language grammar) in
        // order to cut down on extraneous parentheses.

        fn to_doc_term(term: &Term) -> Doc<'_, BoxDoc<'_, ()>> {
            match term {
                _ => to_doc_expr(term),
            }
        }

        fn to_doc_expr(term: &Term) -> Doc<'_, BoxDoc<'_, ()>> {
            match term {
                Term::Let(def, body) => Doc::nil()
                    .append("let")
                    .append(Doc::space())
                    .append("_")
                    .append(Doc::space())
                    .append("=")
                    .append(Doc::space())
                    .append(to_doc_app(def.as_ref()))
                    .append(Doc::space())
                    .append("in")
                    .append(Doc::space())
                    .append(to_doc_term(body.as_ref())),
                Term::FunType(param_ty, body_ty) => Doc::nil()
                    .append(Doc::group(
                        Doc::nil()
                            .append("Fun")
                            .append(Doc::space())
                            .append("(")
                            .append("_")
                            .append(Doc::space())
                            .append(":")
                            .append(Doc::space())
                            .append(to_doc_term(param_ty.as_ref()))
                            .append(")"),
                    ))
                    .append(Doc::space())
                    .append("->")
                    .append(Doc::space())
                    .append(to_doc_app(body_ty.as_ref())),
                Term::FunIntro(body) => Doc::nil()
                    .append("fun")
                    .append(Doc::space())
                    .append("_")
                    .append(Doc::space())
                    .append("=>")
                    .append(Doc::space())
                    .append(to_doc_app(body.as_ref())),
                Term::PairType(fst_ty, snd_ty) => Doc::nil()
                    .append("Pair")
                    .append(Doc::space())
                    .append("{")
                    .append(Doc::space())
                    .append("_")
                    .append(Doc::space())
                    .append(":")
                    .append(Doc::space())
                    .append(to_doc_term(fst_ty.as_ref()))
                    .append(",")
                    .append(Doc::space())
                    .append(to_doc_term(snd_ty.as_ref()))
                    .append(Doc::space())
                    .append("}"),
                Term::PairIntro(fst, snd) => Doc::nil()
                    .append("pair")
                    .append(Doc::space())
                    .append("{")
                    .append(Doc::space())
                    .append(to_doc_term(fst.as_ref()))
                    .append(",")
                    .append(Doc::space())
                    .append(to_doc_term(snd.as_ref()))
                    .append(Doc::space())
                    .append("}"),
                _ => to_doc_app(term),
            }
        }

        fn to_doc_app(term: &Term) -> Doc<'_, BoxDoc<'_, ()>> {
            match term {
                Term::FunApp(fun, arg) => Doc::nil()
                    .append(to_doc_term(fun.as_ref()))
                    .append(Doc::space())
                    .append(to_doc_atomic(arg.as_ref())),
                _ => to_doc_atomic(term),
            }
        }

        fn to_doc_atomic(term: &Term) -> Doc<'_, BoxDoc<'_, ()>> {
            match term {
                Term::Var(DbIndex(index)) => Doc::as_string(format!("@{}", index)),
                Term::Literal(literal) => literal.to_doc(),
                Term::PairFst(pair) => to_doc_atomic(pair.as_ref()).append(".fst"),
                Term::PairSnd(pair) => to_doc_atomic(pair.as_ref()).append(".snd"),
                Term::Universe(UniverseLevel(level)) => {
                    Doc::text("Type^").append(Doc::as_string(level))
                },
                _ => Doc::text("(").append(to_doc_term(term)).append(")"),
            }
        }

        to_doc_term(self)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_doc().group().pretty(1_000_000_000).fmt(f)
    }
}

impl From<&'_ normal::RcNormal> for RcTerm {
    fn from(src: &normal::RcNormal) -> RcTerm {
        RcTerm::from(src.as_ref())
    }
}

impl From<&'_ normal::Normal> for RcTerm {
    fn from(src: &normal::Normal) -> RcTerm {
        RcTerm::from(match src {
            normal::Normal::Neutral(neutral) => return RcTerm::from(neutral),
            normal::Normal::Literal(literal) => Term::Literal(literal.clone()),
            normal::Normal::FunType(param_ty, body_ty) => {
                Term::FunType(RcTerm::from(param_ty), RcTerm::from(body_ty))
            },
            normal::Normal::FunIntro(body) => Term::FunIntro(RcTerm::from(body)),
            normal::Normal::PairType(fst_ty, snd_ty) => {
                Term::PairType(RcTerm::from(fst_ty), RcTerm::from(snd_ty))
            },
            normal::Normal::PairIntro(fst, snd) => {
                Term::PairIntro(RcTerm::from(fst), RcTerm::from(snd))
            },
            normal::Normal::Universe(level) => Term::Universe(*level),
        })
    }
}

impl From<&'_ normal::RcNeutral> for RcTerm {
    fn from(src: &normal::RcNeutral) -> RcTerm {
        RcTerm::from(src.as_ref())
    }
}

impl From<&'_ normal::Neutral> for RcTerm {
    fn from(src: &normal::Neutral) -> RcTerm {
        RcTerm::from(match src {
            normal::Neutral::Var(index) => Term::Var(*index),
            normal::Neutral::FunApp(fun, arg) => Term::FunApp(RcTerm::from(fun), RcTerm::from(arg)),
            normal::Neutral::PairFst(pair) => Term::PairFst(RcTerm::from(pair)),
            normal::Neutral::PairSnd(pair) => Term::PairSnd(RcTerm::from(pair)),
        })
    }
}
