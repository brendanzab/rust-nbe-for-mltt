//! The unchecked raw syntax

use pretty::{BoxDoc, Doc};
use std::fmt;
use std::rc::Rc;

use super::Literal;

/// Top-level items in a module
#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    /// Forward-declarations
    Declaration {
        docs: Vec<String>,
        name: String,
        ann: RcTerm,
    },
    /// Term definitions
    Definition {
        docs: Vec<String>,
        name: String,
        body: RcTerm,
    },
}

impl Item {
    pub fn is_definition(&self) -> bool {
        match self {
            Item::Declaration { .. } => false,
            Item::Definition { .. } => true,
        }
    }
}

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

impl AsRef<Term> for RcTerm {
    fn as_ref(&self) -> &Term {
        self.inner.as_ref()
    }
}

impl fmt::Display for RcTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.inner.fmt(f)
    }
}

/// Raw terms
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// Variables
    Var(String),
    /// Literals
    Literal(Literal),
    /// Let bindings
    Let(String, RcTerm, RcTerm),
    /// A term that is explicitly annotated with a type
    Ann(RcTerm, RcTerm),

    /// Dependent function types
    FunType(String, RcTerm, RcTerm),
    /// Non-dependent function types
    FunArrowType(RcTerm, RcTerm),
    /// Introduce a function
    FunIntro(String, RcTerm),
    /// Apply a function to an argument
    FunApp(RcTerm, Vec<RcTerm>),

    /// Dependent pair types
    PairType(Option<String>, RcTerm, RcTerm),
    /// Introduce a pair
    PairIntro(RcTerm, RcTerm),
    /// Project the first element of a pair
    PairFst(RcTerm),
    /// Project the second element of a pair
    PairSnd(RcTerm),

    /// Universe of types
    Universe(Option<u32>),
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
            match term {
                Term::Ann(term, ann) => Doc::nil()
                    .append(to_doc_expr(term.as_ref()))
                    .append(Doc::space())
                    .append(":")
                    .append(Doc::space())
                    .append(to_doc_app(ann.as_ref())),
                _ => to_doc_expr(term),
            }
        }

        fn to_doc_expr(term: &Term) -> Doc<BoxDoc<()>> {
            match term {
                Term::Let(name, def, body) => Doc::nil()
                    .append("let")
                    .append(Doc::space())
                    .append(name)
                    .append(Doc::space())
                    .append("=")
                    .append(Doc::space())
                    .append(to_doc_app(def.as_ref()))
                    .append(Doc::space())
                    .append("in")
                    .append(Doc::space())
                    .append(to_doc_term(body.as_ref())),
                Term::FunType(name, param_ty, body_ty) => Doc::nil()
                    .append(Doc::group(
                        Doc::nil()
                            .append("Fun")
                            .append(Doc::space())
                            .append("(")
                            .append(name)
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
                Term::FunIntro(name, body) => Doc::nil()
                    .append("fun")
                    .append(Doc::space())
                    .append(name)
                    .append(Doc::space())
                    .append("=>")
                    .append(Doc::space())
                    .append(to_doc_app(body.as_ref())),
                Term::PairType(_, fst_ty, snd_ty) => Doc::nil()
                    .append("Pair")
                    .append(Doc::space())
                    .append("{")
                    .append(Doc::space())
                    .append("_")
                    .append(Doc::space())
                    .append(":")
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
                _ => to_doc_arrow(term),
            }
        }

        fn to_doc_arrow(term: &Term) -> Doc<BoxDoc<()>> {
            match term {
                Term::FunArrowType(param_ty, body_ty) => Doc::nil()
                    .append(to_doc_app(param_ty.as_ref()))
                    .append(Doc::space())
                    .append("->")
                    .append(Doc::space())
                    .append(to_doc_app(body_ty.as_ref())),
                _ => to_doc_app(term),
            }
        }

        fn to_doc_app(term: &Term) -> Doc<BoxDoc<()>> {
            match term {
                Term::FunApp(fun, args) => Doc::nil()
                    .append(to_doc_term(fun.as_ref()))
                    .append(Doc::space())
                    .append(Doc::intersperse(
                        args.iter().map(|arg| to_doc_atomic(arg.as_ref())),
                        Doc::space(),
                    )),
                _ => to_doc_atomic(term),
            }
        }

        fn to_doc_atomic(term: &Term) -> Doc<BoxDoc<()>> {
            match term {
                Term::Var(name) => Doc::as_string(name),
                Term::Literal(literal) => literal.to_doc(),
                Term::PairFst(pair) => to_doc_atomic(pair.as_ref()).append(".1"),
                Term::PairSnd(pair) => to_doc_atomic(pair.as_ref()).append(".2"),
                Term::Universe(None) => Doc::text("Type"),
                Term::Universe(Some(level)) => Doc::text("Type^").append(Doc::as_string(level)),
                _ => Doc::text("(").append(to_doc_term(term)).append(")"),
            }
        }

        to_doc_term(self)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.to_doc().group().pretty(1_000_000_000).fmt(f)
    }
}
