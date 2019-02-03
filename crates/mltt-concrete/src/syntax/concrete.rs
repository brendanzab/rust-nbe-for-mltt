//! The concrete syntax

use pretty::{BoxDoc, Doc};
use std::fmt;

use super::Literal;

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    Declaration {
        docs: Vec<String>,
        name: String,
        ann: Term,
    },
    Definition {
        docs: Vec<String>,
        name: String,
        params: Vec<String>,
        body: Term,
    },
}

/// Concrete terms
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// Variables
    Var(String),
    /// Literals
    Literal(Literal),
    /// Let bindings
    Let(String, Box<Term>, Box<Term>),
    /// A term that is explicitly annotated with a type
    Ann(Box<Term>, Box<Term>),
    /// A parenthesized term
    Parens(Box<Term>),

    /// Dependent function type
    ///
    /// Also known as a _pi type_ or _dependent product type_.
    FunType(Vec<(Vec<String>, Term)>, Box<Term>),
    /// Non-dependent function types
    FunArrowType(Box<Term>, Box<Term>),
    /// Introduce a function
    ///
    /// Also known as a _lambda expression_ or _anonymous function_.
    FunIntro(Vec<String>, Box<Term>),
    /// Apply a function to an argument
    FunApp(Box<Term>, Vec<Term>),

    /// Dependent pair type
    ///
    /// Also known as a _sigma type_ or _dependent sum type_
    PairType(Option<String>, Box<Term>, Box<Term>),
    /// Introduce a pair
    PairIntro(Box<Term>, Box<Term>),
    /// Project the first element of a pair
    PairFst(Box<Term>),
    /// Project the second element of a pair
    PairSnd(Box<Term>),

    /// Universe of types
    Universe(Option<u32>),
}

impl Term {
    /// Convert the term into a pretty-printable document
    pub fn to_doc(&self) -> Doc<BoxDoc<()>> {
        // Using precedence climbing (mirroring the language grammar) in
        // order to cut down on extraneous parentheses.

        fn to_doc_term(term: &Term) -> Doc<BoxDoc<()>> {
            match term {
                Term::Ann(term, ann) => Doc::nil()
                    .append(to_doc_expr(term))
                    .append(Doc::space())
                    .append(":")
                    .append(Doc::space())
                    .append(to_doc_app(ann)),
                _ => to_doc_expr(term),
            }
        }

        fn to_doc_expr(term: &Term) -> Doc<BoxDoc<()>> {
            match term {
                Term::Let(name, def, body) => Doc::nil()
                    .append("let")
                    .append(Doc::space())
                    .append(Doc::as_string(name))
                    .append(Doc::space())
                    .append("=")
                    .append(Doc::space())
                    .append(to_doc_app(def))
                    .append(Doc::space())
                    .append("in")
                    .append(Doc::space())
                    .append(to_doc_term(body)),
                Term::FunType(params, body_ty) => Doc::nil()
                    .append(Doc::group(
                        Doc::nil()
                            .append("Fun")
                            .append(Doc::space())
                            .append(Doc::intersperse(
                                params.iter().map(|(param_names, param_ty)| {
                                    Doc::nil()
                                        .append("(")
                                        .append(Doc::intersperse(
                                            param_names.iter().map(Doc::as_string),
                                            Doc::space(),
                                        ))
                                        .append(Doc::space())
                                        .append(":")
                                        .append(Doc::space())
                                        .append(to_doc_term(param_ty))
                                        .append(")")
                                }),
                                Doc::space(),
                            )),
                    ))
                    .append(Doc::space())
                    .append("->")
                    .append(Doc::space())
                    .append(to_doc_app(body_ty)),
                Term::FunIntro(names, body) => Doc::nil()
                    .append("fun")
                    .append(Doc::space())
                    .append(Doc::intersperse(
                        names.iter().map(Doc::as_string),
                        Doc::space(),
                    ))
                    .append(Doc::space())
                    .append("=>")
                    .append(Doc::space())
                    .append(to_doc_app(body)),
                Term::PairType(name, fst_ty, snd_ty) => Doc::nil()
                    .append("Pair")
                    .append(Doc::space())
                    .append("{")
                    .append(Doc::space())
                    .append(name.as_ref().map_or(Doc::nil(), |name| {
                        Doc::nil()
                            .append(Doc::as_string(name))
                            .append(Doc::space())
                            .append(":")
                    }))
                    .append(to_doc_term(fst_ty))
                    .append(",")
                    .append(Doc::space())
                    .append(to_doc_term(snd_ty))
                    .append(Doc::space())
                    .append("}"),
                Term::PairIntro(fst, snd) => Doc::nil()
                    .append("pair")
                    .append(Doc::space())
                    .append("{")
                    .append(Doc::space())
                    .append(to_doc_term(fst))
                    .append(",")
                    .append(Doc::space())
                    .append(to_doc_term(snd))
                    .append(Doc::space())
                    .append("}"),
                _ => to_doc_arrow(term),
            }
        }

        fn to_doc_arrow(term: &Term) -> Doc<BoxDoc<()>> {
            match term {
                Term::FunArrowType(param_ty, body_ty) => Doc::nil()
                    .append(to_doc_app(param_ty))
                    .append(Doc::space())
                    .append("->")
                    .append(Doc::space())
                    .append(to_doc_app(body_ty)),
                _ => to_doc_app(term),
            }
        }

        fn to_doc_app(term: &Term) -> Doc<BoxDoc<()>> {
            match term {
                Term::FunApp(fun, args) => Doc::nil()
                    .append(to_doc_term(fun))
                    .append(Doc::space())
                    .append(Doc::intersperse(
                        args.iter().map(to_doc_atomic),
                        Doc::space(),
                    )),
                _ => to_doc_atomic(term),
            }
        }

        fn to_doc_atomic(term: &Term) -> Doc<BoxDoc<()>> {
            match term {
                Term::Var(name) => Doc::as_string(name),
                Term::Literal(literal) => literal.to_doc(),
                Term::Parens(term) => Doc::text("(").append(to_doc_term(term)).append(")"),
                Term::PairFst(pair) => to_doc_atomic(pair).append(".1"),
                Term::PairSnd(pair) => to_doc_atomic(pair).append(".2"),
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
        self.to_doc().pretty(100_000).fmt(f)
    }
}
