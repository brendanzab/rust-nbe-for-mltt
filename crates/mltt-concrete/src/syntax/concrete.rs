//! The concrete syntax

use pretty::{BoxDoc, Doc};

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    Definition { name: String, ann: Term, def: Term },
}

/// Concrete terms
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// Variables
    Var(String),
    /// Let bindings
    Let(String, Box<Term>, Box<Term>),
    /// A term that is explicitly annotated with a type
    Ann(Box<Term>, Box<Term>),
    /// A parenthesized term
    Parens(Box<Term>),

    /// Dependent function type
    ///
    /// Also known as a _pi type_ or _dependent product type_.
    FunType(Option<String>, Box<Term>, Box<Term>),
    /// Introduce a function
    ///
    /// Also known as a _lambda expression_ or _anonymous function_.
    FunIntro(String, Box<Term>),
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
            match *term {
                Term::Ann(ref term, ref ann) => Doc::nil()
                    .append(to_doc_expr(term))
                    .append(Doc::space())
                    .append(":")
                    .append(Doc::space())
                    .append(to_doc_app(ann)),
                _ => to_doc_expr(term),
            }
        }

        fn to_doc_expr(term: &Term) -> Doc<BoxDoc<()>> {
            match *term {
                Term::Let(ref ident, ref def, ref body) => Doc::nil()
                    .append("let")
                    .append(Doc::space())
                    .append(Doc::as_string(ident))
                    .append(Doc::space())
                    .append("=")
                    .append(Doc::space())
                    .append(to_doc_app(def))
                    .append(Doc::space())
                    .append("in")
                    .append(Doc::space())
                    .append(to_doc_term(body)),
                Term::FunIntro(ref ident, ref body) => Doc::nil()
                    .append("\\")
                    .append(Doc::as_string(ident))
                    .append(Doc::space())
                    .append("=>")
                    .append(Doc::space())
                    .append(to_doc_app(body)),
                _ => to_doc_arrow(term),
            }
        }

        fn to_doc_arrow(term: &Term) -> Doc<BoxDoc<()>> {
            match *term {
                Term::FunType(None, ref param_ty, ref body_ty) => Doc::nil()
                    .append(to_doc_app(param_ty))
                    .append(Doc::space())
                    .append("->")
                    .append(Doc::space())
                    .append(to_doc_app(body_ty)),
                Term::FunType(Some(ref ident), ref param_ty, ref body_ty) => Doc::nil()
                    .append(Doc::group(
                        Doc::nil()
                            .append("(")
                            .append(Doc::as_string(ident))
                            .append(Doc::space())
                            .append(":")
                            .append(Doc::space())
                            .append(to_doc_term(param_ty))
                            .append(")"),
                    ))
                    .append(Doc::space())
                    .append("->")
                    .append(Doc::space())
                    .append(to_doc_app(body_ty)),
                Term::PairType(None, ref fst_ty, ref snd_ty) => Doc::nil()
                    .append(to_doc_term(fst_ty))
                    .append(Doc::space())
                    .append("*")
                    .append(Doc::space())
                    .append(to_doc_term(snd_ty)),
                Term::PairType(Some(ref ident), ref fst_ty, ref snd_ty) => Doc::nil()
                    .append(Doc::group(
                        Doc::nil()
                            .append("(")
                            .append(Doc::as_string(ident))
                            .append(Doc::space())
                            .append(":")
                            .append(Doc::space())
                            .append(to_doc_term(fst_ty))
                            .append(")"),
                    ))
                    .append(Doc::space())
                    .append("*")
                    .append(Doc::space())
                    .append(to_doc_app(snd_ty)),
                _ => to_doc_app(term),
            }
        }

        fn to_doc_app(term: &Term) -> Doc<BoxDoc<()>> {
            match *term {
                Term::FunApp(ref fun, ref args) => Doc::nil()
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
            match *term {
                Term::Var(ref ident) => Doc::as_string(ident),
                Term::Parens(ref term) => Doc::text("(").append(to_doc_term(term)).append(")"),
                Term::PairIntro(ref fst, ref snd) => Doc::nil()
                    .append("<")
                    .append(to_doc_term(fst))
                    .append(",")
                    .append(Doc::space())
                    .append(to_doc_term(snd))
                    .append(">"),
                Term::PairFst(ref pair) => to_doc_atomic(pair).append(".1"),
                Term::PairSnd(ref pair) => to_doc_atomic(pair).append(".2"),
                Term::Universe(None) => Doc::text("Type"),
                Term::Universe(Some(level)) => Doc::text("Type^").append(Doc::as_string(level)),
                _ => Doc::text("(").append(to_doc_term(term)).append(")"),
            }
        }

        to_doc_term(self)
    }
}
