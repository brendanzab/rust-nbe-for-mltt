//! The core syntax of the language.

use std::fmt;
use std::ops;
use std::rc::Rc;

use super::literal::{LiteralIntro, LiteralType};
use crate::{meta, prim, var, AppMode, DocString, Label, UniverseLevel};

/// Top-level module.
#[derive(Clone, PartialEq)]
pub struct Module {
    pub items: Vec<Item>,
}

impl fmt::Debug for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let doc = self.to_debug_doc().group();
        fmt::Display::fmt(&doc.pretty(1_000_000_000), f)
    }
}

/// Top-level item.
#[derive(Clone, PartialEq)]
pub enum Item {
    /// Forward-declarations.
    Declaration(DocString, Label, RcTerm),
    /// Term definitions.
    Definition(DocString, Label, RcTerm),
}

impl fmt::Debug for Item {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let doc = self.to_debug_doc().group();
        fmt::Display::fmt(&doc.pretty(1_000_000_000), f)
    }
}

/// Reference counted term.
#[derive(Clone, PartialEq)]
pub struct RcTerm {
    /// The inner term.
    pub inner: Rc<Term>,
}

impl RcTerm {
    /// Construct a variable.
    pub fn var(index: impl Into<var::Index>) -> RcTerm {
        RcTerm::from(Term::var(index))
    }

    /// Construct a metavariable.
    pub fn meta(index: impl Into<meta::Index>) -> RcTerm {
        RcTerm::from(Term::meta(index))
    }

    /// Construct a primitive.
    pub fn prim(name: impl Into<prim::Name>) -> RcTerm {
        RcTerm::from(Term::prim(name))
    }

    /// Construct an annotated term.
    pub fn ann(term: impl Into<RcTerm>, term_ty: impl Into<RcTerm>) -> RcTerm {
        RcTerm::from(Term::ann(term, term_ty))
    }

    /// Construct a literal type.
    pub fn literal_ty(ty: impl Into<LiteralType>) -> RcTerm {
        RcTerm::from(Term::literal_ty(ty))
    }

    /// Construct a literal introduction.
    pub fn literal_intro(value: impl Into<LiteralIntro>) -> RcTerm {
        RcTerm::from(Term::literal_intro(value))
    }

    /// Construct a universe.
    pub fn universe(level: impl Into<UniverseLevel>) -> RcTerm {
        RcTerm::from(Term::universe(level))
    }
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

impl ops::Deref for RcTerm {
    type Target = Term;

    fn deref(&self) -> &Term {
        self.as_ref()
    }
}

impl fmt::Debug for RcTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.inner, f)
    }
}

/// Core terms.
// TODO: explicitly annotate with types
#[derive(Clone, PartialEq)]
pub enum Term {
    /// Variables
    Var(var::Index),
    /// Metavariables
    Meta(meta::Index),
    /// Primitives
    Prim(prim::Name),

    /// A term that is explicitly annotated with a type
    Ann(RcTerm, RcTerm),
    /// Let bindings
    Let(Vec<Item>, RcTerm),

    /// Literal types
    LiteralType(LiteralType),
    /// Literal introductions
    LiteralIntro(LiteralIntro),
    /// Eliminate a literal (case split on literals)
    ///
    /// We include a scrutinee, a list of clauses, and a default term. The
    /// clauses are sorted in ascending order by the literal to allow for
    /// efficient binary searching during evaluation.
    LiteralElim(RcTerm, Rc<[(LiteralIntro, RcTerm)]>, RcTerm),

    /// Dependent function types
    FunType(AppMode, RcTerm, RcTerm),
    /// Introduce a function
    FunIntro(AppMode, RcTerm),
    /// Eliminate a function (application)
    FunElim(RcTerm, AppMode, RcTerm),

    /// Dependent record types
    RecordType(Vec<(DocString, Label, RcTerm)>),
    /// Introduce a record
    RecordIntro(Vec<(Label, RcTerm)>),
    /// Eliminate a record (projection)
    RecordElim(RcTerm, Label),

    /// Universe of types
    Universe(UniverseLevel),
}

impl Term {
    /// Construct a variable.
    pub fn var(index: impl Into<var::Index>) -> Term {
        Term::Var(index.into())
    }

    /// Construct a metavariable.
    pub fn meta(index: impl Into<meta::Index>) -> Term {
        Term::Meta(index.into())
    }

    /// Construct a primitive.
    pub fn prim(name: impl Into<prim::Name>) -> Term {
        Term::Prim(name.into())
    }

    /// Construct an annotated term.
    pub fn ann(term: impl Into<RcTerm>, term_ty: impl Into<RcTerm>) -> Term {
        Term::Ann(term.into(), term_ty.into())
    }

    /// Construct a literal type.
    pub fn literal_ty(ty: impl Into<LiteralType>) -> Term {
        Term::LiteralType(ty.into())
    }

    /// Construct a literal introduction.
    pub fn literal_intro(value: impl Into<LiteralIntro>) -> Term {
        Term::LiteralIntro(value.into())
    }

    /// Construct a universe.
    pub fn universe(level: impl Into<UniverseLevel>) -> Term {
        Term::Universe(level.into())
    }

    /// Checks if a term is _alpha equivalent_ to another term.
    ///
    /// This means that the two terms share the same binding structure, while
    /// disregarding the actual names used for those binders. For example, we
    /// consider the following terms to be alpha equivalent:
    ///
    /// - `fun x => x` and `fun y => y`
    /// - `Fun (A : Type) -> A -> A` and `Fun (B : Type) -> B -> B`
    ///
    /// # References
    ///
    /// - https://en.wikipedia.org/wiki/Lambda_calculus#Alpha_equivalence
    /// - http://wiki.c2.com/?AlphaEquivalence
    /// - http://www.twelf.org/wiki/Alpha-equivalence
    pub fn alpha_eq(&self, other: &Term) -> bool {
        // The implementation of this is pretty straightforward, because we
        // are already using De Bruijn indices, so we just need to compare
        // variables using regular equality, while avoiding the comparison of
        // metadata, such as variable name hints and doc strings.
        match (self, other) {
            (Term::Var(index1), Term::Var(index2)) => index1 == index2,
            (Term::Prim(name1), Term::Prim(name2)) => name1 == name2,
            (Term::Ann(term1, term_ty1), Term::Ann(term2, term_ty2)) => {
                Term::alpha_eq(term1, term2) && Term::alpha_eq(term_ty1, term_ty2)
            },
            (Term::Let(items1, body1), Term::Let(items2, body2)) => {
                items1.len() == items2.len()
                    && Iterator::zip(items1.iter(), items2.iter()).all(|(item1, item2)| {
                        match (item1, item2) {
                            (Item::Declaration(_, _, ty1), Item::Declaration(_, _, ty2)) => {
                                Term::alpha_eq(ty1, ty2)
                            },
                            (Item::Definition(_, _, term1), Item::Definition(_, _, term2)) => {
                                Term::alpha_eq(term1, term2)
                            },
                            (_, _) => false,
                        }
                    })
                    && Term::alpha_eq(body1, body2)
            },

            (Term::LiteralType(literal_ty1), Term::LiteralType(literal_ty2)) => {
                LiteralType::alpha_eq(literal_ty1, literal_ty2)
            },
            (Term::LiteralIntro(literal_intro1), Term::LiteralIntro(literal_intro2)) => {
                LiteralIntro::alpha_eq(literal_intro1, literal_intro2)
            },
            (
                Term::LiteralElim(scrutinee1, clauses1, default1),
                Term::LiteralElim(scrutinee2, clauses2, default2),
            ) => {
                Term::alpha_eq(scrutinee1, scrutinee2)
                    && clauses1.len() == clauses2.len()
                    && Iterator::zip(clauses1.iter(), clauses2.iter())
                        .all(|((l1, b1), (l2, b2))| l1 == l2 && Term::alpha_eq(b1, b2))
                    && Term::alpha_eq(default1, default2)
            },

            (
                Term::FunType(app_mode1, param_ty1, body_ty1),
                Term::FunType(app_mode2, param_ty2, body_ty2),
            ) => {
                Term::alpha_eq(param_ty1, param_ty2)
                    && app_mode1 == app_mode2
                    && Term::alpha_eq(body_ty1, body_ty2)
            },
            (Term::FunIntro(app_mode1, body1), Term::FunIntro(app_mode2, body2)) => {
                app_mode1 == app_mode2 && Term::alpha_eq(body1, body2)
            },
            (Term::FunElim(fun1, app_mode1, arg1), Term::FunElim(fun2, app_mode2, arg2)) => {
                Term::alpha_eq(fun1, fun2) && app_mode1 == app_mode2 && Term::alpha_eq(arg1, arg2)
            },

            (Term::RecordType(ty_fields1), Term::RecordType(ty_fields2)) => {
                ty_fields1.len() == ty_fields2.len()
                    && Iterator::zip(ty_fields1.iter(), ty_fields2.iter())
                        .all(|((_, l1, t1), (_, l2, t2))| l1 == l2 && Term::alpha_eq(t1, t2))
            },
            (Term::RecordIntro(intro_fields1), Term::RecordIntro(intro_fields2)) => {
                intro_fields1.len() == intro_fields2.len()
                    && Iterator::zip(intro_fields1.iter(), intro_fields2.iter())
                        .all(|((l1, t1), (l2, t2))| l1 == l2 && Term::alpha_eq(t1, t2))
            },
            (Term::RecordElim(record1, label1), Term::RecordElim(record2, label2)) => {
                Term::alpha_eq(record1, record2) && label1 == label2
            },

            (Term::Universe(level1), Term::Universe(level2)) => level1 == level2,

            (_, _) => false,
        }
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let doc = self.to_debug_doc().group();
        fmt::Display::fmt(&doc.pretty(1_000_000_000), f)
    }
}
