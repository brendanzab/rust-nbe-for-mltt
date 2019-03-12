//! The checked core syntax

use pretty::{BoxDoc, Doc};
use std::fmt;
use std::ops;
use std::rc::Rc;

use crate::syntax::{AppMode, Label, LiteralIntro, LiteralType, UniverseLevel, VarIndex};

/// Top-level items
#[derive(Debug, Clone, PartialEq)]
pub struct Item {
    pub doc: String,
    pub label: String,
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

impl ops::Deref for RcTerm {
    type Target = Term;

    fn deref(&self) -> &Term {
        self.as_ref()
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
    Var(VarIndex),
    /// Let bindings
    Let(RcTerm, RcTerm),

    /// Literal types
    LiteralType(LiteralType),
    /// Literal introductions
    LiteralIntro(LiteralIntro),

    /// Dependent function types
    FunType(AppMode, RcTerm, RcTerm),
    /// Introduce a function
    FunIntro(AppMode, RcTerm),
    /// Eliminate a function (application)
    FunElim(RcTerm, AppMode, RcTerm),

    /// Dependent record types
    RecordType(Vec<(String, Label, RcTerm)>),
    /// Introduce a record
    RecordIntro(Vec<(Label, RcTerm)>),
    /// Eliminate a record (projection)
    RecordElim(RcTerm, Label),

    /// Universe of types
    Universe(UniverseLevel),
}

impl Term {
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        // FIXME: use proper precedences to mirror the Pratt parser?
        match self {
            Term::Var(index) => index.to_doc(),
            Term::Let(def, body) => Doc::nil()
                .append("let")
                .append(Doc::space())
                .append("_")
                .append(Doc::space())
                .append("=")
                .append(Doc::space())
                .append(def.to_doc())
                .append(";")
                .append(Doc::space())
                .append("in")
                .append(Doc::space())
                .append(body.to_doc()),

            Term::LiteralType(literal_ty) => literal_ty.to_doc(),
            Term::LiteralIntro(literal_intro) => literal_intro.to_doc(),

            Term::FunType(app_mode, param_ty, body_ty) => {
                let param = match app_mode {
                    AppMode::Explicit => Doc::nil()
                        .append("(")
                        .append("_")
                        .append(Doc::space())
                        .append(":")
                        .append(Doc::space())
                        .append(param_ty.to_doc())
                        .append(")"),
                    AppMode::Implicit(label) => Doc::nil()
                        .append("{")
                        .append(label.to_doc())
                        .append(Doc::space())
                        .append(":")
                        .append(Doc::space())
                        .append(param_ty.to_doc())
                        .append("}"),
                };

                Doc::nil()
                    .append(Doc::group(
                        Doc::text("Fun").append(Doc::space()).append(param),
                    ))
                    .append(Doc::space())
                    .append("->")
                    .append(Doc::space())
                    .append("(")
                    .append(body_ty.to_doc())
                    .append(")")
            },
            Term::FunIntro(app_mode, body) => {
                let param = match app_mode {
                    AppMode::Explicit => Doc::text("_"),
                    AppMode::Implicit(label) => Doc::nil()
                        .append("{")
                        .append(label.to_doc())
                        .append(Doc::space())
                        .append("=")
                        .append(Doc::space())
                        .append("_")
                        .append("}"),
                };

                Doc::nil()
                    .append("fun")
                    .append(Doc::space())
                    .append(param)
                    .append(Doc::space())
                    .append("=>")
                    .append(Doc::space())
                    .append(body.to_doc())
            },
            Term::FunElim(fun, app_mode, arg) => {
                let arg = match app_mode {
                    AppMode::Explicit => arg.to_arg_doc(),
                    AppMode::Implicit(label) => Doc::nil()
                        .append("{")
                        .append(label.to_doc())
                        .append(Doc::space())
                        .append("=")
                        .append(Doc::space())
                        .append(arg.to_doc())
                        .append("}"),
                };

                Doc::nil()
                    .append(fun.to_arg_doc())
                    .append(Doc::space())
                    .append(arg)
            },

            Term::RecordType(ty_fields) if ty_fields.is_empty() => Doc::text("Record {}"),
            Term::RecordType(ty_fields) => Doc::nil()
                .append("Record")
                .append(Doc::space())
                .append("{")
                .append(Doc::newline())
                .append(
                    Doc::intersperse(
                        ty_fields.iter().map(|(_, label, ty)| {
                            Doc::nil()
                                .append(label.to_doc())
                                .append(Doc::space())
                                .append(":")
                                .append(Doc::space())
                                .append(ty.to_doc())
                                .append(";")
                        }),
                        Doc::newline(),
                    )
                    .nest(4),
                )
                .append(Doc::newline())
                .append("}"),
            Term::RecordIntro(intro_fields) if intro_fields.is_empty() => Doc::text("record {}"),
            Term::RecordIntro(intro_fields) => Doc::nil()
                .append("record")
                .append(Doc::space())
                .append("{")
                .append(Doc::newline())
                .append(
                    Doc::intersperse(
                        intro_fields.iter().map(|(label, term)| {
                            Doc::nil()
                                .append(label.to_doc())
                                .append(Doc::space())
                                .append("=")
                                .append(Doc::space())
                                .append(term.to_doc())
                                .append(";")
                        }),
                        Doc::newline(),
                    )
                    .nest(4),
                )
                .append(Doc::newline())
                .append("}"),
            Term::RecordElim(record, label) => {
                record.to_arg_doc().append(".").append(label.to_doc())
            },

            Term::Universe(level) => Doc::text("Type^").append(level.to_doc()),
        }
    }

    pub fn to_arg_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            Term::Var(_) | Term::LiteralIntro(_) | Term::LiteralType(_) | Term::Universe(_) => {
                self.to_doc()
            },
            _ => Doc::nil().append("(").append(self.to_doc()).append(")"),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_doc().group().pretty(1_000_000_000).fmt(f)
    }
}
