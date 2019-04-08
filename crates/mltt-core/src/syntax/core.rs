//! The checked core syntax.

use pretty::{BoxDoc, Doc};
use std::borrow::Cow;
use std::fmt;
use std::ops;
use std::rc::Rc;

use crate::syntax::{
    AppMode, DocString, Label, LiteralIntro, LiteralType, UniverseLevel, VarIndex,
};

#[derive(Clone, PartialEq)]
pub struct Module {
    pub items: Vec<Item>,
}

impl Module {
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::concat(self.items.iter().map(|item| {
            Doc::group(item.to_doc().append(";"))
                .append(Doc::newline())
                .append(Doc::newline())
        }))
    }

    pub fn to_display_doc(&self, env: &mut DisplayEnv) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::concat(self.items.iter().map(|item| {
            Doc::group(item.to_display_doc(env).append(";"))
                .append(Doc::newline())
                .append(Doc::newline())
        }))
    }
}

impl fmt::Debug for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let doc = self.to_doc().group();
        fmt::Display::fmt(&doc.pretty(1_000_000_000), f)
    }
}

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let doc = self.to_display_doc(&mut DisplayEnv::new()).group();
        fmt::Display::fmt(&doc.pretty(1_000_000_000), f)
    }
}

/// Top-level items
#[derive(Clone, PartialEq)]
pub struct Item {
    pub doc: DocString,
    pub label: Label,
    pub term_ty: RcTerm,
    pub term: RcTerm,
}

impl Item {
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::nil()
            .append(self.label.to_doc())
            .append(Doc::space())
            .append(":")
            .group()
            .append(
                Doc::nil()
                    .append(Doc::space())
                    .append(self.term_ty.to_doc())
                    .group()
                    .nest(4),
            )
            .append(Doc::space())
            .append("=")
            .group()
            .append(Doc::newline().append(self.term.to_doc()).group().nest(4))
    }

    pub fn to_display_doc(&self, env: &mut DisplayEnv) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::nil()
            .append(self.label.to_doc())
            .append(Doc::space())
            .append(":")
            .group()
            .append(
                Doc::nil()
                    .append(Doc::space())
                    .append(self.term_ty.to_display_doc(env))
                    .group()
                    .nest(4),
            )
            .append(Doc::space())
            .append("=")
            .group()
            .append(
                Doc::newline()
                    .append(self.term.to_display_doc(env))
                    .group()
                    .nest(4),
            )
    }
}

impl fmt::Debug for Item {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let doc = self.to_doc().group();
        fmt::Display::fmt(&doc.pretty(1_000_000_000), f)
    }
}

impl fmt::Display for Item {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let doc = self.to_display_doc(&mut DisplayEnv::new()).group();
        fmt::Display::fmt(&doc.pretty(1_000_000_000), f)
    }
}

#[derive(Clone, PartialEq)]
pub struct RcTerm {
    pub inner: Rc<Term>,
}

impl RcTerm {
    /// Construct a variable.
    pub fn var(index: impl Into<VarIndex>) -> RcTerm {
        RcTerm::from(Term::var(index))
    }

    /// Construct a primitive.
    pub fn prim(name: impl Into<String>) -> RcTerm {
        RcTerm::from(Term::prim(name.into()))
    }

    /// Construct a literal type.
    pub fn literal_ty(ty: impl Into<LiteralType>) -> RcTerm {
        RcTerm::from(Term::literal_ty(ty))
    }

    /// Construct a literal introduction.
    pub fn literal_intro(value: impl Into<LiteralIntro>) -> RcTerm {
        RcTerm::from(Term::literal_intro(value))
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

impl fmt::Display for RcTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.inner, f)
    }
}

/// Core terms
// TODO: explicitly annotate with types
#[derive(Clone, PartialEq)]
pub enum Term {
    /// Variables
    Var(VarIndex),
    /// Primitives
    Prim(String),

    /// Let bindings
    Let(RcTerm, RcTerm, RcTerm),

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
    pub fn var(index: impl Into<VarIndex>) -> Term {
        Term::Var(index.into())
    }

    /// Construct a primitive.
    pub fn prim(name: impl Into<String>) -> Term {
        Term::Prim(name.into())
    }

    /// Construct a literal type.
    pub fn literal_ty(ty: impl Into<LiteralType>) -> Term {
        Term::LiteralType(ty.into())
    }

    /// Construct a literal introduction.
    pub fn literal_intro(value: impl Into<LiteralIntro>) -> Term {
        Term::LiteralIntro(value.into())
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
            (Term::Let(def1, def_ty1, body1), Term::Let(def2, def_ty2, body2)) => {
                Term::alpha_eq(def1, def2)
                    && Term::alpha_eq(def_ty1, def_ty2)
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

    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        // FIXME: use proper precedences to mirror the Pratt parser?
        match self {
            Term::Var(index) => index.to_doc(),
            Term::Prim(name) => Doc::nil()
                .append("primitive")
                .append(Doc::space())
                .append(format!("{:?}", name)),
            Term::Let(def, def_ty, body) => Doc::nil()
                .append("let")
                .append(Doc::space())
                .append(Doc::text("_").append(Doc::space()).append(":").group())
                .append(Doc::space())
                .append(def_ty.to_doc())
                .append(Doc::space())
                .append("=")
                .group()
                .append(
                    Doc::space()
                        .append(def.to_doc())
                        .append(";")
                        .group()
                        .nest(4),
                )
                .append(Doc::space())
                .append("in")
                .append(Doc::space().append(body.to_doc()).group().nest(4)),

            Term::LiteralType(literal_ty) => literal_ty.to_doc(),
            Term::LiteralIntro(literal_intro) => literal_intro.to_doc(),
            Term::LiteralElim(scrutinee, clauses, default_body) => {
                let clauses = if clauses.is_empty() {
                    Doc::nil()
                } else {
                    Doc::concat(clauses.iter().map(|(literal_intro, body)| {
                        Doc::nil()
                            .append(literal_intro.to_doc())
                            .append(Doc::space())
                            .append("=>")
                            .append(Doc::space())
                            .append(body.to_doc())
                            .append(";")
                            .group()
                            .append(Doc::space())
                    }))
                };

                Doc::nil()
                    .append("case")
                    .append(Doc::space())
                    .append(scrutinee.to_arg_doc())
                    .append(Doc::space())
                    .append("{")
                    .group()
                    .append(
                        Doc::nil()
                            .append(Doc::space())
                            .append(clauses)
                            .append(
                                Doc::nil()
                                    .append("_")
                                    .append(Doc::space())
                                    .append("=>")
                                    .append(Doc::space())
                                    .append(default_body.to_doc())
                                    .append(";")
                                    .group(),
                            )
                            .group()
                            .nest(4),
                    )
                    .append(Doc::space())
                    .append("}")
            },

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
                    AppMode::Instance(label) => Doc::nil()
                        .append("{{")
                        .append(label.to_doc())
                        .append(Doc::space())
                        .append(":")
                        .append(Doc::space())
                        .append(param_ty.to_doc())
                        .append("}}"),
                };

                Doc::nil()
                    .append(Doc::text("Fun"))
                    .append(Doc::space())
                    .append(param.group())
                    .append(Doc::space())
                    .append("->")
                    .group()
                    .append(
                        Doc::space()
                            .append("(")
                            .append(body_ty.to_doc().group())
                            .append(")")
                            .nest(4),
                    )
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
                    AppMode::Instance(label) => Doc::nil()
                        .append("{{")
                        .append(label.to_doc())
                        .append(Doc::space())
                        .append("=")
                        .append(Doc::space())
                        .append("_")
                        .append("}}"),
                };

                Doc::nil()
                    .append("fun")
                    .append(Doc::space())
                    .append(param.group())
                    .append(Doc::space())
                    .append("=>")
                    .group()
                    .append(Doc::space().append(body.to_doc()).group().nest(4))
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
                    AppMode::Instance(label) => Doc::nil()
                        .append("{{")
                        .append(label.to_doc())
                        .append(Doc::space())
                        .append("=")
                        .append(Doc::space())
                        .append(arg.to_doc())
                        .append("}}"),
                };

                Doc::nil()
                    .append(fun.to_arg_doc())
                    .append(Doc::space())
                    .append(arg.group())
            },

            Term::RecordType(ty_fields) if ty_fields.is_empty() => Doc::text("Record {}"),
            Term::RecordType(ty_fields) => Doc::nil()
                .append("Record")
                .append(Doc::space())
                .append("{")
                .group()
                .append(
                    Doc::nil()
                        .append(Doc::space())
                        .append(Doc::intersperse(
                            ty_fields.iter().map(|(_, label, ty)| {
                                Doc::nil()
                                    .append(label.to_doc())
                                    .append(Doc::space())
                                    .append(":")
                                    .append(
                                        Doc::space()
                                            .append(ty.to_doc())
                                            .append(";")
                                            .group()
                                            .nest(4),
                                    )
                                    .group()
                            }),
                            Doc::space(),
                        ))
                        .nest(4),
                )
                .append(Doc::space())
                .append("}"),
            Term::RecordIntro(intro_fields) if intro_fields.is_empty() => Doc::text("record {}"),
            Term::RecordIntro(intro_fields) => Doc::nil()
                .append("record")
                .append(Doc::space())
                .append("{")
                .group()
                .append(
                    Doc::nil()
                        .append(Doc::newline())
                        .append(Doc::intersperse(
                            intro_fields.iter().map(|(label, term)| {
                                Doc::nil()
                                    .append(label.to_doc())
                                    .append(Doc::space())
                                    .append("=")
                                    .group()
                                    .append(
                                        Doc::space()
                                            .append(term.to_doc().group())
                                            .append(";")
                                            .group()
                                            .nest(4),
                                    )
                                    .group()
                            }),
                            Doc::newline(),
                        ))
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

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let doc = self.to_doc().group();
        fmt::Display::fmt(&doc.pretty(1_000_000_000), f)
    }
}

pub struct DisplayEnv {
    counter: usize,
    names: Vec<String>,
}

impl Default for DisplayEnv {
    fn default() -> DisplayEnv {
        DisplayEnv {
            counter: 0,
            names: vec![
                "String".to_owned(),
                "Char".to_owned(),
                "bool".to_owned(),
                "true".to_owned(),
                "false".to_owned(),
                "U8".to_owned(),
                "U16".to_owned(),
                "U32".to_owned(),
                "U64".to_owned(),
                "S8".to_owned(),
                "S16".to_owned(),
                "S32".to_owned(),
                "S64".to_owned(),
                "F32".to_owned(),
                "F64".to_owned(),
            ],
        }
    }
}

impl DisplayEnv {
    pub fn new() -> DisplayEnv {
        DisplayEnv {
            counter: 0,
            names: Vec::new(),
        }
    }

    fn lookup_name(&self, index: VarIndex) -> Cow<'_, str> {
        match self
            .names
            .len()
            .checked_sub(index.0 as usize + 1)
            .and_then(|i| self.names.get(i))
        {
            Some(name) => Cow::from(name),
            None => Cow::from(format!("free{}", index.0)),
        }
    }

    fn fresh_name(&mut self, _name_hint: Option<&str>) -> String {
        // TODO: use name hint to improve variable names
        let name = format!("x{}", self.counter);
        self.counter += 1;
        self.names.push(name.clone());
        name
    }

    fn pop_name(&mut self) {
        self.names.pop();
    }
}

impl Term {
    pub fn to_display_doc(&self, env: &mut DisplayEnv) -> Doc<'_, BoxDoc<'_, ()>> {
        // FIXME: use proper precedences to mirror the Pratt parser?
        match self {
            Term::Var(index) => Doc::as_string(env.lookup_name(*index)),
            Term::Prim(name) => Doc::nil()
                .append("primitive")
                .append(Doc::space())
                .append(format!("{:?}", name)),
            Term::Let(def, def_ty, body) => {
                let def_doc = def.to_display_doc(env);
                let def_ty_doc = def_ty.to_display_doc(env);
                let def_name = env.fresh_name(None);
                let body_doc = body.to_display_doc(env);
                env.pop_name();

                // TODO: flatten definitions
                Doc::nil()
                    .append("let")
                    .append(Doc::space())
                    .append(
                        Doc::nil()
                            .append(def_name)
                            .append(Doc::space())
                            .append(":")
                            .group(),
                    )
                    .append(Doc::space())
                    .append(def_ty_doc)
                    .append(Doc::space())
                    .append("=")
                    .group()
                    .append(Doc::space().append(def_doc).append(";").group().nest(4))
                    .append(Doc::space())
                    .append("in")
                    .append(Doc::space().append(body_doc).group().nest(4))
            },

            Term::LiteralType(literal_ty) => literal_ty.to_doc(),
            Term::LiteralIntro(literal_intro) => literal_intro.to_doc(),
            Term::LiteralElim(scrutinee, clauses, default_body) => {
                let scrutinee = scrutinee.to_display_arg_doc(env);
                let clauses = if clauses.is_empty() {
                    Doc::nil()
                } else {
                    Doc::concat(clauses.iter().map(|(literal_intro, body)| {
                        Doc::nil()
                            .append(literal_intro.to_doc())
                            .append(Doc::space())
                            .append("=>")
                            .append(Doc::space())
                            .append(body.to_display_doc(env))
                            .append(";")
                            .group()
                            .append(Doc::space())
                    }))
                };

                Doc::nil()
                    .append("case")
                    .append(Doc::space())
                    .append(scrutinee)
                    .append(Doc::space())
                    .append("{")
                    .group()
                    .append(
                        Doc::nil()
                            .append(Doc::space())
                            .append(clauses)
                            .append(
                                Doc::nil()
                                    .append("_")
                                    .append(Doc::space())
                                    .append("=>")
                                    .append(Doc::space())
                                    .append(default_body.to_display_doc(env))
                                    .append(";")
                                    .group(),
                            )
                            .group()
                            .nest(4),
                    )
                    .append(Doc::space())
                    .append("}")
            },

            Term::FunType(app_mode, param_ty, body_ty) => {
                let param_ty_doc = param_ty.to_display_doc(env);
                let param_doc = match app_mode {
                    AppMode::Explicit => {
                        let param_name = env.fresh_name(None);

                        Doc::nil()
                            .append("(")
                            .append(param_name)
                            .append(Doc::space())
                            .append(":")
                            .append(Doc::space())
                            .append(param_ty_doc)
                            .append(")")
                    },
                    AppMode::Implicit(label) => {
                        let param_name = env.fresh_name(Some(&label.0));

                        Doc::nil()
                            .append("{")
                            .append(label.to_doc())
                            .append(Doc::space())
                            // TODO: only use `as` if `label.0 != param_name`
                            .append("as")
                            .append(Doc::space())
                            .append(param_name)
                            .append(Doc::space())
                            .append(":")
                            .append(Doc::space())
                            .append(param_ty_doc)
                            .append("}")
                    },
                    AppMode::Instance(label) => {
                        let param_name = env.fresh_name(Some(&label.0));

                        Doc::nil()
                            .append("{{")
                            .append(label.to_doc())
                            .append(Doc::space())
                            // TODO: only use `as` if `label.0 != param_name`
                            .append("as")
                            .append(Doc::space())
                            .append(param_name)
                            .append(Doc::space())
                            .append(":")
                            .append(Doc::space())
                            .append(param_ty_doc)
                            .append("}}")
                    },
                };
                let body_ty_doc = body_ty.to_display_doc(env);
                env.pop_name();

                // TODO: use non-dependent function if possible
                // TODO: flatten params
                Doc::nil()
                    .append(Doc::text("Fun"))
                    .append(Doc::space())
                    .append(param_doc.group())
                    .append(Doc::space())
                    .append("->")
                    .group()
                    .append(
                        Doc::space()
                            .append("(")
                            .append(body_ty_doc.group())
                            .append(")")
                            .nest(4),
                    )
            },
            Term::FunIntro(app_mode, body) => {
                let param_doc = match app_mode {
                    AppMode::Explicit => Doc::as_string(env.fresh_name(None)),
                    AppMode::Implicit(label) => {
                        let param_name = env.fresh_name(Some(&label.0));

                        Doc::nil()
                            .append("{")
                            .append(label.to_doc())
                            .append(Doc::space())
                            // TODO: only use `as` if `label.0 != param_name`
                            .append("as")
                            .append(Doc::space())
                            .append(param_name)
                            .append(Doc::space())
                            .append("=")
                            .append(Doc::space())
                            .append("_")
                            .append("}")
                    },
                    AppMode::Instance(label) => {
                        let param_name = env.fresh_name(Some(&label.0));

                        Doc::nil()
                            .append("{{")
                            .append(label.to_doc())
                            .append(Doc::space())
                            // TODO: only use `as` if `label.0 != param_name`
                            .append("as")
                            .append(Doc::space())
                            .append(param_name)
                            .append(Doc::space())
                            .append("=")
                            .append(Doc::space())
                            .append("_")
                            .append("}}")
                    },
                };
                let body_doc = body.to_display_doc(env);
                env.pop_name();

                Doc::nil()
                    .append("fun")
                    .append(Doc::space())
                    .append(param_doc.group())
                    .append(Doc::space())
                    .append("=>")
                    .group()
                    .append(Doc::space().append(body_doc).group().nest(4))
            },
            Term::FunElim(fun, app_mode, arg) => {
                let arg = match app_mode {
                    AppMode::Explicit => arg.to_display_arg_doc(env),
                    AppMode::Implicit(label) => Doc::nil()
                        .append("{")
                        .append(label.to_doc())
                        .append(Doc::space())
                        .append("=")
                        .append(Doc::space())
                        .append(arg.to_display_doc(env))
                        .append("}"),
                    AppMode::Instance(label) => Doc::nil()
                        .append("{{")
                        .append(label.to_doc())
                        .append(Doc::space())
                        .append("=")
                        .append(Doc::space())
                        .append(arg.to_display_doc(env))
                        .append("}}"),
                };

                Doc::nil()
                    .append(fun.to_display_arg_doc(env))
                    .append(Doc::space())
                    .append(arg.group())
            },

            Term::RecordType(ty_fields) if ty_fields.is_empty() => Doc::text("Record {}"),
            Term::RecordType(ty_fields) => {
                let mut field_count = 0;

                let fields_doc = {
                    Doc::intersperse(
                        ty_fields.iter().map(|(_, label, ty)| {
                            let ty_doc = ty.to_display_doc(env);
                            let name = env.fresh_name(Some(&label.0));
                            field_count += 1;

                            Doc::nil()
                                .append(label.to_doc())
                                .append(Doc::space())
                                // TODO: only use `as` if `label != param_name`
                                .append("as")
                                .append(Doc::space())
                                .group()
                                .append(name)
                                .append(Doc::space())
                                .append(":")
                                .group()
                                .append(Doc::space().append(ty_doc).append(";").group().nest(4))
                                .group()
                        }),
                        Doc::space(),
                    )
                };

                for _ in 0..field_count {
                    env.pop_name();
                }

                Doc::nil()
                    .append("Record")
                    .append(Doc::space())
                    .append("{")
                    .group()
                    .append(Doc::space().append(fields_doc).nest(4))
                    .append(Doc::space())
                    .append("}")
            },
            Term::RecordIntro(intro_fields) if intro_fields.is_empty() => Doc::text("record {}"),
            Term::RecordIntro(intro_fields) => Doc::nil()
                .append("record")
                .append(Doc::space())
                .append("{")
                .group()
                .append(
                    Doc::nil()
                        .append(Doc::space())
                        .append(Doc::intersperse(
                            intro_fields.iter().map(|(label, term)| {
                                // TODO: parameter sugar
                                Doc::nil()
                                    .append(label.to_doc())
                                    .append(Doc::space())
                                    .append("=")
                                    .group()
                                    .append(
                                        Doc::space()
                                            .append(term.to_display_doc(env))
                                            .append(";")
                                            .group()
                                            .nest(4),
                                    )
                                    .group()
                            }),
                            Doc::space(),
                        ))
                        .nest(4),
                )
                .append(Doc::space())
                .append("}"),
            Term::RecordElim(record, label) => record
                .to_display_arg_doc(env)
                .append(".")
                .append(label.to_doc()),

            Term::Universe(level) => Doc::text("Type^").append(level.to_doc()),
        }
    }

    pub fn to_display_arg_doc(&self, env: &mut DisplayEnv) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            Term::Var(_) | Term::LiteralIntro(_) | Term::LiteralType(_) | Term::Universe(_) => {
                self.to_display_doc(env)
            },
            _ => Doc::nil()
                .append("(")
                .append(self.to_display_doc(env))
                .append(")"),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let doc = self.to_display_doc(&mut DisplayEnv::new()).group();
        fmt::Display::fmt(&doc.pretty(1_000_000_000), f)
    }
}
