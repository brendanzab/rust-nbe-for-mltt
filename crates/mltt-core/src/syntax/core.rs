//! The checked core syntax.

use pretty::{BoxDoc, Doc};
use std::borrow::Cow;
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

#[derive(Clone, PartialEq)]
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
    /// Primitive abort function
    // TODO: implement a more general primitive mechanism - perhaps something like:
    //
    // ```
    // primitive "abort" : Fun {A : Type} -> String -> A
    // ```
    PrimitiveAbort(RcTerm, String),
    /// Let bindings
    Let(RcTerm, RcTerm),

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
    RecordType(Vec<(String, Label, RcTerm)>),
    /// Introduce a record
    RecordIntro(Vec<(Label, RcTerm)>),
    /// Eliminate a record (projection)
    RecordElim(RcTerm, Label),

    /// Variant types
    VariantType(Vec<(String, Label, RcTerm)>),
    /// Introduce a variant
    VariantIntro(Label, RcTerm),
    /// Eliminate a record (projection)
    VariantElim(RcTerm, Vec<(Label, RcTerm)>),

    /// Universe of types
    Universe(UniverseLevel),
}

impl Term {
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        // FIXME: use proper precedences to mirror the Pratt parser?
        match self {
            Term::Var(index) => index.to_doc(),
            Term::PrimitiveAbort(ty, message) => Doc::nil()
                .append("(primitive \"abort\")")
                .append(Doc::space())
                .append("{")
                .append("A")
                .append(Doc::space())
                .append("=")
                .append(Doc::space())
                .append(ty.to_doc())
                .append("}")
                .append(Doc::space())
                .append(format!("{:?}", message)),
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
            Term::LiteralElim(scrutinee, clauses, default_body) => {
                let clauses = Doc::intersperse(
                    clauses.iter().map(|(literal_intro, body)| {
                        Doc::nil()
                            .append(literal_intro.to_doc())
                            .append(Doc::space())
                            .append("=>")
                            .append(Doc::space())
                            .append(body.to_doc())
                    }),
                    Doc::text(";").append(Doc::space()),
                );

                Doc::nil()
                    .append("case")
                    .append(Doc::space())
                    .append(scrutinee.to_arg_doc())
                    .append(Doc::space())
                    .append("{")
                    .append(Doc::space())
                    .append(clauses)
                    .append(";")
                    .append(Doc::space())
                    .append("_")
                    .append(Doc::space())
                    .append("=>")
                    .append(Doc::space())
                    .append(default_body.to_doc())
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
            Term::PrimitiveAbort(ty, message) => Doc::nil()
                .append("(primitive \"abort\")")
                .append(Doc::space())
                .append("{")
                .append("A")
                .append(Doc::space())
                .append("=")
                .append(Doc::space())
                .append(ty.to_doc())
                .append("}")
                .append(Doc::space())
                .append(format!("{:?}", message)),
            Term::Let(def, body) => {
                let def_doc = def.to_display_doc(env);
                let def_name = env.fresh_name(None);
                let body_doc = body.to_display_doc(env);
                env.pop_name();

                // TODO: flatten definitions
                Doc::nil()
                    .append("let")
                    .append(Doc::space())
                    .append(def_name)
                    .append(Doc::space())
                    .append("=")
                    .append(Doc::space())
                    .append(def_doc)
                    .append(";")
                    .append(Doc::space())
                    .append("in")
                    .append(Doc::space())
                    .append(body_doc)
            },

            Term::LiteralType(literal_ty) => literal_ty.to_doc(),
            Term::LiteralIntro(literal_intro) => literal_intro.to_doc(),
            Term::LiteralElim(scrutinee, clauses, default_body) => {
                let scrutinee = scrutinee.to_display_arg_doc(env);
                let clauses = Doc::intersperse(
                    clauses.iter().map(|(literal_intro, body)| {
                        Doc::nil()
                            .append(literal_intro.to_doc())
                            .append(Doc::space())
                            .append("=>")
                            .append(Doc::space())
                            .append(body.to_display_doc(env))
                    }),
                    Doc::text(";").append(Doc::space()),
                );
                let default_param_name = env.fresh_name(None);
                let default_body = default_body.to_display_doc(env);
                env.pop_name();

                Doc::nil()
                    .append("case")
                    .append(Doc::space())
                    .append(scrutinee)
                    .append(Doc::space())
                    .append("{")
                    .append(Doc::space())
                    .append(clauses)
                    .append(";")
                    .append(Doc::space())
                    .append(default_param_name)
                    .append(Doc::space())
                    .append("=>")
                    .append(Doc::space())
                    .append(default_body)
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
                };
                let body_ty_doc = body_ty.to_display_doc(env);
                env.pop_name();

                // TODO: use non-dependent function if possible
                // TODO: flatten params
                Doc::nil()
                    .append(Doc::group(
                        Doc::text("Fun").append(Doc::space()).append(param_doc),
                    ))
                    .append(Doc::space())
                    .append("->")
                    .append(Doc::space())
                    .append("(")
                    .append(body_ty_doc)
                    .append(")")
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
                };
                let body_doc = body.to_display_doc(env);
                env.pop_name();

                Doc::nil()
                    .append("fun")
                    .append(Doc::space())
                    .append(param_doc)
                    .append(Doc::space())
                    .append("=>")
                    .append(Doc::space())
                    .append(body_doc)
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
                };

                Doc::nil()
                    .append(fun.to_display_arg_doc(env))
                    .append(Doc::space())
                    .append(arg)
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
                                .append(name)
                                .append(Doc::space())
                                .append(":")
                                .append(Doc::space())
                                .append(ty_doc)
                                .append(";")
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
                    .append(Doc::space())
                    .append(fields_doc.nest(4))
                    .append(Doc::space())
                    .append("}")
            },
            Term::RecordIntro(intro_fields) if intro_fields.is_empty() => Doc::text("record {}"),
            Term::RecordIntro(intro_fields) => Doc::nil()
                .append("record")
                .append(Doc::space())
                .append("{")
                .append(Doc::space())
                .append(
                    Doc::intersperse(
                        intro_fields.iter().map(|(label, term)| {
                            // TODO: parameter sugar
                            Doc::nil()
                                .append(label.to_doc())
                                .append(Doc::space())
                                .append("=")
                                .append(Doc::space())
                                .append(term.to_display_doc(env))
                                .append(";")
                        }),
                        Doc::space(),
                    )
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
