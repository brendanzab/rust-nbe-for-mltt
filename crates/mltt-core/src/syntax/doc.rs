//! Pretty printing conversions

use pretty::{BoxDoc, Doc};
use std::borrow::Cow;

use super::core;
use super::{AppMode, VarIndex};

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

impl core::Module {
    pub fn to_debug_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::concat(self.items.iter().map(|item| {
            Doc::group(item.to_debug_doc().append(";"))
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

impl core::Item {
    pub fn to_debug_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::nil()
            .append(self.label.to_doc())
            .append(Doc::space())
            .append(":")
            .group()
            .append(
                Doc::nil()
                    .append(Doc::space())
                    .append(self.term_ty.to_debug_doc())
                    .group()
                    .nest(4),
            )
            .append(Doc::space())
            .append("=")
            .group()
            .append(
                Doc::newline()
                    .append(self.term.to_debug_doc())
                    .group()
                    .nest(4),
            )
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

impl core::Term {
    pub fn to_debug_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        // FIXME: use proper precedences to mirror the Pratt parser?
        match self {
            core::Term::Var(index) => index.to_doc(),
            core::Term::Prim(name) => Doc::nil()
                .append("primitive")
                .append(Doc::space())
                .append(format!("{:?}", name)),
            core::Term::Let(def, def_ty, body) => Doc::nil()
                .append("let")
                .append(Doc::space())
                .append(Doc::text("_").append(Doc::space()).append(":").group())
                .append(Doc::space())
                .append(def_ty.to_debug_doc())
                .append(Doc::space())
                .append("=")
                .group()
                .append(
                    Doc::space()
                        .append(def.to_debug_doc())
                        .append(";")
                        .group()
                        .nest(4),
                )
                .append(Doc::space())
                .append("in")
                .append(Doc::space().append(body.to_debug_doc()).group().nest(4)),

            core::Term::LiteralType(literal_ty) => literal_ty.to_doc(),
            core::Term::LiteralIntro(literal_intro) => literal_intro.to_doc(),
            core::Term::LiteralElim(scrutinee, clauses, default_body) => {
                let clauses = if clauses.is_empty() {
                    Doc::nil()
                } else {
                    Doc::concat(clauses.iter().map(|(literal_intro, body)| {
                        Doc::nil()
                            .append(literal_intro.to_doc())
                            .append(Doc::space())
                            .append("=>")
                            .append(Doc::space())
                            .append(body.to_debug_doc())
                            .append(";")
                            .group()
                            .append(Doc::space())
                    }))
                };

                Doc::nil()
                    .append("case")
                    .append(Doc::space())
                    .append(scrutinee.to_debug_arg_doc())
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
                                    .append(default_body.to_debug_doc())
                                    .append(";")
                                    .group(),
                            )
                            .group()
                            .nest(4),
                    )
                    .append(Doc::space())
                    .append("}")
            },

            core::Term::FunType(app_mode, param_ty, body_ty) => {
                let param = match app_mode {
                    AppMode::Explicit => Doc::nil()
                        .append("(")
                        .append("_")
                        .append(Doc::space())
                        .append(":")
                        .append(Doc::space())
                        .append(param_ty.to_debug_doc())
                        .append(")"),
                    AppMode::Implicit(label) => Doc::nil()
                        .append("{")
                        .append(label.to_doc())
                        .append(Doc::space())
                        .append(":")
                        .append(Doc::space())
                        .append(param_ty.to_debug_doc())
                        .append("}"),
                    AppMode::Instance(label) => Doc::nil()
                        .append("{{")
                        .append(label.to_doc())
                        .append(Doc::space())
                        .append(":")
                        .append(Doc::space())
                        .append(param_ty.to_debug_doc())
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
                            .append(body_ty.to_debug_doc().group())
                            .append(")")
                            .nest(4),
                    )
            },
            core::Term::FunIntro(app_mode, body) => {
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
                    .append(Doc::space().append(body.to_debug_doc()).group().nest(4))
            },
            core::Term::FunElim(fun, app_mode, arg) => {
                let arg = match app_mode {
                    AppMode::Explicit => arg.to_debug_arg_doc(),
                    AppMode::Implicit(label) => Doc::nil()
                        .append("{")
                        .append(label.to_doc())
                        .append(Doc::space())
                        .append("=")
                        .append(Doc::space())
                        .append(arg.to_debug_doc())
                        .append("}"),
                    AppMode::Instance(label) => Doc::nil()
                        .append("{{")
                        .append(label.to_doc())
                        .append(Doc::space())
                        .append("=")
                        .append(Doc::space())
                        .append(arg.to_debug_doc())
                        .append("}}"),
                };

                Doc::nil()
                    .append(fun.to_debug_arg_doc())
                    .append(Doc::space())
                    .append(arg.group())
            },

            core::Term::RecordType(ty_fields) if ty_fields.is_empty() => Doc::text("Record {}"),
            core::Term::RecordType(ty_fields) => Doc::nil()
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
                                            .append(ty.to_debug_doc())
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
            core::Term::RecordIntro(intro_fields) if intro_fields.is_empty() => {
                Doc::text("record {}")
            },
            core::Term::RecordIntro(intro_fields) => Doc::nil()
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
                                            .append(term.to_debug_doc().group())
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
            core::Term::RecordElim(record, label) => {
                record.to_debug_arg_doc().append(".").append(label.to_doc())
            },

            core::Term::Universe(level) => Doc::text("Type^").append(level.to_doc()),
        }
    }

    pub fn to_debug_arg_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            core::Term::Var(_)
            | core::Term::LiteralIntro(_)
            | core::Term::LiteralType(_)
            | core::Term::Universe(_) => self.to_debug_doc(),
            _ => Doc::nil()
                .append("(")
                .append(self.to_debug_doc())
                .append(")"),
        }
    }

    pub fn to_display_doc(&self, env: &mut DisplayEnv) -> Doc<'_, BoxDoc<'_, ()>> {
        // FIXME: use proper precedences to mirror the Pratt parser?
        match self {
            core::Term::Var(index) => Doc::as_string(env.lookup_name(*index)),
            core::Term::Prim(name) => Doc::nil()
                .append("primitive")
                .append(Doc::space())
                .append(format!("{:?}", name)),
            core::Term::Let(def, def_ty, body) => {
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

            core::Term::LiteralType(literal_ty) => literal_ty.to_doc(),
            core::Term::LiteralIntro(literal_intro) => literal_intro.to_doc(),
            core::Term::LiteralElim(scrutinee, clauses, default_body) => {
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

            core::Term::FunType(app_mode, param_ty, body_ty) => {
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
            core::Term::FunIntro(app_mode, body) => {
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
            core::Term::FunElim(fun, app_mode, arg) => {
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

            core::Term::RecordType(ty_fields) if ty_fields.is_empty() => Doc::text("Record {}"),
            core::Term::RecordType(ty_fields) => {
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
            core::Term::RecordIntro(intro_fields) if intro_fields.is_empty() => {
                Doc::text("record {}")
            },
            core::Term::RecordIntro(intro_fields) => Doc::nil()
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
            core::Term::RecordElim(record, label) => record
                .to_display_arg_doc(env)
                .append(".")
                .append(label.to_doc()),

            core::Term::Universe(level) => Doc::text("Type^").append(level.to_doc()),
        }
    }

    pub fn to_display_arg_doc(&self, env: &mut DisplayEnv) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            core::Term::Var(_)
            | core::Term::LiteralIntro(_)
            | core::Term::LiteralType(_)
            | core::Term::Universe(_) => self.to_display_doc(env),
            _ => Doc::nil()
                .append("(")
                .append(self.to_display_doc(env))
                .append(")"),
        }
    }
}