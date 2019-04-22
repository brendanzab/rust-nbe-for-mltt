//! Pretty printing conversions

use pretty::{BoxDoc, Doc};
use std::borrow::Cow;

use super::core;
use super::{AppMode, Label, LiteralIntro, LiteralType, UniverseLevel, VarIndex};

/// An environment that can assist in pretty printing terms with pretty names.
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

impl VarIndex {
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::as_string(format!("@{}", self.0))
    }
}

impl LiteralType {
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            LiteralType::String => Doc::text("String"),
            LiteralType::Char => Doc::text("Char"),
            LiteralType::Bool => Doc::text("Bool"),
            LiteralType::U8 => Doc::text("U8"),
            LiteralType::U16 => Doc::text("U16"),
            LiteralType::U32 => Doc::text("U32"),
            LiteralType::U64 => Doc::text("U64"),
            LiteralType::S8 => Doc::text("S8"),
            LiteralType::S16 => Doc::text("S16"),
            LiteralType::S32 => Doc::text("S32"),
            LiteralType::S64 => Doc::text("S64"),
            LiteralType::F32 => Doc::text("F32"),
            LiteralType::F64 => Doc::text("F64"),
        }
    }
}

impl LiteralIntro {
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            LiteralIntro::String(value) => Doc::text(format!("{:?}", value)),
            LiteralIntro::Char(value) => Doc::text(format!("{:?}", value)),
            LiteralIntro::Bool(true) => Doc::text("true"),
            LiteralIntro::Bool(false) => Doc::text("false"),
            LiteralIntro::U8(value) => Doc::as_string(&value),
            LiteralIntro::U16(value) => Doc::as_string(&value),
            LiteralIntro::U32(value) => Doc::as_string(&value),
            LiteralIntro::U64(value) => Doc::as_string(&value),
            LiteralIntro::S8(value) => Doc::as_string(&value),
            LiteralIntro::S16(value) => Doc::as_string(&value),
            LiteralIntro::S32(value) => Doc::as_string(&value),
            LiteralIntro::S64(value) => Doc::as_string(&value),
            LiteralIntro::F32(value) => Doc::as_string(&value),
            LiteralIntro::F64(value) => Doc::as_string(&value),
        }
    }
}

impl Label {
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::text(&self.0)
    }
}

impl UniverseLevel {
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::as_string(&self.0)
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
        let (num_defs, items_doc) = items_to_display_doc(&self.items, env);
        for _ in 0..num_defs {
            env.pop_name();
        }

        items_doc
    }
}

impl core::Item {
    pub fn to_debug_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            core::Item::Declaration(_, label, term_ty) => Doc::nil()
                .append(label.to_doc())
                .append(Doc::space())
                .append(":")
                .group()
                .append(
                    Doc::nil()
                        .append(Doc::space())
                        .append(term_ty.to_debug_doc())
                        .group()
                        .nest(4),
                ),
            core::Item::Definition(_, label, term) => Doc::nil()
                .append(label.to_doc())
                .append(Doc::space())
                .append("=")
                .group()
                .append(Doc::newline().append(term.to_debug_doc()).group().nest(4)),
        }
    }
}

pub fn items_to_display_doc<'doc>(
    items: &'doc [core::Item],
    env: &mut DisplayEnv,
) -> (usize, Doc<'doc, BoxDoc<'doc, ()>>) {
    let mut num_defs = 0;
    let item_docs = items
        .iter()
        .map(|item| match item {
            core::Item::Declaration(_, label, term_ty) => Doc::nil()
                .append(label.to_doc())
                .append(Doc::space())
                .append(":")
                .group()
                .append(
                    Doc::nil()
                        .append(Doc::space())
                        .append(term_ty.to_display_doc(env))
                        .group()
                        .append(";")
                        .nest(4),
                )
                .append(Doc::newline())
                .append(Doc::newline()),
            core::Item::Definition(_, label, term) => {
                let doc = Doc::nil()
                    .append(label.to_doc())
                    .append(Doc::space())
                    .append("=")
                    .group()
                    .append(
                        Doc::newline()
                            .append(term.to_display_doc(env))
                            .group()
                            .append(";")
                            .nest(4),
                    )
                    .append(Doc::newline())
                    .append(Doc::newline());
                env.fresh_name(Some(&label.0));
                num_defs += 1;
                doc
            },
        })
        .collect::<Vec<_>>();

    (num_defs, Doc::concat(item_docs))
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

            core::Term::Ann(term, term_ty) => Doc::nil()
                .append(term.to_debug_doc())
                .append(Doc::space())
                .append(":")
                .group()
                .append(Doc::space().append(term_ty.to_debug_doc()).group().nest(4)),
            core::Term::Let(items, body) => Doc::nil()
                .append("let")
                .append(Doc::space())
                .append(Doc::concat(items.iter().map(|item| {
                    Doc::nil()
                        .append(item.to_debug_doc())
                        .append(";")
                        .append(Doc::newline())
                        .append(Doc::newline())
                })))
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
                        .group()
                        .append(Doc::space().append(param_ty.to_debug_doc()).nest(4))
                        .append(")"),
                    AppMode::Implicit(label) => Doc::nil()
                        .append("{")
                        .append(label.to_doc())
                        .append(Doc::space())
                        .append(":")
                        .group()
                        .append(Doc::space().append(param_ty.to_debug_doc()).nest(4))
                        .append("}"),
                    AppMode::Instance(label) => Doc::nil()
                        .append("{{")
                        .append(label.to_doc())
                        .append(Doc::space())
                        .append(":")
                        .group()
                        .append(Doc::space().append(param_ty.to_debug_doc()).nest(4))
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
                        .group()
                        .append(Doc::space().append("_").nest(4))
                        .append("}"),
                    AppMode::Instance(label) => Doc::nil()
                        .append("{{")
                        .append(label.to_doc())
                        .append(Doc::space())
                        .append("=")
                        .group()
                        .append(Doc::space().append("_").nest(4))
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
                        .group()
                        .append(Doc::space().append(arg.to_debug_doc()).nest(4))
                        .append("}"),
                    AppMode::Instance(label) => Doc::nil()
                        .append("{{")
                        .append(label.to_doc())
                        .append(Doc::space())
                        .append("=")
                        .group()
                        .append(Doc::space().append(arg.to_debug_doc()).nest(4))
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
            | core::Term::RecordElim(_, _)
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

            core::Term::Ann(term, term_ty) => Doc::nil()
                .append(term.to_display_doc(env))
                .append(Doc::space())
                .append(":")
                .group()
                .append(
                    Doc::space()
                        .append(term_ty.to_display_doc(env))
                        .group()
                        .nest(4),
                ),
            core::Term::Let(items, body) => {
                let (num_defs, items_doc) = items_to_display_doc(items, env);
                let body_doc = body.to_display_doc(env);
                for _ in 0..num_defs {
                    env.pop_name();
                }

                // TODO: flatten definitions
                Doc::nil()
                    .append("let")
                    .append(Doc::space())
                    .append(items_doc)
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
                let mut body_ty = body_ty;
                let mut params = vec![(app_mode, param_ty)];
                while let core::Term::FunType(app_mode, param_ty, next_body_ty) = body_ty.as_ref() {
                    params.push((app_mode, param_ty));
                    body_ty = next_body_ty;
                }

                let params_doc = Doc::intersperse(
                    params.iter().map(|(app_mode, param_ty)| {
                        let param_ty_doc = param_ty.to_display_doc(env);
                        match app_mode {
                            AppMode::Explicit => {
                                let param_name = env.fresh_name(None);

                                Doc::nil()
                                    .append("(")
                                    .append(param_name)
                                    .append(Doc::space())
                                    .append(":")
                                    .group()
                                    .append(Doc::space().append(param_ty_doc).nest(4))
                                    .append(")")
                                    .group()
                            },
                            AppMode::Implicit(label) => {
                                let param_name = env.fresh_name(Some(&label.0));

                                Doc::nil()
                                    .append(if label.0 == param_name {
                                        Doc::text("{").append(label.to_doc()).group()
                                    } else {
                                        Doc::nil()
                                            .append("{")
                                            .append(label.to_doc())
                                            .append(Doc::space())
                                            .append("=")
                                            .group()
                                            .append(Doc::space().append(param_name).nest(4))
                                    })
                                    .append(Doc::space())
                                    .append(":")
                                    .group()
                                    .append(Doc::space().append(param_ty_doc).nest(4))
                                    .append("}")
                                    .group()
                            },
                            AppMode::Instance(label) => {
                                let param_name = env.fresh_name(Some(&label.0));

                                Doc::nil()
                                    .append(if label.0 == param_name {
                                        Doc::text("{{").append(label.to_doc()).group()
                                    } else {
                                        Doc::nil()
                                            .append("{{")
                                            .append(label.to_doc())
                                            .append(Doc::space())
                                            .append("=")
                                            .group()
                                            .append(Doc::space().append(param_name).nest(4))
                                    })
                                    .append(Doc::space())
                                    .append(":")
                                    .group()
                                    .append(Doc::space().append(param_ty_doc).nest(4))
                                    .append("}}")
                                    .group()
                            },
                        }
                    }),
                    Doc::space(),
                );

                let body_ty_doc = body_ty.to_display_doc(env);

                for _ in params {
                    env.pop_name();
                }

                // TODO: use non-dependent function if possible
                // TODO: flatten params
                Doc::nil()
                    .append(Doc::text("Fun"))
                    .append(Doc::space().append(params_doc).nest(4))
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
                let mut body = body;
                let mut app_modes = vec![app_mode];
                while let core::Term::FunIntro(app_mode, next_body) = body.as_ref() {
                    app_modes.push(app_mode);
                    body = next_body;
                }

                let params_doc = Doc::intersperse(
                    app_modes.iter().map(|app_mode| match app_mode {
                        AppMode::Explicit => Doc::as_string(env.fresh_name(None)).group(),
                        AppMode::Implicit(label) => {
                            let param_name = env.fresh_name(Some(&label.0));

                            Doc::nil()
                                .append(if label.0 == param_name {
                                    Doc::text("{").append(label.to_doc()).group()
                                } else {
                                    Doc::nil()
                                        .append("{")
                                        .append(label.to_doc())
                                        .append(Doc::space())
                                        .append("=")
                                        .group()
                                        .append(Doc::space().append(param_name).nest(4))
                                })
                                .append("}")
                                .group()
                        },
                        AppMode::Instance(label) => {
                            let param_name = env.fresh_name(Some(&label.0));

                            Doc::nil()
                                .append(if label.0 == param_name {
                                    Doc::text("{{").append(label.to_doc()).group()
                                } else {
                                    Doc::nil()
                                        .append("{{")
                                        .append(label.to_doc())
                                        .append(Doc::space())
                                        .append("=")
                                        .group()
                                        .append(Doc::space().append(param_name).nest(4))
                                })
                                .append("}}")
                                .group()
                        },
                    }),
                    Doc::space(),
                );

                let body_doc = body.to_display_doc(env);

                for _ in app_modes {
                    env.pop_name();
                }

                Doc::nil()
                    .append("fun")
                    .append(Doc::space())
                    .append(params_doc)
                    .append(Doc::space())
                    .append("=>")
                    .group()
                    .append(Doc::space().append(body_doc).group().nest(4))
            },
            core::Term::FunElim(fun, app_mode, arg) => {
                let mut fun = fun;
                let mut args = vec![(app_mode, arg)];
                while let core::Term::FunElim(next_fun, app_mode, arg) = fun.as_ref() {
                    args.push((app_mode, arg));
                    fun = next_fun;
                }

                let args_doc = Doc::intersperse(
                    args.iter().rev().map(|(app_mode, arg)| match app_mode {
                        AppMode::Explicit => arg.to_display_arg_doc(env).group(),
                        AppMode::Implicit(label) => Doc::nil()
                            .append("{")
                            .append(label.to_doc())
                            .append(Doc::space())
                            .append("=")
                            .group()
                            .append(Doc::space().append(arg.to_display_doc(env)).nest(4))
                            .append("}")
                            .group(),
                        AppMode::Instance(label) => Doc::nil()
                            .append("{{")
                            .append(label.to_doc())
                            .append(Doc::space())
                            .append("=")
                            .group()
                            .append(Doc::space().append(arg.to_display_doc(env)).nest(4))
                            .append("}}")
                            .group(),
                    }),
                    Doc::space(),
                );

                Doc::nil()
                    .append(fun.to_display_arg_doc(env))
                    .append(Doc::space().append(args_doc).nest(4))
            },

            core::Term::RecordType(ty_fields) if ty_fields.is_empty() => Doc::text("Record {}"),
            core::Term::RecordType(ty_fields) => {
                let mut field_count = 0;

                let fields_doc = {
                    Doc::intersperse(
                        ty_fields.iter().map(|(_, label, ty)| {
                            let ty_doc = ty.to_display_doc(env);
                            let field_name = env.fresh_name(Some(&label.0));
                            field_count += 1;

                            Doc::nil()
                                .append(if label.0 == field_name {
                                    label.to_doc()
                                } else {
                                    Doc::nil()
                                        .append(label.to_doc())
                                        .append(Doc::space())
                                        .append("=")
                                        .group()
                                        .append(Doc::space().append(field_name))
                                        .group()
                                })
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
            | core::Term::RecordElim(_, _)
            | core::Term::Universe(_) => self.to_display_doc(env),
            _ => Doc::nil()
                .append("(")
                .append(self.to_display_doc(env))
                .append(")"),
        }
    }
}
