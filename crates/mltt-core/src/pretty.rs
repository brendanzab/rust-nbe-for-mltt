//! Pretty printing conversions

use pretty::{BoxDoc, Doc};
use std::borrow::Cow;

use super::{syntax, var, AppMode};

pub fn parens<'doc, A>(
    inner: impl Into<Doc<'doc, BoxDoc<'doc, A>, A>>,
) -> Doc<'doc, BoxDoc<'doc, A>, A> {
    Doc::nil().append("(").append(inner.into()).append(")")
}

pub fn declaration<'doc, A>(
    label: impl Into<Doc<'doc, BoxDoc<'doc, A>, A>>,
    term_ty: impl Into<Doc<'doc, BoxDoc<'doc, A>, A>>,
) -> Doc<'doc, BoxDoc<'doc, A>, A> {
    Doc::nil()
        .append(label.into())
        .append(Doc::space())
        .append(":")
        .group()
        .append(
            Doc::nil()
                .append(Doc::space())
                .append(term_ty.into())
                .group()
                .append(";")
                .nest(4),
        )
}

pub fn definition<'doc, A>(
    label: impl Into<Doc<'doc, BoxDoc<'doc, A>, A>>,
    term: impl Into<Doc<'doc, BoxDoc<'doc, A>, A>>,
) -> Doc<'doc, BoxDoc<'doc, A>, A> {
    Doc::nil()
        .append(label.into())
        .append(Doc::space())
        .append("=")
        .group()
        .append(
            Doc::nil()
                .append(Doc::space())
                .append(term.into())
                .group()
                .append(";")
                .nest(4),
        )
}

pub fn clause<'doc, A>(
    patterns: impl Into<Doc<'doc, BoxDoc<'doc, A>, A>>,
    body: impl Into<Doc<'doc, BoxDoc<'doc, A>, A>>,
) -> Doc<'doc, BoxDoc<'doc, A>, A> {
    Doc::nil()
        .append(patterns.into())
        .append(Doc::space())
        .append("=>")
        .append(Doc::space())
        .append(body.into())
        .append(";")
}

pub fn prim<'doc, A>(
    prim_name: impl Into<Doc<'doc, BoxDoc<'doc, A>, A>>,
) -> Doc<'doc, BoxDoc<'doc, A>, A> {
    Doc::nil()
        .append("primitive")
        .append(Doc::space())
        .append(prim_name.into())
}

pub fn ann<'doc, A>(
    term: impl Into<Doc<'doc, BoxDoc<'doc, A>, A>>,
    term_ty: impl Into<Doc<'doc, BoxDoc<'doc, A>, A>>,
) -> Doc<'doc, BoxDoc<'doc, A>, A> {
    Doc::nil()
        .append(term.into())
        .append(Doc::space())
        .append(":")
        .group()
        .append(Doc::space().append(term_ty.into()).group().nest(4))
}

pub fn record_elim<'doc, A>(
    term: impl Into<Doc<'doc, BoxDoc<'doc, A>, A>>,
    label: impl Into<Doc<'doc, BoxDoc<'doc, A>, A>>,
) -> Doc<'doc, BoxDoc<'doc, A>, A> {
    Doc::nil()
        .append(term.into())
        .append(".")
        .append(label.into())
}

pub fn universe<'doc, A>(
    level: impl Into<Doc<'doc, BoxDoc<'doc, A>, A>>,
) -> Doc<'doc, BoxDoc<'doc, A>, A> {
    Doc::nil().append("Type^").append(level.into())
}

/// An environment that can assist in pretty printing terms with pretty names.
#[derive(Debug, Clone)]
pub struct Env {
    counter: usize,
    names: var::Env<String>,
}

impl Env {
    pub fn new(names: var::Env<String>) -> Env {
        Env { counter: 0, names }
    }

    fn lookup_name(&self, var_index: var::Index) -> Cow<'_, str> {
        match self.names.lookup_entry(var_index) {
            Some(name) => Cow::from(name),
            None => Cow::from(format!("free{}", var_index)),
        }
    }

    fn fresh_name(&mut self, _name_hint: Option<&str>) -> String {
        // TODO: use name hint to improve variable names
        let name = format!("x{}", self.counter);
        self.counter += 1;
        self.names.add_entry(name.clone());
        name
    }
}

impl syntax::Module {
    pub fn to_debug_doc(&self) -> Doc<'static, BoxDoc<'static, ()>> {
        Doc::concat(self.items.iter().map(|item| {
            item.to_debug_doc()
                .append(Doc::newline())
                .append(Doc::newline())
        }))
    }

    pub fn to_display_doc(&self, env: &Env) -> Doc<'static, BoxDoc<'static, ()>> {
        let mut env = env.clone();
        items_to_display_doc(&self.items, &mut env)
    }
}

impl syntax::Item {
    pub fn to_debug_doc(&self) -> Doc<'static, BoxDoc<'static, ()>> {
        match self {
            syntax::Item::Declaration(_, label, term_ty) => {
                declaration(Doc::as_string(label), term_ty.to_debug_doc())
            },
            syntax::Item::Definition(_, label, term) => {
                definition(Doc::as_string(label), term.to_debug_doc())
            },
        }
    }
}

pub fn items_to_display_doc(
    items: &[syntax::Item],
    env: &mut Env,
) -> Doc<'static, BoxDoc<'static, ()>> {
    Doc::concat(items.iter().map(|item| {
        match item {
            syntax::Item::Declaration(_, label, term_ty) => {
                declaration(Doc::as_string(label), term_ty.to_display_doc(env))
                    .append(Doc::newline())
                    .append(Doc::newline())
            },
            syntax::Item::Definition(_, label, term) => {
                let doc = definition(Doc::as_string(label), term.to_display_doc(env))
                    .append(Doc::newline())
                    .append(Doc::newline());
                env.fresh_name(Some(&label.0));
                doc
            },
        }
    }))
}

impl syntax::Term {
    pub fn to_debug_doc(&self) -> Doc<'static, BoxDoc<'static, ()>> {
        // FIXME: use proper precedences to mirror the Pratt parser?
        match self {
            syntax::Term::Var(var_index) => Doc::as_string(var_index),
            syntax::Term::Meta(meta_index) => Doc::as_string(meta_index),
            syntax::Term::Prim(prim_name) => prim(Doc::as_string(prim_name)),

            syntax::Term::Ann(term, term_ty) => ann(term.to_debug_doc(), term_ty.to_debug_doc()),
            syntax::Term::Let(items, body) => Doc::nil()
                .append("let")
                .append(Doc::space())
                .append(Doc::concat(items.iter().map(|item| {
                    item.to_debug_doc()
                        .append(Doc::newline())
                        .append(Doc::newline())
                })))
                .append("in")
                .append(Doc::space().append(body.to_debug_doc()).group().nest(4)),

            syntax::Term::LiteralType(literal_ty) => Doc::as_string(literal_ty),
            syntax::Term::LiteralIntro(literal_intro) => Doc::as_string(literal_intro),
            syntax::Term::LiteralElim(scrutinee, clauses, default_body) => {
                let clauses = if clauses.is_empty() {
                    Doc::nil()
                } else {
                    Doc::concat(clauses.iter().map(|(literal_intro, body)| {
                        clause(Doc::as_string(literal_intro), body.to_debug_doc())
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
                            .append(clause("_", default_body.to_debug_doc()).group())
                            .group()
                            .nest(4),
                    )
                    .append(Doc::space())
                    .append("}")
            },

            syntax::Term::FunType(app_mode, param_ty, body_ty) => {
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
                        .append(Doc::as_string(label))
                        .append(Doc::space())
                        .append(":")
                        .group()
                        .append(Doc::space().append(param_ty.to_debug_doc()).nest(4))
                        .append("}"),
                    AppMode::Instance(label) => Doc::nil()
                        .append("{{")
                        .append(Doc::as_string(label))
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
                            .append(body_ty.to_debug_arg_doc())
                            .group()
                            .nest(4),
                    )
            },
            syntax::Term::FunIntro(app_mode, body) => {
                let param = match app_mode {
                    AppMode::Explicit => Doc::text("_"),
                    AppMode::Implicit(label) => Doc::nil()
                        .append("{")
                        .append(Doc::as_string(label))
                        .append(Doc::space())
                        .append("=")
                        .group()
                        .append(Doc::space().append("_").nest(4))
                        .append("}"),
                    AppMode::Instance(label) => Doc::nil()
                        .append("{{")
                        .append(Doc::as_string(label))
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
            syntax::Term::FunElim(fun, app_mode, arg) => {
                let arg = match app_mode {
                    AppMode::Explicit => arg.to_debug_arg_doc(),
                    AppMode::Implicit(label) => Doc::nil()
                        .append("{")
                        .append(Doc::as_string(label))
                        .append(Doc::space())
                        .append("=")
                        .group()
                        .append(Doc::space().append(arg.to_debug_doc()).nest(4))
                        .append("}"),
                    AppMode::Instance(label) => Doc::nil()
                        .append("{{")
                        .append(Doc::as_string(label))
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

            syntax::Term::RecordType(ty_fields) if ty_fields.is_empty() => Doc::text("Record {}"),
            syntax::Term::RecordType(ty_fields) => Doc::nil()
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
                                    .append(Doc::as_string(label))
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
            syntax::Term::RecordIntro(intro_fields) if intro_fields.is_empty() => {
                Doc::text("record {}")
            },
            syntax::Term::RecordIntro(intro_fields) => Doc::nil()
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
                                    .append(Doc::as_string(label))
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
            syntax::Term::RecordElim(record, label) => {
                record_elim(record.to_debug_doc(), Doc::as_string(label))
            },

            syntax::Term::Universe(level) => universe(Doc::as_string(level)),
        }
    }

    pub fn to_debug_arg_doc(&self) -> Doc<'static, BoxDoc<'static, ()>> {
        match self {
            syntax::Term::Var(_)
            | syntax::Term::Meta(_)
            | syntax::Term::LiteralIntro(_)
            | syntax::Term::LiteralType(_)
            | syntax::Term::RecordElim(_, _)
            | syntax::Term::Universe(_) => self.to_debug_doc(),
            _ => parens(self.to_debug_doc()),
        }
    }

    pub fn to_display_doc(&self, env: &Env) -> Doc<'static, BoxDoc<'static, ()>> {
        // FIXME: use proper precedences to mirror the Pratt parser?
        match self {
            syntax::Term::Var(var_index) => Doc::as_string(env.lookup_name(*var_index)),
            syntax::Term::Meta(meta_index) => Doc::as_string(meta_index),
            syntax::Term::Prim(prim_name) => prim(Doc::as_string(prim_name)),

            syntax::Term::Ann(term, term_ty) => {
                ann(term.to_display_doc(env), term_ty.to_display_doc(env))
            },
            syntax::Term::Let(items, body) => {
                let mut env = env.clone();
                let items_doc = items_to_display_doc(items, &mut env);

                // TODO: flatten definitions
                Doc::nil()
                    .append("let")
                    .append(Doc::space())
                    .append(items_doc)
                    .append("in")
                    .append(
                        Doc::space()
                            .append(body.to_display_doc(&env))
                            .group()
                            .nest(4),
                    )
            },

            syntax::Term::LiteralType(literal_ty) => Doc::as_string(literal_ty),
            syntax::Term::LiteralIntro(literal_intro) => Doc::as_string(literal_intro),
            syntax::Term::LiteralElim(scrutinee, clauses, default_body) => {
                let scrutinee = scrutinee.to_display_arg_doc(env);
                let clauses = if clauses.is_empty() {
                    Doc::nil()
                } else {
                    Doc::concat(clauses.iter().map(|(literal_intro, body)| {
                        clause(Doc::as_string(literal_intro), body.to_display_doc(env))
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
                            .append(clause("_", default_body.to_display_doc(env)).group())
                            .group()
                            .nest(4),
                    )
                    .append(Doc::space())
                    .append("}")
            },

            syntax::Term::FunType(app_mode, param_ty, body_ty) => {
                let mut env = env.clone();
                let mut body_ty = body_ty;
                let mut params = vec![(app_mode, param_ty)];
                while let syntax::Term::FunType(app_mode, param_ty, next_body_ty) = body_ty.as_ref()
                {
                    params.push((app_mode, param_ty));
                    body_ty = next_body_ty;
                }

                let params_doc = Doc::intersperse(
                    params.iter().map(|(app_mode, param_ty)| {
                        let param_ty_doc = param_ty.to_display_doc(&env);
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
                                        Doc::text("{").append(Doc::as_string(label)).group()
                                    } else {
                                        Doc::nil()
                                            .append("{")
                                            .append(Doc::as_string(label))
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
                                        Doc::text("{{").append(Doc::as_string(label)).group()
                                    } else {
                                        Doc::nil()
                                            .append("{{")
                                            .append(Doc::as_string(label))
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
                            .append(body_ty.to_display_arg_doc(&env))
                            .group()
                            .nest(4),
                    )
            },
            syntax::Term::FunIntro(app_mode, body) => {
                let mut env = env.clone();
                let mut body = body;
                let mut app_modes = vec![app_mode];
                while let syntax::Term::FunIntro(app_mode, next_body) = body.as_ref() {
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
                                    Doc::text("{").append(Doc::as_string(label)).group()
                                } else {
                                    Doc::nil()
                                        .append("{")
                                        .append(Doc::as_string(label))
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
                                    Doc::text("{{").append(Doc::as_string(label)).group()
                                } else {
                                    Doc::nil()
                                        .append("{{")
                                        .append(Doc::as_string(label))
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

                Doc::nil()
                    .append("fun")
                    .append(Doc::space())
                    .append(params_doc)
                    .append(Doc::space())
                    .append("=>")
                    .group()
                    .append(
                        Doc::space()
                            .append(body.to_display_doc(&env))
                            .group()
                            .nest(4),
                    )
            },
            syntax::Term::FunElim(fun, app_mode, arg) => {
                let mut fun = fun;
                let mut args = vec![(app_mode, arg)];
                while let syntax::Term::FunElim(next_fun, app_mode, arg) = fun.as_ref() {
                    args.push((app_mode, arg));
                    fun = next_fun;
                }

                let args_doc = Doc::intersperse(
                    args.iter().rev().map(|(app_mode, arg)| match app_mode {
                        AppMode::Explicit => arg.to_display_arg_doc(env).group(),
                        AppMode::Implicit(label) => Doc::nil()
                            .append("{")
                            .append(Doc::as_string(label))
                            .append(Doc::space())
                            .append("=")
                            .group()
                            .append(Doc::space().append(arg.to_display_doc(env)).nest(4))
                            .append("}")
                            .group(),
                        AppMode::Instance(label) => Doc::nil()
                            .append("{{")
                            .append(Doc::as_string(label))
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

            syntax::Term::RecordType(ty_fields) if ty_fields.is_empty() => Doc::text("Record {}"),
            syntax::Term::RecordType(ty_fields) => {
                let mut env = env.clone();

                let fields_doc = {
                    Doc::intersperse(
                        ty_fields.iter().map(|(_, label, ty)| {
                            let ty_doc = ty.to_display_doc(&env);
                            let field_name = env.fresh_name(Some(&label.0));

                            Doc::nil()
                                .append(if label.0 == field_name {
                                    Doc::as_string(label)
                                } else {
                                    Doc::nil()
                                        .append(Doc::as_string(label))
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

                Doc::nil()
                    .append("Record")
                    .append(Doc::space())
                    .append("{")
                    .group()
                    .append(Doc::space().append(fields_doc).nest(4))
                    .append(Doc::space())
                    .append("}")
            },
            syntax::Term::RecordIntro(intro_fields) if intro_fields.is_empty() => {
                Doc::text("record {}")
            },
            syntax::Term::RecordIntro(intro_fields) => Doc::nil()
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
                                    .append(Doc::as_string(label))
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
            syntax::Term::RecordElim(record, label) => {
                record_elim(record.to_display_doc(env), Doc::as_string(label))
            },

            syntax::Term::Universe(level) => universe(Doc::as_string(level)),
        }
    }

    pub fn to_display_arg_doc(&self, env: &Env) -> Doc<'static, BoxDoc<'static, ()>> {
        match self {
            syntax::Term::Var(_)
            | syntax::Term::Meta(_)
            | syntax::Term::LiteralIntro(_)
            | syntax::Term::LiteralType(_)
            | syntax::Term::RecordElim(_, _)
            | syntax::Term::Universe(_) => self.to_display_doc(env),
            _ => parens(self.to_display_doc(env)),
        }
    }
}
