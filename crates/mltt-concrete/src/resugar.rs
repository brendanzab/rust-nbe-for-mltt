//! Convert the core syntax into the concrete syntax.
//!
//! We add back in syntactic sugar that was lost during elaboration, and also
//! the necessary parentheses needed to appropriately group expressions.

use mltt_core::syntax::{core, DbIndex, UniverseLevel};

use crate::syntax;

pub struct Env {
    counter: usize,
    names: Vec<String>,
}

impl Env {
    pub fn new() -> Env {
        Env {
            counter: 0,
            names: Vec::new(),
        }
    }

    pub fn lookup_index(&self, index: DbIndex) -> String {
        match self.names.get(index.0 as usize) {
            Some(name) => name.clone(),
            None => format!("free{}", index.0),
        }
    }

    pub fn with_binding<T>(&mut self, f: impl Fn(&mut Env) -> T) -> (String, T) {
        self.counter += 1;
        // TODO: use name hint to improve variable names
        let name = format!("x{}", self.counter);
        self.names.push(name.clone());
        let result = f(self);
        self.names.pop();
        (name, result)
    }
}

pub fn resugar(term: &core::RcTerm) -> syntax::Term {
    resugar_env(term, &mut Env::new())
}

pub fn resugar_env(term: &core::RcTerm, env: &mut Env) -> syntax::Term {
    // Using precedence climbing (mirroring the language grammar) in
    // order to cut down on extraneous parentheses.

    fn resugar_term(term: &core::RcTerm, env: &mut Env) -> syntax::Term {
        match term.as_ref() {
            core::Term::Let(def, /* def_ty, */ body) => {
                let def = resugar_app(def, env);
                let (def_name, body) = env.with_binding(|env| resugar_term(body, env));
                syntax::Term::Let(def_name, Box::new(def), Box::new(body))
            },
            core::Term::FunIntro(/* param_ty, */ body) => {
                let (param_name, body) = env.with_binding(|env| resugar_app(body, env));
                // TODO: flatten params
                syntax::Term::FunIntro(vec![syntax::Pattern::Var(param_name)], Box::new(body))
            },
            _ => resugar_arrow(term, env),
        }
    }

    fn resugar_arrow(term: &core::RcTerm, env: &mut Env) -> syntax::Term {
        match term.as_ref() {
            core::Term::FunType(param_ty, body_ty) => {
                let param_ty = resugar_term(param_ty, env);
                let (param_name, body_ty) = env.with_binding(|env| resugar_app(body_ty, env));
                // TODO: only use `param_name` if it is used in `body_ty`
                // TODO: flatten params
                syntax::Term::FunType(vec![(vec![param_name], param_ty)], Box::new(body_ty))
            },
            core::Term::RecordType(ty_fields) => {
                let ty_fields = ty_fields
                    .iter()
                    .map(|(_, label, ty)| syntax::RecordTypeField {
                        docs: Vec::new(),
                        label: label.0.clone(),
                        ann: resugar_term(ty, env),
                    })
                    .collect();

                syntax::Term::RecordType(ty_fields)
            },
            core::Term::RecordIntro(intro_fields) => {
                let intro_fields = intro_fields
                    .iter()
                    .map(|(label, term)| {
                        // TODO: Punned fields
                        // TODO: Function sugar
                        syntax::RecordIntroField::Explicit {
                            label: label.0.clone(),
                            patterns: Vec::new(),
                            term_ty: None,
                            term: resugar_term(term, env),
                        }
                    })
                    .collect();

                syntax::Term::RecordIntro(intro_fields)
            },
            _ => resugar_app(term, env),
        }
    }

    fn resugar_app(term: &core::RcTerm, env: &mut Env) -> syntax::Term {
        match term.as_ref() {
            core::Term::FunApp(fun, arg) => match resugar_term(fun, env) {
                syntax::Term::FunApp(fun, mut args) => {
                    args.push(resugar_atomic(arg, env));
                    syntax::Term::FunApp(fun, args)
                },
                fun => syntax::Term::FunApp(Box::new(fun), vec![resugar_atomic(arg, env)]),
            },
            _ => resugar_atomic(term, env),
        }
    }

    fn resugar_atomic(term: &core::RcTerm, env: &mut Env) -> syntax::Term {
        match term.as_ref() {
            core::Term::Var(index) => syntax::Term::Var(env.lookup_index(*index)),
            core::Term::RecordProj(record, label) => {
                syntax::Term::RecordProj(Box::new(resugar_atomic(record, env)), label.0.clone())
            },
            core::Term::Universe(UniverseLevel(0)) => syntax::Term::Universe(None),
            core::Term::Universe(UniverseLevel(level)) => syntax::Term::Universe(Some(*level)),
            _ => syntax::Term::Parens(Box::new(resugar_term(term, env))),
        }
    }

    resugar_term(term, env)
}
