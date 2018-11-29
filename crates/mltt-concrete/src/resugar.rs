use mltt_core::syntax::{core, DbIndex, IdentHint, UniverseLevel};

use crate::syntax::concrete;

pub struct Env {
    counter: usize,
    idents: Vec<String>,
}

impl Env {
    pub fn new() -> Env {
        Env {
            counter: 0,
            idents: Vec::new(),
        }
    }

    pub fn lookup_index(&self, index: DbIndex) -> String {
        match self.idents.get(index.0 as usize) {
            Some(ident) => ident.clone(),
            None => format!("free{}", index.0),
        }
    }

    pub fn with_binding<T>(
        &mut self,
        _ident: &IdentHint,
        f: impl Fn(&mut Env) -> T,
    ) -> (String, T) {
        self.counter += 1;
        // TODO: use ident hint to improve variable names
        let ident = format!("x{}", self.counter);
        self.idents.push(ident.clone());
        let result = f(self);
        self.idents.pop();
        (ident, result)
    }
}

pub fn resugar(term: &core::RcTerm) -> concrete::Term {
    resugar_env(term, &mut Env::new())
}

pub fn resugar_env(term: &core::RcTerm, env: &mut Env) -> concrete::Term {
    // Using precedence climbing (mirroring the language grammar) in
    // order to cut down on extraneous parentheses.

    fn resugar_term(term: &core::RcTerm, env: &mut Env) -> concrete::Term {
        match *term.inner {
            core::Term::Check(ref term, ref ann) => concrete::Term::PairIntro(
                Box::new(resugar_expr(term, env)),
                Box::new(resugar_app(ann, env)),
            ),
            _ => resugar_expr(term, env),
        }
    }

    fn resugar_expr(term: &core::RcTerm, env: &mut Env) -> concrete::Term {
        match *term.inner {
            core::Term::Let(ref ident, ref def, ref body) => {
                let def = resugar_app(def, env);
                let (ident, body) = env.with_binding(ident, |env| resugar_term(body, env));
                concrete::Term::Let(ident, Box::new(def), Box::new(body))
            },
            core::Term::FunIntro(ref ident, ref body) => {
                let (ident, body) = env.with_binding(ident, |env| resugar_app(body, env));
                concrete::Term::FunIntro(ident, Box::new(body))
            },
            _ => resugar_arrow(term, env),
        }
    }

    fn resugar_arrow(term: &core::RcTerm, env: &mut Env) -> concrete::Term {
        match *term.inner {
            core::Term::FunType(ref ident, ref param_ty, ref body_ty) => {
                let param_ty = resugar_term(param_ty, env);
                let (ident, body_ty) = env.with_binding(ident, |env| resugar_app(body_ty, env));
                // TODO: only use `ident` if it is used in `body_ty`
                concrete::Term::FunType(Some(ident), Box::new(param_ty), Box::new(body_ty))
            },
            core::Term::PairType(ref ident, ref fst_ty, ref snd_ty) => {
                let fst_ty = resugar_term(fst_ty, env);
                let (ident, snd_ty) = env.with_binding(ident, |env| resugar_app(snd_ty, env));
                // TODO: only use `ident` if it is used in `body_ty`
                concrete::Term::PairType(Some(ident), Box::new(fst_ty), Box::new(snd_ty))
            },
            _ => resugar_app(term, env),
        }
    }

    fn resugar_app(term: &core::RcTerm, env: &mut Env) -> concrete::Term {
        match *term.inner {
            core::Term::FunApp(ref fun, ref arg) => match resugar_term(fun, env) {
                concrete::Term::FunApp(fun, mut args) => {
                    args.push(resugar_atomic(arg, env));
                    concrete::Term::FunApp(fun, args)
                },
                fun => concrete::Term::FunApp(Box::new(fun), vec![resugar_atomic(arg, env)]),
            },
            _ => resugar_atomic(term, env),
        }
    }

    fn resugar_atomic(term: &core::RcTerm, env: &mut Env) -> concrete::Term {
        match *term.inner {
            core::Term::Var(index) => concrete::Term::Var(env.lookup_index(index)),
            core::Term::PairIntro(ref fst, ref snd) => concrete::Term::PairIntro(
                Box::new(resugar_term(fst, env)),
                Box::new(resugar_term(snd, env)),
            ),
            core::Term::PairFst(ref pair) => {
                concrete::Term::PairFst(Box::new(resugar_atomic(pair, env)))
            },
            core::Term::PairSnd(ref pair) => {
                concrete::Term::PairSnd(Box::new(resugar_atomic(pair, env)))
            },
            core::Term::Universe(UniverseLevel(0)) => concrete::Term::Universe(None),
            core::Term::Universe(UniverseLevel(level)) => concrete::Term::Universe(Some(level)),
            _ => concrete::Term::Parens(Box::new(resugar_term(term, env))),
        }
    }

    resugar_term(term, env)
}
