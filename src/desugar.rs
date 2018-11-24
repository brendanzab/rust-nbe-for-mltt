use syntax::{concrete, core, DbIndex, Ident, IdentHint, UniverseLevel};

struct Env<'a> {
    idents: Vec<Option<&'a Ident>>,
}

impl<'a> Env<'a> {
    fn new() -> Env<'a> {
        Env { idents: Vec::new() }
    }

    fn with_ident<T>(
        &mut self,
        ident: impl Into<Option<&'a Ident>>,
        f: impl Fn(&mut Env<'a>) -> T,
    ) -> T {
        self.idents.push(ident.into());
        let result = f(self);
        self.idents.pop();
        result
    }

    fn lookup_ident(&self, ident: &Ident) -> Option<DbIndex> {
        self.idents
            .iter()
            .rev()
            .enumerate()
            .find(|(_, i)| **i == Some(ident))
            .map(|(index, _)| DbIndex(index as u32))
    }
}

pub enum DesugarError {
    UnboundVar(Ident),
}

pub fn desugar(concrete_term: &concrete::Term) -> Result<core::RcTerm, DesugarError> {
    desugar_env(concrete_term, &mut Env::new())
}

fn desugar_env<'a>(
    concrete_term: &'a concrete::Term,
    env: &mut Env<'a>,
) -> Result<core::RcTerm, DesugarError> {
    match *concrete_term {
        concrete::Term::Var(ref ident) => match env.lookup_ident(ident) {
            None => Err(DesugarError::UnboundVar(ident.clone())),
            Some(index) => Ok(core::RcTerm::from(core::Term::Var(
                IdentHint(Some(ident.clone())),
                index,
            ))),
        },
        concrete::Term::Let(ref ident, ref def, ref body) => {
            let def = desugar_env(def, env)?;
            let body = env.with_ident(ident, |env| desugar_env(body, env))?;
            Ok(core::RcTerm::from(core::Term::Let(
                IdentHint(Some(ident.clone())),
                def,
                body,
            )))
        },
        concrete::Term::Check(ref term, ref ann) => Ok(core::RcTerm::from(core::Term::Check(
            desugar_env(term, env)?,
            desugar_env(ann, env)?,
        ))),
        concrete::Term::Parens(ref term) => desugar_env(term, env),

        // Functions
        concrete::Term::FunType(ref ident, ref param_ty, ref body_ty) => {
            let param_ty = desugar_env(param_ty, env)?;
            let body_ty = env.with_ident(ident, |env| desugar_env(body_ty, env))?;
            Ok(core::RcTerm::from(core::Term::FunType(
                IdentHint(ident.clone()),
                param_ty,
                body_ty,
            )))
        },
        concrete::Term::FunIntro(ref ident, ref body) => {
            let body = env.with_ident(ident, |env| desugar_env(body, env))?;
            Ok(core::RcTerm::from(core::Term::FunIntro(
                IdentHint(Some(ident.clone())),
                body,
            )))
        },
        concrete::Term::FunApp(ref fun, ref args) => {
            args.iter().fold(desugar_env(fun, env), |acc, arg| {
                Ok(core::RcTerm::from(core::Term::FunApp(
                    acc?,
                    desugar_env(arg, env)?,
                )))
            })
        },

        // Pairs
        concrete::Term::PairType(ref ident, ref fst_ty, ref snd_ty) => {
            let fst_ty = desugar_env(fst_ty, env)?;
            let snd_ty = env.with_ident(ident, |env| desugar_env(snd_ty, env))?;
            Ok(core::RcTerm::from(core::Term::PairType(
                IdentHint(ident.clone()),
                fst_ty,
                snd_ty,
            )))
        },
        concrete::Term::PairIntro(ref fst, ref snd) => Ok(core::RcTerm::from(
            core::Term::PairIntro(desugar_env(fst, env)?, desugar_env(snd, env)?),
        )),
        concrete::Term::PairFst(ref pair) => Ok(core::RcTerm::from(core::Term::PairFst(
            desugar_env(pair, env)?,
        ))),
        concrete::Term::PairSnd(ref pair) => Ok(core::RcTerm::from(core::Term::PairSnd(
            desugar_env(pair, env)?,
        ))),

        // Universes
        concrete::Term::Universe(level) => match level {
            None => Ok(core::RcTerm::from(core::Term::Universe(UniverseLevel(0)))),
            Some(level) => Ok(core::RcTerm::from(core::Term::Universe(level))),
        },
    }
}
