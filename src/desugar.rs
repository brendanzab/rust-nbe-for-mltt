use syntax::{concrete, core, DbIndex, Ident, IdentHint, UniverseLevel};

struct Env<'a> {
    idents: Vec<Option<&'a Ident>>,
}

impl<'a> Env<'a> {
    fn new() -> Env<'a> {
        Env { idents: Vec::new() }
    }

    fn with_binding<T>(
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

pub fn desugar(term: &concrete::Term) -> Result<core::RcTerm, DesugarError> {
    desugar_env(term, &mut Env::new())
}

fn desugar_env<'a>(
    term: &'a concrete::Term,
    env: &mut Env<'a>,
) -> Result<core::RcTerm, DesugarError> {
    match *term {
        concrete::Term::Var(ref ident) => match env.lookup_ident(ident) {
            None => Err(DesugarError::UnboundVar(ident.clone())),
            Some(index) => Ok(core::RcTerm::from(core::Term::Var(index))),
        },
        concrete::Term::Let(ref ident, ref def, ref body) => {
            let ident_hint = IdentHint(Some(ident.clone()));
            let def = desugar_env(def, env)?;
            let body = env.with_binding(ident, |env| desugar_env(body, env))?;

            Ok(core::RcTerm::from(core::Term::Let(ident_hint, def, body)))
        },
        concrete::Term::Check(ref term, ref ann) => {
            let term = desugar_env(term, env)?;
            let ann = desugar_env(ann, env)?;

            Ok(core::RcTerm::from(core::Term::Check(term, ann)))
        },
        concrete::Term::Parens(ref term) => desugar_env(term, env),

        // Functions
        concrete::Term::FunType(ref ident, ref param_ty, ref body_ty) => {
            let ident_hint = IdentHint(ident.clone());
            let param_ty = desugar_env(param_ty, env)?;
            let body_ty = env.with_binding(ident, |env| desugar_env(body_ty, env))?;

            Ok(core::RcTerm::from(core::Term::FunType(
                ident_hint, param_ty, body_ty,
            )))
        },
        concrete::Term::FunIntro(ref ident, ref body) => {
            let ident_hint = IdentHint(Some(ident.clone()));
            let body = env.with_binding(ident, |env| desugar_env(body, env))?;

            Ok(core::RcTerm::from(core::Term::FunIntro(ident_hint, body)))
        },
        concrete::Term::FunApp(ref fun, ref args) => {
            args.iter().fold(desugar_env(fun, env), |acc, arg| {
                let arg = desugar_env(arg, env)?;
                Ok(core::RcTerm::from(core::Term::FunApp(acc?, arg)))
            })
        },

        // Pairs
        concrete::Term::PairType(ref ident, ref fst_ty, ref snd_ty) => {
            let ident_hint = IdentHint(ident.clone());
            let fst_ty = desugar_env(fst_ty, env)?;
            let snd_ty = env.with_binding(ident, |env| desugar_env(snd_ty, env))?;

            Ok(core::RcTerm::from(core::Term::PairType(
                ident_hint, fst_ty, snd_ty,
            )))
        },
        concrete::Term::PairIntro(ref fst, ref snd) => {
            let fst = desugar_env(fst, env)?;
            let snd = desugar_env(snd, env)?;

            Ok(core::RcTerm::from(core::Term::PairIntro(fst, snd)))
        },
        concrete::Term::PairFst(ref pair) => {
            let pair = desugar_env(pair, env)?;

            Ok(core::RcTerm::from(core::Term::PairFst(pair)))
        },
        concrete::Term::PairSnd(ref pair) => {
            let pair = desugar_env(pair, env)?;

            Ok(core::RcTerm::from(core::Term::PairSnd(pair)))
        },

        // Universes
        concrete::Term::Universe(level) => match level {
            None => Ok(core::RcTerm::from(core::Term::Universe(UniverseLevel(0)))),
            Some(level) => Ok(core::RcTerm::from(core::Term::Universe(level))),
        },
    }
}
