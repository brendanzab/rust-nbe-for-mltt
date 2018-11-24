use syntax::{concrete, core, DbIndex, Ident, IdentHint, UniverseLevel};

pub enum DesugarError {
    UnboundVar(Ident),
}

pub fn desugar<'a>(
    concrete_term: &'a concrete::Term,
    env: &mut Vec<Option<&'a Ident>>,
) -> Result<core::RcTerm, DesugarError> {
    match *concrete_term {
        concrete::Term::Var(ref ident) => {
            match env
                .iter()
                .rev()
                .enumerate()
                .find(|(_, i)| **i == Some(ident))
            {
                None => Err(DesugarError::UnboundVar(ident.clone())),
                Some((index, _)) => Ok(core::RcTerm::from(core::Term::Var(
                    IdentHint(Some(ident.clone())),
                    DbIndex(index as u32),
                ))),
            }
        },
        concrete::Term::Let(ref ident, ref def, ref body) => {
            let def = desugar(def, env)?;
            env.push(Some(ident));
            let body = desugar(body, env)?;
            env.pop();

            Ok(core::RcTerm::from(core::Term::Let(
                IdentHint(Some(ident.clone())),
                def,
                body,
            )))
        },
        concrete::Term::Check(ref term, ref ann) => Ok(core::RcTerm::from(core::Term::Check(
            desugar(term, env)?,
            desugar(ann, env)?,
        ))),
        concrete::Term::Parens(ref term) => desugar(term, env),

        // Functions
        concrete::Term::FunType(ref ident, ref param_ty, ref body_ty) => {
            let param_ty = desugar(param_ty, env)?;
            env.push(ident.as_ref());
            let body_ty = desugar(body_ty, env)?;
            env.pop();

            Ok(core::RcTerm::from(core::Term::FunType(
                IdentHint(ident.clone()),
                param_ty,
                body_ty,
            )))
        },
        concrete::Term::FunIntro(ref ident, ref body) => {
            env.push(Some(ident));
            let body = desugar(body, env)?;
            env.pop();

            Ok(core::RcTerm::from(core::Term::FunIntro(
                IdentHint(Some(ident.clone())),
                body,
            )))
        },
        concrete::Term::FunApp(ref fun, ref args) => {
            args.iter().fold(desugar(fun, env), |acc, arg| {
                Ok(core::RcTerm::from(core::Term::FunApp(
                    acc?,
                    desugar(arg, env)?,
                )))
            })
        },

        // Pairs
        concrete::Term::PairType(ref ident, ref fst_ty, ref snd_ty) => {
            let fst_ty = desugar(fst_ty, env)?;
            env.push(ident.as_ref());
            let snd_ty = desugar(snd_ty, env)?;
            env.pop();

            Ok(core::RcTerm::from(core::Term::PairType(
                IdentHint(ident.clone()),
                fst_ty,
                snd_ty,
            )))
        },
        concrete::Term::PairIntro(ref fst, ref snd) => Ok(core::RcTerm::from(
            core::Term::PairIntro(desugar(fst, env)?, desugar(snd, env)?),
        )),
        concrete::Term::PairFst(ref pair) => {
            Ok(core::RcTerm::from(core::Term::PairFst(desugar(pair, env)?)))
        },
        concrete::Term::PairSnd(ref pair) => {
            Ok(core::RcTerm::from(core::Term::PairSnd(desugar(pair, env)?)))
        },

        // Universes
        concrete::Term::Universe(level) => match level {
            None => Ok(core::RcTerm::from(core::Term::Universe(UniverseLevel(0)))),
            Some(level) => Ok(core::RcTerm::from(core::Term::Universe(level))),
        },
    }
}
