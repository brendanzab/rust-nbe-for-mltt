use im;

use syntax::{concrete, core, DbIndex};

pub enum DesugarError {
    UnboundVar(concrete::Ident),
}

pub fn desugar(
    concrete_term: &concrete::Term,
    env: &im::Vector<Option<concrete::Ident>>,
) -> Result<core::RcTerm, DesugarError> {
    match *concrete_term {
        concrete::Term::Var(ref ident) => match env
            .iter()
            .enumerate()
            .find(|(_, i)| i.as_ref() == Some(ident))
        {
            None => Err(DesugarError::UnboundVar(ident.clone())),
            Some((index, _)) => Ok(core::RcTerm::from(core::Term::Var(DbIndex(index as u32)))),
        },
        concrete::Term::Let(ref ident, ref def, ref body) => {
            Ok(core::RcTerm::from(core::Term::Let(desugar(def, env)?, {
                let mut env = env.clone();
                env.push_front(Some(ident.clone()));
                desugar(body, &env)?
            })))
        },
        concrete::Term::Check(ref term, ref ann) => Ok(core::RcTerm::from(core::Term::Check(
            desugar(term, env)?,
            desugar(ann, env)?,
        ))),

        concrete::Term::FunType(ref ident, ref param_ty, ref body_ty) => Ok(core::RcTerm::from(
            core::Term::FunType(desugar(param_ty, env)?, {
                let mut env = env.clone();
                env.push_front(ident.clone());
                desugar(body_ty, &env)?
            }),
        )),
        concrete::Term::FunIntro(ref ident, ref body) => {
            Ok(core::RcTerm::from(core::Term::FunIntro({
                let mut env = env.clone();
                env.push_front(Some(ident.clone()));
                desugar(body, &env)?
            })))
        },
        concrete::Term::FunApp(ref fun, ref args) => {
            args.iter().fold(desugar(fun, env), |acc, arg| {
                Ok(core::RcTerm::from(core::Term::FunApp(
                    acc?,
                    desugar(arg, env)?,
                )))
            })
        },

        concrete::Term::PairType(ref ident, ref fst_ty, ref snd_ty) => Ok(core::RcTerm::from(
            core::Term::PairType(desugar(fst_ty, env)?, {
                let mut env = env.clone();
                env.push_front(ident.clone());
                desugar(snd_ty, &env)?
            }),
        )),
        concrete::Term::PairIntro(ref fst, ref snd) => Ok(core::RcTerm::from(
            core::Term::PairIntro(desugar(fst, env)?, desugar(snd, env)?),
        )),
        concrete::Term::PairFst(ref pair) => {
            Ok(core::RcTerm::from(core::Term::PairFst(desugar(pair, env)?)))
        },
        concrete::Term::PairSnd(ref pair) => {
            Ok(core::RcTerm::from(core::Term::PairSnd(desugar(pair, env)?)))
        },

        concrete::Term::Universe(level) => Ok(core::RcTerm::from(core::Term::Universe(level))),
    }
}
