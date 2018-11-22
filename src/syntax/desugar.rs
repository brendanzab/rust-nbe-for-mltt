use im;

use syntax::{concrete, core, DbIndex};

pub enum DesugarError {
    UnboundVar(concrete::Ident),
}

pub fn desugar(
    concrete_term: &concrete::Term,
    env: &im::Vector<concrete::Ident>,
) -> Result<core::RcTerm, DesugarError> {
    match *concrete_term {
        concrete::Term::Var(ref ident) => match env.iter().enumerate().find(|(_, i)| *i == ident) {
            None => Err(DesugarError::UnboundVar(ident.clone())),
            Some((index, _)) => Ok(core::RcTerm::from(core::Term::Var(DbIndex(index as u32)))),
        },
        concrete::Term::Let(ref ident, ref def, ref body) => {
            Ok(core::RcTerm::from(core::Term::Let(desugar(def, env)?, {
                let mut env = env.clone();
                env.push_front(ident.clone());
                desugar(body, &env)?
            })))
        },
        concrete::Term::Check(ref term, ref ann) => Ok(core::RcTerm::from(core::Term::Check(
            desugar(term, env)?,
            desugar(ann, env)?,
        ))),

        concrete::Term::NatType => Ok(core::RcTerm::from(core::Term::NatType)),
        concrete::Term::NatSucc(ref nat) => {
            Ok(core::RcTerm::from(core::Term::NatSucc(desugar(nat, env)?)))
        },
        concrete::Term::NatLit(nat) => Ok((0..nat)
            .fold(core::RcTerm::from(core::Term::NatZero), |acc, _| {
                core::RcTerm::from(core::Term::NatSucc(acc))
            })),
        concrete::Term::NatRec {
            motive: (ref motive_ident, ref motive_body),
            ref zero,
            succ: (ref succ_ident1, ref succ_ident2, ref succ_body),
            ref nat,
        } => Ok(core::RcTerm::from(core::Term::NatRec(
            {
                let mut env = env.clone();
                env.push_front(motive_ident.clone());
                desugar(motive_body, &env)?
            },
            desugar(zero, &env)?,
            {
                let mut env = env.clone();
                env.push_front(succ_ident1.clone());
                env.push_front(succ_ident2.clone());
                desugar(succ_body, &env)?
            },
            desugar(nat, &env)?,
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
                env.push_front(ident.clone());
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
