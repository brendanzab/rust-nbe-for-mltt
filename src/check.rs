use im;

use nbe::{self, NbeError};
use syntax::core::{RcTerm, Term};
use syntax::domain::{self, RcType, RcValue, Value};
use syntax::{DbIndex, DbLevel, UniverseLevel};

#[derive(Debug, Clone)]
pub enum Entry {
    Term { term: RcValue, ann: RcType },
    TopLevel { term: RcValue, ann: RcType },
}

pub type Env = im::Vector<Entry>;

/// An error produced during type checking
#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    ExpectedFunType {
        found: RcType,
    },
    ExpectedPairType {
        found: RcType,
    },
    ExpectedUniverse {
        over: Option<UniverseLevel>,
        found: RcType,
    },
    ExpectedSubtype(RcType, RcType),
    AmbiguousTerm(RcTerm),
    UnboundVariable,
    Nbe(NbeError),
}

impl From<NbeError> for TypeError {
    fn from(src: NbeError) -> TypeError {
        TypeError::Nbe(src)
    }
}

fn env_to_domain_env(env: &Env) -> domain::Env {
    env.iter()
        .map(|entry| match *entry {
            Entry::Term { ref term, .. } => term.clone(),
            Entry::TopLevel { ref term, .. } => term.clone(),
        })
        .collect()
}

fn check_subtype(size: u32, ty1: &RcType, ty2: &RcType) -> Result<(), TypeError> {
    if nbe::check_subtype(size, ty1, ty2)? {
        Ok(())
    } else {
        Err(TypeError::ExpectedSubtype(ty1.clone(), ty2.clone()))
    }
}

pub fn check(env: &Env, size: u32, term: &RcTerm, ann: &RcType) -> Result<(), TypeError> {
    match *term.inner {
        Term::Let(ref def, ref body) => {
            let mut body_env = env.clone();
            body_env.push_front(Entry::Term {
                term: nbe::eval(def, &env_to_domain_env(env))?,
                ann: synth(env, size, def)?,
            });

            check(&body_env, size + 1, body, ann)
        },

        Term::FunType(ref ann, ref body) | Term::PairType(ref ann, ref body) => {
            check_ty(env, size, ann)?;
            let ann_value = nbe::eval(ann, &env_to_domain_env(env))?;

            let mut body_env = env.clone();
            body_env.push_front(Entry::Term {
                term: RcValue::var(DbLevel(size), ann_value.clone()),
                ann: ann_value,
            });

            check_ty(&body_env, size + 1, body)
        },
        Term::FunIntro(ref body) => match *ann.inner {
            Value::FunType(ref param_ty, ref body_ty) => {
                let var = RcValue::var(DbLevel(size), param_ty.clone());
                let body_ty = nbe::do_closure(body_ty, var.clone())?;

                let mut body_env = env.clone();
                body_env.push_front(Entry::Term {
                    term: var,
                    ann: param_ty.clone(),
                });

                check(&body_env, size + 1, body, &body_ty)
            },
            _ => Err(TypeError::ExpectedFunType { found: ann.clone() }),
        },

        Term::PairIntro(ref fst, ref snd) => match *ann.inner {
            Value::PairType(ref fst_ty, ref snd_ty) => {
                check(env, size, fst, fst_ty)?;
                let fst_value = nbe::eval(fst, &env_to_domain_env(env))?;
                check(env, size, snd, &nbe::do_closure(snd_ty, fst_value)?)
            },
            _ => Err(TypeError::ExpectedPairType { found: ann.clone() }),
        },

        Term::Universe(term_level) => match *ann.inner {
            Value::Universe(ann_level) if term_level < ann_level => Ok(()),
            _ => Err(TypeError::ExpectedUniverse {
                over: Some(term_level),
                found: ann.clone(),
            }),
        },

        _ => check_subtype(size, &synth(env, size, term)?, ann),
    }
}

pub fn synth(env: &Env, size: u32, term: &RcTerm) -> Result<RcType, TypeError> {
    match *term.inner {
        Term::Var(DbIndex(index)) => match env.get(index as usize) {
            None => Err(TypeError::UnboundVariable),
            Some(Entry::Term { ref ann, .. }) | Some(Entry::TopLevel { ref ann, .. }) => {
                Ok(ann.clone())
            },
        },
        Term::Let(ref def, ref body) => {
            let mut body_env = env.clone();
            body_env.push_front(Entry::Term {
                term: nbe::eval(def, &env_to_domain_env(env))?,
                ann: synth(env, size, def)?,
            });

            synth(&body_env, size + 1, body)
        },
        Term::Check(ref term, ref ann) => {
            let ann_value = nbe::eval(ann, &env_to_domain_env(env))?;
            check(env, size, term, &ann_value)?;
            Ok(ann_value)
        },

        Term::FunApp(ref fun, ref arg) => {
            let fun_ty = synth(env, size, fun)?;
            match *fun_ty.inner {
                Value::FunType(ref arg_ty, ref body_ty) => {
                    check(env, size, arg, arg_ty)?;
                    let arg_value = nbe::eval(arg, &env_to_domain_env(env))?;
                    Ok(nbe::do_closure(body_ty, arg_value)?)
                },
                _ => Err(TypeError::ExpectedFunType {
                    found: fun_ty.clone(),
                }),
            }
        },

        Term::PairFst(ref pair) => {
            let pair_ty = synth(env, size, pair)?;
            match *pair_ty.inner {
                Value::PairType(ref fst_ty, _) => Ok(fst_ty.clone()),
                _ => Err(TypeError::ExpectedPairType {
                    found: pair_ty.clone(),
                }),
            }
        },
        Term::PairSnd(ref pair) => {
            let pair_ty = synth(env, size, pair)?;
            match *pair_ty.inner {
                Value::PairType(_, ref snd_ty) => {
                    let fst = nbe::eval(
                        &RcTerm::from(Term::PairFst(pair.clone())),
                        &env_to_domain_env(env),
                    )?;
                    Ok(nbe::do_closure(snd_ty, fst)?)
                },
                _ => Err(TypeError::ExpectedPairType {
                    found: pair_ty.clone(),
                }),
            }
        },

        _ => Err(TypeError::AmbiguousTerm(term.clone())),
    }
}

pub fn check_ty(env: &Env, size: u32, ty: &RcTerm) -> Result<(), TypeError> {
    match *ty.inner {
        Term::Let(ref def, ref body) => {
            let mut body_env = env.clone();
            body_env.push_front(Entry::Term {
                term: nbe::eval(def, &env_to_domain_env(env))?,
                ann: synth(env, size, def)?,
            });

            check_ty(&body_env, size + 1, body)
        },

        Term::FunType(ref ann, ref body) | Term::PairType(ref ann, ref body) => {
            check_ty(env, size, ann)?;
            let ann_value = nbe::eval(ann, &env_to_domain_env(env))?;

            let mut body_env = env.clone();
            body_env.push_front(Entry::Term {
                term: RcValue::var(DbLevel(size), ann_value.clone()),
                ann: ann_value,
            });

            check_ty(&body_env, size + 1, body)
        },

        Term::Universe(_) => Ok(()),

        _ => {
            let synth_ty = synth(env, size, ty)?;
            match *synth_ty.inner {
                Value::Universe(_) => Ok(()),
                _ => Err(TypeError::ExpectedUniverse {
                    over: None,
                    found: synth_ty,
                }),
            }
        },
    }
}
