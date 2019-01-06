//! Bidirectional type checking of the core syntax
//!
//! This is used to verify that the core syntax is correctly formed, for
//! debugging purposes.

use im;

use crate::nbe::{self, NbeError};
use crate::syntax::core::{RcTerm, Term};
use crate::syntax::domain::{self, RcType, RcValue, Value};
use crate::syntax::{DbIndex, DbLevel, UniverseLevel};

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

/// Check that a term conforms to a given type
pub fn check_term(env: &Env, size: u32, term: &RcTerm, expected_ty: &RcType) -> Result<(), TypeError> {
    match *term.inner {
        Term::Let(_, ref def, ref body) => {
            let mut body_env = env.clone();
            body_env.push_front(Entry::Term {
                term: nbe::eval(def, &env_to_domain_env(env))?,
                ann: synth_term(env, size, def)?,
            });

            check_term(&body_env, size + 1, body, expected_ty)
        },

        Term::FunType(_, ref ann_ty, ref body_ty) | Term::PairType(_, ref ann_ty, ref body_ty) => {
            check_term(env, size, ann_ty, expected_ty)?;
            let ann_ty_value = nbe::eval(ann_ty, &env_to_domain_env(env))?;

            let mut body_ty_env = env.clone();
            body_ty_env.push_front(Entry::Term {
                term: RcValue::var(DbLevel(size)),
                ann: ann_ty_value,
            });

            check_term(&body_ty_env, size + 1, body_ty, expected_ty)
        },
        Term::FunIntro(_, ref body) => match *expected_ty.inner {
            Value::FunType(_, ref param_ty, ref body_ty) => {
                let param = RcValue::var(DbLevel(size));
                let body_ty = nbe::do_closure_app(body_ty, param.clone())?;

                let mut body_env = env.clone();
                body_env.push_front(Entry::Term {
                    term: param,
                    ann: param_ty.clone(),
                });

                check_term(&body_env, size + 1, body, &body_ty)
            },
            _ => Err(TypeError::ExpectedFunType {
                found: expected_ty.clone(),
            }),
        },

        Term::PairIntro(ref fst, ref snd) => match *expected_ty.inner {
            Value::PairType(_, ref fst_ty, ref snd_ty) => {
                check_term(env, size, fst, fst_ty)?;
                let fst_value = nbe::eval(fst, &env_to_domain_env(env))?;
                check_term(env, size, snd, &nbe::do_closure_app(snd_ty, fst_value)?)
            },
            _ => Err(TypeError::ExpectedPairType {
                found: expected_ty.clone(),
            }),
        },

        Term::Universe(term_level) => match *expected_ty.inner {
            Value::Universe(ann_level) if term_level < ann_level => Ok(()),
            _ => Err(TypeError::ExpectedUniverse {
                over: Some(term_level),
                found: expected_ty.clone(),
            }),
        },

        _ => check_subtype(size, &synth_term(env, size, term)?, expected_ty),
    }
}

/// Synthesize the type of the term
pub fn synth_term(env: &Env, size: u32, term: &RcTerm) -> Result<RcType, TypeError> {
    match *term.inner {
        Term::Var(DbIndex(index)) => match env.get(index as usize) {
            None => Err(TypeError::UnboundVariable),
            Some(Entry::Term { ref ann, .. }) | Some(Entry::TopLevel { ref ann, .. }) => {
                Ok(ann.clone())
            },
        },
        Term::Let(_, ref def, ref body) => {
            let mut body_env = env.clone();
            body_env.push_front(Entry::Term {
                term: nbe::eval(def, &env_to_domain_env(env))?,
                ann: synth_term(env, size, def)?,
            });

            synth_term(&body_env, size + 1, body)
        },
        Term::Ann(ref term, ref ann) => {
            check_term_ty(context, raw_ann)?;
            let ann_value = nbe::eval(ann, &env_to_domain_env(env))?;
            check_term(env, size, term, &ann_value)?;
            Ok(ann_value)
        },

        Term::FunApp(ref fun, ref arg) => {
            let fun_ty = synth_term(env, size, fun)?;
            match *fun_ty.inner {
                Value::FunType(_, ref arg_ty, ref body_ty) => {
                    check_term(env, size, arg, arg_ty)?;
                    let arg_value = nbe::eval(arg, &env_to_domain_env(env))?;
                    Ok(nbe::do_closure_app(body_ty, arg_value)?)
                },
                _ => Err(TypeError::ExpectedFunType {
                    found: fun_ty.clone(),
                }),
            }
        },

        Term::PairFst(ref pair) => {
            let pair_ty = synth_term(env, size, pair)?;
            match *pair_ty.inner {
                Value::PairType(_, ref fst_ty, _) => Ok(fst_ty.clone()),
                _ => Err(TypeError::ExpectedPairType {
                    found: pair_ty.clone(),
                }),
            }
        },
        Term::PairSnd(ref pair) => {
            let pair_ty = synth_term(env, size, pair)?;
            match *pair_ty.inner {
                Value::PairType(_, _, ref snd_ty) => {
                    let fst = nbe::eval(
                        &RcTerm::from(Term::PairFst(pair.clone())),
                        &env_to_domain_env(env),
                    )?;
                    Ok(nbe::do_closure_app(snd_ty, fst)?)
                },
                _ => Err(TypeError::ExpectedPairType {
                    found: pair_ty.clone(),
                }),
            }
        },

        _ => Err(TypeError::AmbiguousTerm(term.clone())),
    }
}

/// Check that the given term is a type
pub fn check_term_ty(env: &Env, size: u32, term: &RcTerm) -> Result<(), TypeError> {
    match *term.inner {
        Term::Let(_, ref def, ref body) => {
            let mut body_env = env.clone();
            body_env.push_front(Entry::Term {
                term: nbe::eval(def, &env_to_domain_env(env))?,
                ann: synth_term(env, size, def)?,
            });

            check_term_ty(&body_env, size + 1, body)
        },

        Term::FunType(_, ref ann, ref body) | Term::PairType(_, ref ann, ref body) => {
            check_term_ty(env, size, ann)?;
            let ann_value = nbe::eval(ann, &env_to_domain_env(env))?;

            let mut body_env = env.clone();
            body_env.push_front(Entry::Term {
                term: RcValue::var(DbLevel(size)),
                ann: ann_value,
            });

            check_term_ty(&body_env, size + 1, body)
        },

        Term::Universe(_) => Ok(()),

        _ => {
            let synth_ty = synth_term(env, size, term)?;
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
