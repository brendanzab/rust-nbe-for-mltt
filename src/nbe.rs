//! Normalization by evaluation

use syntax::core::{self, RcTerm, Term};
use syntax::domain::{Closure, Env, Neutral, Nf, RcNeutral, RcType, RcValue, Value};
use syntax::{DbIndex, DbLevel};

/// An error produced during normalization
///
/// If a term has been successfully type checked prior to evaluation or
/// normalization, then this error should never be produced.
#[derive(Debug, Clone, PartialEq)]
pub struct NbeError {
    pub message: String,
}

impl NbeError {
    pub fn new(message: impl Into<String>) -> NbeError {
        NbeError {
            message: message.into(),
        }
    }
}

/// Return the first element of a pair
fn do_pair_fst(pair: &RcValue) -> Result<RcValue, NbeError> {
    match *pair.inner {
        Value::PairIntro(ref fst, _) => Ok(fst.clone()),
        Value::Neutral { ref ann, ref term } => match *ann.inner {
            Value::PairType(ref ann_ty, _) => Ok(RcValue::from(Value::Neutral {
                term: RcNeutral::from(Neutral::PairFst(term.clone())),
                ann: ann_ty.clone(),
            })),
            _ => Err(NbeError::new("do_pair_fst: not a pair type")),
        },
        _ => Err(NbeError::new("do_pair_fst: not a pair")),
    }
}

/// Return the second element of a pair
fn do_pair_snd(pair: &RcValue) -> Result<RcValue, NbeError> {
    match *pair.inner {
        Value::PairIntro(_, ref snd) => Ok(snd.clone()),
        Value::Neutral { ref ann, ref term } => match *ann.inner {
            Value::PairType(_, ref closure) => {
                let fst = do_pair_fst(pair)?;
                let ann = do_closure(closure, fst)?;
                let term = RcNeutral::from(Neutral::PairSnd(term.clone()));

                Ok(RcValue::from(Value::Neutral { term, ann }))
            },
            _ => Err(NbeError::new("do_pair_snd: not a pair type")),
        },
        _ => Err(NbeError::new("do_pair_snd: not a pair")),
    }
}

/// Run a closure with the given argument
pub fn do_closure(closure: &Closure, arg: RcValue) -> Result<RcValue, NbeError> {
    let mut env = closure.env.clone();
    env.push_front(arg);
    eval(&closure.term, &env)
}

/// Apply an argument to a function
pub fn do_app(fun: &RcValue, arg: RcValue) -> Result<RcValue, NbeError> {
    match *fun.inner {
        Value::FunIntro(ref body) => do_closure(body, arg),
        Value::Neutral { ref ann, ref term } => match *ann.inner {
            Value::FunType(ref param_ty, ref body_ty) => {
                let arg_nf = Nf {
                    term: arg.clone(),
                    ann: param_ty.clone(),
                };

                Ok(RcValue::from(Value::Neutral {
                    term: RcNeutral::from(Neutral::FunApp(term.clone(), arg_nf)),
                    ann: do_closure(body_ty, arg)?,
                }))
            },
            _ => Err(NbeError::new("do_ap: not a function type")),
        },
        _ => Err(NbeError::new("do_ap: not a function")),
    }
}

/// Evaluate a syntactic term into a semantic value
pub fn eval(term: &RcTerm, env: &Env) -> Result<RcValue, NbeError> {
    match *term.inner {
        Term::Var(DbIndex(index)) => match env.get(index as usize) {
            Some(value) => Ok(value.clone()),
            None => Err(NbeError::new("eval: variable not found")),
        },
        Term::Let(ref def, ref body) => {
            let def = eval(def, env)?;
            let mut env = env.clone();
            env.push_front(def);
            eval(body, &env)
        },
        Term::Check(ref term, _) => eval(term, env),

        // Functions
        Term::FunType(ref ann_ty, ref body_ty) => Ok(RcValue::from(Value::FunType(
            eval(ann_ty, env)?,
            Closure {
                term: body_ty.clone(),
                env: env.clone(),
            },
        ))),
        Term::FunIntro(ref body) => Ok(RcValue::from(Value::FunIntro(Closure {
            term: body.clone(),
            env: env.clone(),
        }))),
        Term::FunApp(ref fun, ref arg) => do_app(&eval(fun, env)?, eval(arg, env)?),

        // Pairs
        Term::PairType(ref ann_ty, ref body_ty) => Ok(RcValue::from(Value::PairType(
            eval(ann_ty, env)?,
            Closure {
                term: body_ty.clone(),
                env: env.clone(),
            },
        ))),
        Term::PairIntro(ref fst, ref snd) => Ok(RcValue::from(Value::PairIntro(
            eval(fst, env)?,
            eval(snd, env)?,
        ))),
        Term::PairFst(ref pair) => do_pair_fst(&eval(pair, env)?),
        Term::PairSnd(ref pair) => do_pair_snd(&eval(pair, env)?),

        // Universes
        Term::Universe(level) => Ok(RcValue::from(Value::Universe(level))),
    }
}

/// Quote back a type
pub fn read_back_nf(size: u32, nf: Nf) -> Result<RcTerm, NbeError> {
    let Nf { term, ann } = nf;

    match (&*term.inner, &*ann.inner) {
        (&Value::Neutral { ref term, .. }, &Value::Neutral { .. }) => read_back_neutral(size, term),

        // Functions
        (_, &Value::FunType(ref param_ty, ref body_ty)) => {
            let arg = RcValue::from(Value::Neutral {
                term: RcNeutral::from(Neutral::Var(DbLevel(size))),
                ann: param_ty.clone(),
            });
            let nf = Nf {
                term: do_app(&term, arg.clone())?,
                ann: do_closure(body_ty, arg)?,
            };

            Ok(RcTerm::from(Term::FunIntro(read_back_nf(size + 1, nf)?)))
        },

        // Pairs
        (_, &Value::PairType(ref fst_ty, ref snd_ty)) => {
            let fst = do_pair_fst(&term)?;
            let fst_ty = fst_ty.clone();
            let snd = do_pair_snd(&term)?;
            let snd_ty = do_closure(snd_ty, fst.clone())?;

            let fst_nf = Nf {
                term: fst,
                ann: fst_ty,
            };
            let snd_nf = Nf {
                term: snd,
                ann: snd_ty,
            };

            Ok(RcTerm::from(Term::PairIntro(
                read_back_nf(size, fst_nf)?,
                read_back_nf(size, snd_nf)?,
            )))
        },

        // Types
        (&Value::FunType(ref param_ty, ref body_ty), &Value::Universe(_)) => {
            let var = RcValue::var(DbLevel(size), param_ty.clone());
            let param_ty_nf = Nf {
                term: param_ty.clone(),
                ann: ann.clone(),
            };
            let body_ty_nf = Nf {
                term: do_closure(body_ty, var)?,
                ann: ann.clone(),
            };

            Ok(RcTerm::from(Term::FunType(
                read_back_nf(size, param_ty_nf)?,
                read_back_nf(size + 1, body_ty_nf)?,
            )))
        },
        (&Value::PairType(ref fst_ty, ref snd_ty), &Value::Universe(_)) => {
            let var = RcValue::var(DbLevel(size), fst_ty.clone());
            let fst_ty_nf = Nf {
                term: fst_ty.clone(),
                ann: ann.clone(),
            };
            let snd_ty_nf = Nf {
                term: do_closure(snd_ty, var)?,
                ann: ann.clone(),
            };

            Ok(RcTerm::from(Term::PairType(
                read_back_nf(size, fst_ty_nf)?,
                read_back_nf(size + 1, snd_ty_nf)?,
            )))
        },
        (&Value::Universe(level), &Value::Universe(_)) => Ok(RcTerm::from(Term::Universe(level))),
        (&Value::Neutral { ref term, .. }, &Value::Universe(_)) => read_back_neutral(size, term),

        _ => Err(NbeError::new("read_back_nf: ill-typed")),
    }
}

/// Quote back a neutral term
fn read_back_neutral(size: u32, neutral: &RcNeutral) -> Result<RcTerm, NbeError> {
    match &*neutral.inner {
        Neutral::Var(DbLevel(level)) => Ok(RcTerm::from(Term::Var(DbIndex(size - level)))),
        Neutral::FunApp(ref fun, ref arg) => Ok(RcTerm::from(Term::FunApp(
            read_back_neutral(size, fun)?,
            read_back_nf(size, arg.clone())?,
        ))),
        Neutral::PairFst(ref pair) => {
            Ok(RcTerm::from(Term::PairFst(read_back_neutral(size, pair)?)))
        },
        Neutral::PairSnd(ref pair) => {
            Ok(RcTerm::from(Term::PairSnd(read_back_neutral(size, pair)?)))
        },
    }
}

/// Check whether a semantic type is a subtype of another
pub fn check_subtype(size: u32, ty1: &RcType, ty2: &RcType) -> Result<bool, NbeError> {
    match (&*ty1.inner, &*ty2.inner) {
        (
            &Value::Neutral {
                term: ref term1, ..
            },
            &Value::Neutral {
                term: ref term2, ..
            },
        ) => Ok(read_back_neutral(size, term1)? == read_back_neutral(size, term2)?),
        (
            &Value::FunType(ref param_ty1, ref body_ty1),
            &Value::FunType(ref param_ty2, ref body_ty2),
        ) => {
            let var = RcValue::var(DbLevel(size), param_ty2.clone());

            Ok(check_subtype(size, param_ty2, param_ty1)?
                && check_subtype(
                    size + 1,
                    &do_closure(body_ty1, var.clone())?,
                    &do_closure(body_ty2, var)?,
                )?)
        },
        (
            &Value::PairType(ref fst_ty1, ref snd_ty1),
            &Value::PairType(ref fst_ty2, ref snd_ty2),
        ) => {
            let var = RcValue::var(DbLevel(size), fst_ty1.clone());

            Ok(check_subtype(size, fst_ty1, fst_ty2)?
                && check_subtype(
                    size + 1,
                    &do_closure(snd_ty1, var.clone())?,
                    &do_closure(snd_ty2, var)?,
                )?)
        },
        (&Value::Universe(level1), &Value::Universe(level2)) => Ok(level1 <= level2),
        _ => Ok(false),
    }
}

/// Convert a core environment into the initial environment for normalization
fn initial_env(env: &core::Env) -> Result<Env, NbeError> {
    let mut new_env = Env::new();

    for ann in env {
        let index = DbLevel((env.len() - new_env.len()) as u32); // TODO: double-check this!
        let ann = RcValue::var(index, eval(ann, &new_env)?);
        new_env.push_front(ann);
    }

    Ok(new_env)
}

/// Do a full normalization
pub fn normalize(env: &core::Env, term: &RcTerm, ann: &RcTerm) -> Result<RcTerm, NbeError> {
    let env = initial_env(env)?;
    let term = eval(term, &env)?;
    let ann = eval(ann, &env)?;

    read_back_nf(env.len() as u32, Nf { term, ann })
}
