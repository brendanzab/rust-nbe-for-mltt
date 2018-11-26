//! Normalization by evaluation
//!
//! Here we implement a full normalization algorithm by first implementing
//! evaluation to `Value`s in weak-head-normal-form, and then reading it back
//! `Normal` terms.

use syntax::core::{self, RcTerm, Term};
use syntax::domain::{self, Closure, Env, Nf, RcType, RcValue, Value};
use syntax::normal::{self, Normal, RcNormal};
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
        Value::Neutral(ref pair, ref pair_ty) => match *pair_ty.inner {
            Value::PairType(_, ref ann_ty, _) => {
                let fst = domain::RcNeutral::from(domain::Neutral::PairFst(pair.clone()));
                let fst_ty = ann_ty.clone();

                Ok(RcValue::from(Value::Neutral(fst, fst_ty)))
            },
            _ => Err(NbeError::new("do_pair_fst: not a pair type")),
        },
        _ => Err(NbeError::new("do_pair_fst: not a pair")),
    }
}

/// Return the second element of a pair
fn do_pair_snd(pair: &RcValue) -> Result<RcValue, NbeError> {
    match *pair.inner {
        Value::PairIntro(_, ref snd) => Ok(snd.clone()),
        Value::Neutral(ref pair_ne, ref pair_ty) => match *pair_ty.inner {
            Value::PairType(_, _, ref snd_ty) => {
                let fst = do_pair_fst(pair)?;
                let snd = domain::RcNeutral::from(domain::Neutral::PairSnd(pair_ne.clone()));
                let snd_ty = do_closure(snd_ty, fst)?;

                Ok(RcValue::from(Value::Neutral(snd, snd_ty)))
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
        Value::FunIntro(_, ref body) => do_closure(body, arg),
        Value::Neutral(ref fun, ref fun_ty) => match *fun_ty.inner {
            Value::FunType(_, ref param_ty, ref body_ty) => {
                let arg_nf = Nf::new(arg.clone(), param_ty.clone());
                let body = domain::RcNeutral::from(domain::Neutral::FunApp(fun.clone(), arg_nf));
                let body_ty = do_closure(body_ty, arg)?;

                Ok(RcValue::from(Value::Neutral(body, body_ty)))
            },
            _ => Err(NbeError::new("do_ap: not a function type")),
        },
        _ => Err(NbeError::new("do_ap: not a function")),
    }
}

/// Evaluate a syntactic term into a semantic value
pub fn eval(term: &RcTerm, env: &Env) -> Result<RcValue, NbeError> {
    match *term.inner {
        Term::Var(_, DbIndex(index)) => match env.get(index as usize) {
            Some(value) => Ok(value.clone()),
            None => Err(NbeError::new("eval: variable not found")),
        },
        Term::Let(_, ref def, ref body) => {
            let def = eval(def, env)?;
            let mut env = env.clone();
            env.push_front(def);
            eval(body, &env)
        },
        Term::Check(ref term, _) => eval(term, env),

        // Functions
        Term::FunType(ref ident, ref param_ty, ref body_ty) => Ok(RcValue::from(Value::FunType(
            ident.clone(),
            eval(param_ty, env)?,
            Closure {
                term: body_ty.clone(),
                env: env.clone(),
            },
        ))),
        Term::FunIntro(ref ident, ref body) => Ok(RcValue::from(Value::FunIntro(
            ident.clone(),
            Closure {
                term: body.clone(),
                env: env.clone(),
            },
        ))),
        Term::FunApp(ref fun, ref arg) => do_app(&eval(fun, env)?, eval(arg, env)?),

        // Pairs
        Term::PairType(ref ident, ref fst_ty, ref snd_ty) => Ok(RcValue::from(Value::PairType(
            ident.clone(),
            eval(fst_ty, env)?,
            Closure {
                term: snd_ty.clone(),
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

/// Quote back a term into normal form
pub fn read_back_nf(size: u32, nf: Nf) -> Result<RcNormal, NbeError> {
    let Nf { term, ann } = nf;

    // We don't look inside the `term` when reading back functions and pairs.
    // This is because we are [converting to eta-long form][eta-conversion].
    // This is the reason that we need to take care to pass along type
    // annotations with our normal forms.
    //
    // [eta-conversion]: https://en.wikipedia.org/wiki/Lambda_calculus#%CE%B7-conversion

    match (&*term.inner, &*ann.inner) {
        (&Value::Neutral(ref term, _), &Value::Neutral(_, _)) => Ok(RcNormal::from(
            Normal::Neutral(read_back_neutral(size, term)?),
        )),

        // Functions
        (_, &Value::FunType(ref ident, ref param_ty, ref body_ty)) => {
            let param = RcValue::var(ident.clone(), DbLevel(size), param_ty.clone());
            let body = do_app(&term, param.clone())?;
            let body_ty = do_closure(body_ty, param)?;

            Ok(RcNormal::from(Normal::FunIntro(
                ident.clone(),
                read_back_nf(size + 1, Nf::new(body, body_ty))?,
            )))
        },

        // Pairs
        (_, &Value::PairType(_, ref fst_ty, ref snd_ty)) => {
            let fst = do_pair_fst(&term)?;
            let fst_ty = fst_ty.clone();
            let snd = do_pair_snd(&term)?;
            let snd_ty = do_closure(snd_ty, fst.clone())?;

            Ok(RcNormal::from(Normal::PairIntro(
                read_back_nf(size, Nf::new(fst, fst_ty))?,
                read_back_nf(size, Nf::new(snd, snd_ty))?,
            )))
        },

        // Types
        (&Value::FunType(ref ident, ref param_ty, ref body_ty), &Value::Universe(_)) => {
            let param = RcValue::var(ident.clone(), DbLevel(size), param_ty.clone());
            let param_ty = param_ty.clone();
            let body_ty = do_closure(body_ty, param)?;

            Ok(RcNormal::from(Normal::FunType(
                ident.clone(),
                read_back_nf(size, Nf::new(param_ty, ann.clone()))?,
                read_back_nf(size + 1, Nf::new(body_ty, ann.clone()))?,
            )))
        },
        (&Value::PairType(ref ident, ref fst_ty, ref snd_ty), &Value::Universe(_)) => {
            let fst = RcValue::var(ident.clone(), DbLevel(size), fst_ty.clone());
            let fst_ty = fst_ty.clone();
            let snd_ty = do_closure(snd_ty, fst)?;

            Ok(RcNormal::from(Normal::PairType(
                ident.clone(),
                read_back_nf(size, Nf::new(fst_ty, ann.clone()))?,
                read_back_nf(size + 1, Nf::new(snd_ty, ann.clone()))?,
            )))
        },
        (&Value::Universe(level), &Value::Universe(_)) => {
            Ok(RcNormal::from(Normal::Universe(level)))
        },
        (&Value::Neutral(ref term, _), &Value::Universe(_)) => Ok(RcNormal::from(Normal::Neutral(
            read_back_neutral(size, term)?,
        ))),

        _ => Err(NbeError::new("read_back_nf: ill-typed")),
    }
}

/// Quote back a neutral term into normal form
pub fn read_back_neutral(
    size: u32,
    neutral: &domain::RcNeutral,
) -> Result<normal::RcNeutral, NbeError> {
    match &*neutral.inner {
        domain::Neutral::Var(ref ident, DbLevel(level)) => Ok(normal::RcNeutral::from(
            normal::Neutral::Var(ident.clone(), DbIndex(size - level)),
        )),
        domain::Neutral::FunApp(ref fun, ref arg) => {
            Ok(normal::RcNeutral::from(normal::Neutral::FunApp(
                read_back_neutral(size, fun)?,
                read_back_nf(size, arg.clone())?,
            )))
        },
        domain::Neutral::PairFst(ref pair) => {
            let pair = read_back_neutral(size, pair)?;
            Ok(normal::RcNeutral::from(normal::Neutral::PairFst(pair)))
        },
        domain::Neutral::PairSnd(ref pair) => {
            let pair = read_back_neutral(size, pair)?;
            Ok(normal::RcNeutral::from(normal::Neutral::PairSnd(pair)))
        },
    }
}

/// Check whether a semantic type is a subtype of another
pub fn check_subtype(size: u32, ty1: &RcType, ty2: &RcType) -> Result<bool, NbeError> {
    match (&*ty1.inner, &*ty2.inner) {
        (&Value::Neutral(ref term1, _), &Value::Neutral(ref term2, _)) => {
            let term1 = read_back_neutral(size, term1)?;
            let term2 = read_back_neutral(size, term2)?;

            Ok(term1 == term2)
        },
        (
            &Value::FunType(_, ref param_ty1, ref body_ty1),
            &Value::FunType(_, ref param_ty2, ref body_ty2),
        ) => {
            let param = RcValue::var(None, DbLevel(size), param_ty2.clone());

            Ok(check_subtype(size, param_ty2, param_ty1)? && {
                let body_ty1 = do_closure(body_ty1, param.clone())?;
                let body_ty2 = do_closure(body_ty2, param)?;
                check_subtype(size + 1, &body_ty1, &body_ty2)?
            })
        },
        (
            &Value::PairType(_, ref fst_ty1, ref snd_ty1),
            &Value::PairType(_, ref fst_ty2, ref snd_ty2),
        ) => {
            let fst = RcValue::var(None, DbLevel(size), fst_ty1.clone());

            Ok(check_subtype(size, fst_ty1, fst_ty2)? && {
                let snd_ty1 = do_closure(snd_ty1, fst.clone())?;
                let snd_ty2 = do_closure(snd_ty2, fst)?;
                check_subtype(size + 1, &snd_ty1, &snd_ty2)?
            })
        },
        (&Value::Universe(level1), &Value::Universe(level2)) => Ok(level1 <= level2),
        _ => Ok(false),
    }
}

/// Convert a core environment into the initial environment for normalization
fn initial_env(env: &core::Env) -> Result<Env, NbeError> {
    let mut new_env = Env::new();

    for (ref ident, ref ann) in env {
        let index = DbLevel((env.len() - new_env.len()) as u32);
        let ann = RcValue::var(ident.clone(), index, eval(ann, &new_env)?);
        new_env.push_front(ann);
    }

    Ok(new_env)
}

/// Do a full normalization by first evaluating, and then reading back the result
pub fn normalize(env: &core::Env, term: &RcTerm, ann: &RcTerm) -> Result<RcNormal, NbeError> {
    let env = initial_env(env)?;
    let term = eval(term, &env)?;
    let ann = eval(ann, &env)?;

    read_back_nf(env.len() as u32, Nf::new(term, ann))
}
