//! Normalization by evaluation

use syntax::core::{self, RcTerm, Term};
use syntax::domain::{Closure1, Closure2, Env, Neutral, Nf, RcNeutral, RcType, RcValue, Value};
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

fn do_nat_rec(
    motive: Closure1,
    zero: RcValue,
    succ: Closure2,
    nat: RcValue,
) -> Result<RcValue, NbeError> {
    match *nat.inner {
        Value::NatZero => Ok(zero),
        Value::NatSucc(ref nat) => {
            let rec = do_nat_rec(motive, zero, succ.clone(), nat.clone())?;
            do_closure2(&succ, nat.clone(), rec)
        },
        Value::Neutral { term: ref ne, .. } => {
            let final_motive = do_closure1(&motive, nat.clone())?;
            Ok(RcValue::from(Value::Neutral {
                ann: final_motive,
                term: RcNeutral::from(Neutral::NatRec(motive, zero, succ, ne.clone())),
            }))
        },
        _ => Err(NbeError::new("do_nat_rec: not a nat")),
    }
}

fn do_pair_fst(pair: &RcValue) -> Result<RcValue, NbeError> {
    match *pair.inner {
        Value::PairIntro(ref fst, _) => Ok(fst.clone()),
        Value::Neutral {
            ref ann,
            term: ref ne,
        } => match *ann.inner {
            Value::PairType(ref ann, _) => {
                let ann = ann.clone();
                let term = RcNeutral::from(Neutral::PairFst(ne.clone()));

                Ok(RcValue::from(Value::Neutral { ann, term }))
            },
            _ => Err(NbeError::new("do_pair_fst: not a pair type")),
        },
        _ => Err(NbeError::new("do_pair_fst: not a pair")),
    }
}

fn do_pair_snd(pair: &RcValue) -> Result<RcValue, NbeError> {
    match *pair.inner {
        Value::PairIntro(_, ref snd) => Ok(snd.clone()),
        Value::Neutral {
            ref ann,
            term: ref ne,
        } => match *ann.inner {
            Value::PairType(_, ref closure) => {
                let fst = do_pair_fst(pair)?;
                let ann = do_closure1(closure, fst)?;
                let term = RcNeutral::from(Neutral::PairSnd(ne.clone()));

                Ok(RcValue::from(Value::Neutral { ann, term }))
            },
            _ => Err(NbeError::new("do_pair_snd: not a pair type")),
        },
        _ => Err(NbeError::new("do_pair_snd: not a pair")),
    }
}

pub fn do_closure1(closure: &Closure1, arg: RcValue) -> Result<RcValue, NbeError> {
    let mut env = closure.env.clone();
    env.push_front(arg);
    eval(&closure.term, &env)
}

pub fn do_closure2(closure: &Closure2, arg1: RcValue, arg2: RcValue) -> Result<RcValue, NbeError> {
    let mut env = closure.env.clone();
    env.push_front(arg1);
    env.push_front(arg2);
    eval(&closure.term, &env)
}

pub fn do_app(fun: RcValue, arg: RcValue) -> Result<RcValue, NbeError> {
    match *fun.inner {
        Value::FunIntro(ref body) => do_closure1(body, arg),
        Value::Neutral { ref ann, ref term } => match *ann.inner {
            Value::FunType(ref param_ty, ref body_ty) => {
                let body_ty = do_closure1(body_ty, arg.clone())?;
                Ok(RcValue::from(Value::Neutral {
                    ann: body_ty.clone(),
                    term: RcNeutral::from(Neutral::FunApp(
                        term.clone(),
                        Nf {
                            ann: param_ty.clone(),
                            term: arg,
                        },
                    )),
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

        // Natural numbers
        Term::NatType => Ok(RcValue::from(Value::NatType)),
        Term::NatZero => Ok(RcValue::from(Value::NatZero)),
        Term::NatSucc(ref nat) => Ok(RcValue::from(Value::NatSucc(eval(nat, env)?))),
        Term::NatRec(ref motive, ref zero, ref succ, ref nat) => do_nat_rec(
            Closure1 {
                term: motive.clone(),
                env: env.clone(),
            },
            eval(zero, env)?,
            Closure2 {
                term: succ.clone(),
                env: env.clone(),
            },
            eval(nat, env)?,
        ),

        // Functions
        Term::FunType(ref ann, ref body) => Ok(RcValue::from(Value::FunType(
            eval(ann, env)?,
            Closure1 {
                term: body.clone(),
                env: env.clone(),
            },
        ))),
        Term::FunIntro(ref body) => Ok(RcValue::from(Value::FunIntro(Closure1 {
            term: body.clone(),
            env: env.clone(),
        }))),
        Term::FunApp(ref fun, ref arg) => do_app(eval(fun, env)?, eval(arg, env)?),

        // Pairs
        Term::PairType(ref ann, ref body) => Ok(RcValue::from(Value::PairType(
            eval(ann, env)?,
            Closure1 {
                term: body.clone(),
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
    match (&*nf.ann.inner, &*nf.term.inner) {
        (&Value::Neutral { .. }, &Value::Neutral { term: ref ne, .. }) => {
            read_back_neutral(size, ne)
        },

        // Natural numbers
        (&Value::NatType, &Value::NatZero) => Ok(RcTerm::from(Term::NatZero)),
        (&Value::NatType, &Value::NatSucc(ref nat)) => {
            let ann = RcValue::from(Value::NatType);
            let term = nat.clone();
            let nf = Nf { ann, term };

            Ok(RcTerm::from(Term::NatSucc(read_back_nf(size, nf)?)))
        },
        (&Value::NatType, &Value::Neutral { term: ref ne, .. }) => read_back_neutral(size, ne),

        // Functions
        (&Value::FunType(ref param_ty, ref body_ty), _) => {
            let arg = RcValue::from(Value::Neutral {
                ann: param_ty.clone(),
                term: RcNeutral::from(Neutral::Var(DbLevel(size))),
            });
            let nf = Nf {
                ann: do_closure1(body_ty, arg.clone())?,
                term: do_app(nf.term.clone(), arg)?,
            };

            Ok(RcTerm::from(Term::FunIntro(read_back_nf(size + 1, nf)?)))
        },

        // Pairs
        (&Value::PairType(ref fst_ty, ref snd_ty), _) => {
            let fst = do_pair_fst(&nf.term)?;
            let snd_ty = do_closure1(snd_ty, fst.clone())?;
            let snd = do_pair_snd(&nf.term)?;

            let fst_nf = Nf {
                ann: fst_ty.clone(),
                term: fst,
            };
            let snd_nf = Nf {
                ann: snd_ty,
                term: snd,
            };

            Ok(RcTerm::from(Term::PairIntro(
                read_back_nf(size, fst_nf)?,
                read_back_nf(size, snd_nf)?,
            )))
        },

        // Types
        (&Value::Universe(_), &Value::NatType) => Ok(RcTerm::from(Term::NatType)),
        (&Value::Universe(_), &Value::FunType(ref param_ty, ref body_ty)) => {
            let var = RcValue::var(DbLevel(size), param_ty.clone());
            let param_ty_nf = Nf {
                ann: nf.ann.clone(),
                term: param_ty.clone(),
            };
            let body_ty_nf = Nf {
                ann: nf.ann.clone(),
                term: do_closure1(body_ty, var)?,
            };

            Ok(RcTerm::from(Term::FunType(
                read_back_nf(size, param_ty_nf)?,
                read_back_nf(size + 1, body_ty_nf)?,
            )))
        },
        (&Value::Universe(_), &Value::PairType(ref fst, ref snd)) => {
            let var = RcValue::var(DbLevel(size), fst.clone());
            let fst_nf = Nf {
                ann: nf.ann.clone(),
                term: fst.clone(),
            };
            let snd_nf = Nf {
                ann: nf.ann.clone(),
                term: do_closure1(snd, var)?,
            };

            Ok(RcTerm::from(Term::PairType(
                read_back_nf(size, fst_nf)?,
                read_back_nf(size + 1, snd_nf)?,
            )))
        },
        (&Value::Universe(_), &Value::Universe(level)) => Ok(RcTerm::from(Term::Universe(level))),
        (&Value::Universe(_), &Value::Neutral { term: ref ne, .. }) => read_back_neutral(size, ne),

        _ => Err(NbeError::new("read_back_nf: ill-typed")),
    }
}

fn read_back_ty(size: u32, ty: &RcType) -> Result<RcTerm, NbeError> {
    match *ty.inner {
        Value::Neutral { ref term, .. } => read_back_neutral(size, term),
        Value::NatType => Ok(RcTerm::from(Term::NatType)),
        Value::FunType(ref param_ty, ref dest) => {
            let var = RcValue::var(DbLevel(size), param_ty.clone());
            Ok(RcTerm::from(Term::FunType(
                read_back_ty(size, param_ty)?,
                read_back_ty(size + 1, &do_closure1(dest, var)?)?,
            )))
        },
        Value::PairType(ref fst, ref snd) => {
            let var = RcValue::var(DbLevel(size), fst.clone());
            Ok(RcTerm::from(Term::PairType(
                read_back_ty(size, fst)?,
                read_back_ty(size + 1, &do_closure1(snd, var)?)?,
            )))
        },
        Value::Universe(level) => Ok(RcTerm::from(Term::Universe(level))),
        _ => Err(NbeError::new("read_back_ty: not a type")),
    }
}

fn read_back_neutral(size: u32, ne: &RcNeutral) -> Result<RcTerm, NbeError> {
    match &*ne.inner {
        Neutral::Var(DbLevel(level)) => Ok(RcTerm::from(Term::Var(DbIndex(size - (level + 1))))),
        Neutral::FunApp(ref fun, ref arg) => Ok(RcTerm::from(Term::FunApp(
            read_back_neutral(size, fun)?,
            read_back_nf(size, arg.clone())?,
        ))),
        Neutral::NatRec(ref motive, ref zero, ref succ, ref nat) => {
            //   | D.NRec (tp, zero, suc, n) ->
            //     let tp_var = D.mk_var D.Nat size in
            //     let applied_tp = do_clos tp tp_var in
            //     let zero_tp = do_clos tp D.Zero in
            //     let applied_suc_tp = do_clos tp (D.Suc tp_var) in
            //     let tp' = read_back_tp (size + 1) applied_tp in
            //     let suc_var = D.mk_var applied_tp (size + 1) in
            //     let applied_suc = do_clos2 suc tp_var suc_var in
            //     let suc' =
            //       read_back_nf (size + 2) (D.Normal {tp = applied_suc_tp; term = applied_suc}) in
            //     Syn.NRec
            //       (tp',
            //        read_back_nf size (D.Normal {tp = zero_tp; term = zero}),
            //        suc',
            //        read_back_ne size n)

            unimplemented!("read_back_neutral: Neutral::NatRec")
        },
        Neutral::PairFst(ref ne) => Ok(RcTerm::from(Term::PairFst(read_back_neutral(size, ne)?))),
        Neutral::PairSnd(ref ne) => Ok(RcTerm::from(Term::PairSnd(read_back_neutral(size, ne)?))),
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
        (&Value::NatType, &Value::NatType) => Ok(true),
        (
            &Value::FunType(ref param_ty1, ref body_ty1),
            &Value::FunType(ref param_ty2, ref body_ty2),
        ) => {
            let var = RcValue::var(DbLevel(size), param_ty2.clone());

            Ok(check_subtype(size, param_ty2, param_ty1)?
                && check_subtype(
                    size + 1,
                    &do_closure1(body_ty1, var.clone())?,
                    &do_closure1(body_ty2, var)?,
                )?)
        },
        (&Value::PairType(ref fst1, ref snd1), &Value::PairType(ref fst2, ref snd2)) => {
            let var = RcValue::var(DbLevel(size), fst1.clone());

            Ok(check_subtype(size, fst1, fst2)?
                && check_subtype(
                    size + 1,
                    &do_closure1(snd1, var.clone())?,
                    &do_closure1(snd2, var)?,
                )?)
        },
        (&Value::Universe(level1), &Value::Universe(level2)) => Ok(level1 <= level2),
        _ => Ok(false),
    }
}

fn initial_env(env: &core::Env) -> Result<Env, NbeError> {
    let mut new_env = Env::new();

    for ann in env {
        let ann = RcValue::from(Value::Neutral {
            ann: eval(ann, &new_env)?,
            term: RcNeutral::from(Neutral::Var(DbLevel(
                (env.len() - new_env.len()) as u32 - 1, // TODO: double-check this!
            ))),
        });
        new_env.push_front(ann);
    }

    Ok(new_env)
}

/// Do a full normalization
pub fn normalize(env: &core::Env, term: &RcTerm, ann: &RcTerm) -> Result<RcTerm, NbeError> {
    let env = initial_env(env)?;
    let ann = eval(ann, &env)?;
    let term = eval(term, &env)?;

    read_back_nf(env.len() as u32, Nf { ann, term })
}
