//! Normalization by evaluation

use syntax::core::{self, RcTerm, Term};
use syntax::domain::{Closure, Closure2, Env, Neutral, Nf, RcNeutral, RcValue, Value};
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
    ann: Closure,
    zero: RcValue,
    succ: Closure2,
    n: RcValue,
) -> Result<RcValue, NbeError> {
    match *n.inner {
        Value::NatZero => Ok(zero),
        Value::NatSucc(ref n) => {
            let rec = do_nat_rec(ann, zero, succ.clone(), n.clone())?;
            do_closure2(&succ, n.clone(), rec)
        },
        Value::Neutral { term: ref ne, .. } => {
            let final_ann = do_closure(&ann, n.clone())?;
            Ok(RcValue::from(Value::Neutral {
                ann: final_ann,
                term: RcNeutral::from(Neutral::NatRec(ann, zero, succ, ne.clone())),
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
                let ann = do_closure(closure, fst)?;
                let term = RcNeutral::from(Neutral::PairSnd(ne.clone()));

                Ok(RcValue::from(Value::Neutral { ann, term }))
            },
            _ => Err(NbeError::new("do_pair_snd: not a pair type")),
        },
        _ => Err(NbeError::new("do_pair_snd: not a pair")),
    }
}

pub fn do_closure(closure: &Closure, arg: RcValue) -> Result<RcValue, NbeError> {
    match *closure {
        Closure::Closure { ref term, ref env } => {
            let mut env = env.clone();
            env.push_front(arg);
            eval(term, &env)
        },
        Closure::Const(ref term) => Ok(term.clone()),
    }
}

pub fn do_closure2(closure: &Closure2, arg1: RcValue, arg2: RcValue) -> Result<RcValue, NbeError> {
    let Closure2 { ref term, ref env } = *closure;
    let mut env = env.clone();
    env.push_front(arg1);
    env.push_front(arg2);
    eval(term, &env)
}

pub fn do_app(fun: RcValue, arg: RcValue) -> Result<RcValue, NbeError> {
    match *fun.inner {
        Value::FunIntro(ref body) => do_closure(body, arg),
        Value::Neutral { ref ann, ref term } => match *ann.inner {
            Value::FunType(ref src, ref dst) => {
                let dst = do_closure(dst, arg.clone())?;
                Ok(RcValue::from(Value::Neutral {
                    ann: dst.clone(),
                    term: RcNeutral::from(Neutral::FunApp(
                        term.clone(),
                        Nf {
                            ann: src.clone(),
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
        Term::NatSucc(ref n) => Ok(RcValue::from(Value::NatSucc(eval(n, env)?))),
        Term::NatRec(ref ann, ref zero, ref succ, ref n) => do_nat_rec(
            Closure::Closure {
                term: ann.clone(),
                env: env.clone(),
            },
            eval(zero, env)?,
            Closure2 {
                term: succ.clone(),
                env: env.clone(),
            },
            eval(n, env)?,
        ),

        // Functions
        Term::FunType(ref ann, ref body) => Ok(RcValue::from(Value::FunType(
            eval(ann, env)?,
            Closure::Closure {
                term: body.clone(),
                env: env.clone(),
            },
        ))),
        Term::FunIntro(ref body) => Ok(RcValue::from(Value::FunIntro(Closure::Closure {
            term: body.clone(),
            env: env.clone(),
        }))),
        Term::FunApp(ref fun, ref arg) => do_app(eval(fun, env)?, eval(arg, env)?),

        // Pairs
        Term::PairType(ref ann, ref body) => Ok(RcValue::from(Value::PairType(
            eval(ann, env)?,
            Closure::Closure {
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
        (&Value::NatType, &Value::NatSucc(ref n)) => {
            let ann = RcValue::from(Value::NatType);
            let term = n.clone();
            let nf = Nf { ann, term };

            Ok(RcTerm::from(Term::NatSucc(read_back_nf(size, nf)?)))
        },
        (&Value::NatType, &Value::Neutral { term: ref ne, .. }) => read_back_neutral(size, ne),

        // Functions
        (&Value::FunType(ref src, ref dst), _) => {
            let arg = RcValue::from(Value::Neutral {
                ann: src.clone(),
                term: RcNeutral::from(Neutral::Var(DbLevel(size))),
            });
            let nf = Nf {
                ann: do_closure(dst, arg.clone())?,
                term: do_app(nf.term.clone(), arg)?,
            };

            Ok(RcTerm::from(Term::FunIntro(read_back_nf(size + 1, nf)?)))
        },

        // Pairs
        (&Value::PairType(ref fst_ty, ref snd_ty), _) => {
            let fst = do_pair_fst(&nf.term)?;
            let snd_ty = do_closure(snd_ty, fst.clone())?;
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
        (&Value::Universe(_), &Value::FunType(ref src, ref dst)) => {
            let var = RcValue::var(DbLevel(size), src.clone());
            let src_nf = Nf {
                ann: nf.ann.clone(),
                term: src.clone(),
            };
            let dst_nf = Nf {
                ann: nf.ann.clone(),
                term: do_closure(dst, var)?,
            };

            Ok(RcTerm::from(Term::FunType(
                read_back_nf(size, src_nf)?,
                read_back_nf(size + 1, dst_nf)?,
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
                term: do_closure(snd, var)?,
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

fn read_back_ty(size: u32, ty: &RcValue) -> Result<RcTerm, NbeError> {
    match *ty.inner {
        Value::Neutral { ref term, .. } => read_back_neutral(size, term),
        Value::NatType => Ok(RcTerm::from(Term::NatType)),
        Value::FunType(ref src, ref dest) => {
            let var = RcValue::var(DbLevel(size), src.clone());
            Ok(RcTerm::from(Term::FunType(
                read_back_ty(size, src)?,
                read_back_ty(size + 1, &do_closure(dest, var)?)?,
            )))
        },
        Value::PairType(ref fst, ref snd) => {
            let var = RcValue::var(DbLevel(size), fst.clone());
            Ok(RcTerm::from(Term::PairType(
                read_back_ty(size, fst)?,
                read_back_ty(size + 1, &do_closure(snd, var)?)?,
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
        Neutral::NatRec(ref ann, ref zero, ref succ, ref n) => {
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
pub fn check_subtype(size: u32, ty1: &RcValue, ty2: &RcValue) -> Result<bool, NbeError> {
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
        (&Value::FunType(ref src1, ref dst1), &Value::FunType(ref src2, ref dst2)) => {
            let var = RcValue::var(DbLevel(size), src2.clone());

            Ok(check_subtype(size, src2, src1)?
                && check_subtype(
                    size + 1,
                    &do_closure(dst1, var.clone())?,
                    &do_closure(dst2, var)?,
                )?)
        },
        (&Value::PairType(ref fst1, ref snd1), &Value::PairType(ref fst2, ref snd2)) => {
            let var = RcValue::var(DbLevel(size), fst1.clone());

            Ok(check_subtype(size, fst1, fst2)?
                && check_subtype(
                    size + 1,
                    &do_closure(snd1, var.clone())?,
                    &do_closure(snd2, var)?,
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
