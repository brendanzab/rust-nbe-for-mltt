use im;

use crate::nbe::{self, NbeError};
use crate::syntax::core::{RcTerm, Term};
use crate::syntax::domain::{self, RcType, RcValue, Value};
use crate::syntax::{DbIndex, DbLevel, UniverseLevel};

/// Local elaboration context
#[derive(Debug, Clone, PartialEq)]
pub struct Context {
    values: domain::Env,
    tys: domain::Env,
}

impl Context {
    pub fn new() -> Context {
        Context {
            values: domain::Env::new(),
            tys: domain::Env::new(),
        }
    }

    pub fn insert(&mut self, value: RcValue, ty: RcType) {
        self.values.push_front(value);
        self.tys.push_front(ty);
    }

    pub fn lookup(&self, index: DbIndex) -> Option<(&RcValue, &RcType)> {
        let term = self.values.get(index.0 as usize)?;
        let ty = self.tys.get(index.0 as usize)?;
        Some((term, ty))
    }
}

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

fn check_subtype(size: u32, ty1: &RcType, ty2: &RcType) -> Result<(), TypeError> {
    if nbe::check_subtype(size, ty1, ty2)? {
        Ok(())
    } else {
        Err(TypeError::ExpectedSubtype(ty1.clone(), ty2.clone()))
    }
}

/// Synthesize the type of the term
pub fn synth(context: &Context, size: u32, term: &RcTerm) -> Result<RcType, TypeError> {
    match *term.inner {
        Term::Var(index) => match context.lookup(index) {
            None => Err(TypeError::UnboundVariable),
            Some((_, ann)) => Ok(ann.clone()),
        },
        Term::Let(_, ref def, ref def_ty, ref body) => {
            let def_ty = synth(context, size, def)?;
            let def_value = nbe::eval(def, &context.values)?;
            {
                let mut context = context.clone();
                context.insert(def_value, def_ty);
                synth(&context, size + 1, body)
            }
        },

        Term::FunType(ref ident, ref param_ty, ref body_ty) => {
            check_ty(context, size, param_ty)?;
            let param_ty_value = nbe::eval(param_ty, &context.values)?;
            {
                let mut context = context.clone();
                context.insert(RcValue::var(DbLevel(size)), param_ty_value);
                check_ty(&context, size + 1, body_ty)
            }
        },
        Term::FunIntro(ref ident, ref param_ty, ref body) => unimplemented!(),
        Term::FunApp(ref fun, ref arg) => {
            let fun_ty = synth(context, size, fun)?;
            match *fun_ty.inner {
                Value::FunType(_, ref param_ty, ref body_ty) => {
                    let arg_ty = synth(context, size, arg)?;
                    check_subtype(size, param_ty, &arg_ty)?;
                    let arg_value = nbe::eval(arg, &context.values)?;
                    Ok(nbe::do_closure_app(body_ty, arg_value)?)
                },
                _ => Err(TypeError::ExpectedFunType {
                    found: fun_ty.clone(),
                }),
            }
        },

        Term::PairType(ref ident, ref fst_ty, ref snd_ty) => unimplemented!(),
        Term::PairIntro(ref fst, ref snd, ref ident, ref fst_ty, ref snd_ty) => unimplemented!(),
        Term::PairFst(ref pair) => {
            let pair_ty = synth(context, size, pair)?;
            match *pair_ty.inner {
                Value::PairType(_, ref fst_ty, _) => Ok(fst_ty.clone()),
                _ => Err(TypeError::ExpectedPairType {
                    found: pair_ty.clone(),
                }),
            }
        },
        Term::PairSnd(ref pair) => {
            let pair_ty = synth(context, size, pair)?;
            match *pair_ty.inner {
                Value::PairType(_, _, ref snd_ty) => {
                    let fst =
                        nbe::eval(&RcTerm::from(Term::PairFst(pair.clone())), &context.values)?;
                    Ok(nbe::do_closure_app(snd_ty, fst)?)
                },
                _ => Err(TypeError::ExpectedPairType {
                    found: pair_ty.clone(),
                }),
            }
        },

        Term::Universe(level) => Ok(RcValue::from(Value::Universe(level))),
    }
}

/// Check that the given term is a type
pub fn check_ty(context: &Context, size: u32, term: &RcTerm) -> Result<(), TypeError> {
    match *term.inner {
        Term::Let(_, ref def, ref def_ty, ref body) => {
            let def_ty = synth(context, size, def)?;
            let def_value = nbe::eval(def, &context.values)?;
            {
                let mut context = context.clone();
                context.insert(def_value, def_ty);
                check_ty(&context, size + 1, body)
            }
        },

        Term::FunType(_, ref ann, ref body) | Term::PairType(_, ref ann, ref body) => {
            check_ty(context, size, ann)?;
            let ann_value = nbe::eval(ann, &context.values)?;
            {
                let mut context = context.clone();
                context.insert(RcValue::var(DbLevel(size)), ann_value);
                check_ty(&context, size + 1, body)
            }
        },

        Term::Universe(_) => Ok(()),

        _ => {
            let synth_ty = synth(context, size, term)?;
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
