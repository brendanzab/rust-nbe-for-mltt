//! Bidirectional type checking of the core syntax
//!
//! This is used to verify that the core syntax is correctly formed, for
//! debugging purposes.

use im;

use crate::nbe::{self, NbeError};
use crate::syntax::core::{RcTerm, Term};
use crate::syntax::domain::{self, RcType, RcValue, Value};
use crate::syntax::{DbIndex, DbLevel, UniverseLevel};

/// Local type checking context
#[derive(Debug, Clone, PartialEq)]
pub struct Context {
    /// Number of local entries
    size: u32,
    /// Values to be used during evaluation
    values: domain::Env,
    /// Types of the binders we have passed over
    tys: im::Vector<RcType>,
}

impl Context {
    pub fn new() -> Context {
        Context {
            size: 0,
            values: domain::Env::new(),
            tys: im::Vector::new(),
        }
    }

    pub fn insert(&mut self, value: RcValue, ty: RcType) {
        self.size += 1;
        self.values.push_front(value);
        self.tys.push_front(ty);
    }

    pub fn lookup_ty(&self, index: DbIndex) -> Option<&RcType> {
        self.tys.get(index.0 as usize)
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

fn check_subtype(context: &Context, ty1: &RcType, ty2: &RcType) -> Result<(), TypeError> {
    if nbe::check_subtype(context.size, ty1, ty2)? {
        Ok(())
    } else {
        Err(TypeError::ExpectedSubtype(ty1.clone(), ty2.clone()))
    }
}

/// Check that a term conforms to a given type
pub fn check_term(context: &Context, term: &RcTerm, expected_ty: &RcType) -> Result<(), TypeError> {
    match *term.inner {
        Term::Let(ref def, ref body) => {
            let mut body_context = context.clone();
            body_context.insert(nbe::eval(def, &context.values)?, synth_term(context, def)?);

            check_term(&body_context, body, expected_ty)
        },

        Term::FunType(ref ann_ty, ref body_ty) | Term::PairType(ref ann_ty, ref body_ty) => {
            check_term(context, ann_ty, expected_ty)?;
            let ann_ty_value = nbe::eval(ann_ty, &context.values)?;

            let mut body_ty_context = context.clone();
            body_ty_context.insert(RcValue::var(DbLevel(context.size)), ann_ty_value);

            check_term(&body_ty_context, body_ty, expected_ty)
        },
        Term::FunIntro(ref body) => match *expected_ty.inner {
            Value::FunType(ref param_ty, ref body_ty) => {
                let param = RcValue::var(DbLevel(context.size));
                let body_ty = nbe::do_closure_app(body_ty, param.clone())?;

                let mut body_context = context.clone();
                body_context.insert(param, param_ty.clone());

                check_term(&body_context, body, &body_ty)
            },
            _ => Err(TypeError::ExpectedFunType {
                found: expected_ty.clone(),
            }),
        },

        Term::PairIntro(ref fst, ref snd) => match *expected_ty.inner {
            Value::PairType(ref fst_ty, ref snd_ty) => {
                check_term(context, fst, fst_ty)?;
                let fst_value = nbe::eval(fst, &context.values)?;
                check_term(context, snd, &nbe::do_closure_app(snd_ty, fst_value)?)
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

        _ => check_subtype(context, &synth_term(context, term)?, expected_ty),
    }
}

/// Synthesize the type of the term
pub fn synth_term(context: &Context, term: &RcTerm) -> Result<RcType, TypeError> {
    match *term.inner {
        Term::Var(index) => match context.lookup_ty(index) {
            None => Err(TypeError::UnboundVariable),
            Some(ann) => Ok(ann.clone()),
        },
        Term::Let(ref def, ref body) => {
            let mut body_context = context.clone();
            body_context.insert(nbe::eval(def, &context.values)?, synth_term(context, def)?);

            synth_term(&body_context, body)
        },

        Term::FunApp(ref fun, ref arg) => {
            let fun_ty = synth_term(context, fun)?;
            match *fun_ty.inner {
                Value::FunType(ref arg_ty, ref body_ty) => {
                    check_term(context, arg, arg_ty)?;
                    let arg_value = nbe::eval(arg, &context.values)?;
                    Ok(nbe::do_closure_app(body_ty, arg_value)?)
                },
                _ => Err(TypeError::ExpectedFunType {
                    found: fun_ty.clone(),
                }),
            }
        },

        Term::PairFst(ref pair) => {
            let pair_ty = synth_term(context, pair)?;
            match *pair_ty.inner {
                Value::PairType(ref fst_ty, _) => Ok(fst_ty.clone()),
                _ => Err(TypeError::ExpectedPairType {
                    found: pair_ty.clone(),
                }),
            }
        },
        Term::PairSnd(ref pair) => {
            let pair_ty = synth_term(context, pair)?;
            match *pair_ty.inner {
                Value::PairType(_, ref snd_ty) => {
                    let fst =
                        nbe::eval(&RcTerm::from(Term::PairFst(pair.clone())), &context.values)?;
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
pub fn check_term_ty(context: &Context, term: &RcTerm) -> Result<(), TypeError> {
    match *term.inner {
        Term::Let(ref def, ref body) => {
            let mut body_context = context.clone();
            body_context.insert(nbe::eval(def, &context.values)?, synth_term(context, def)?);

            check_term_ty(&body_context, body)
        },

        Term::FunType(ref ann, ref body) | Term::PairType(ref ann, ref body) => {
            check_term_ty(context, ann)?;
            let ann_value = nbe::eval(ann, &context.values)?;

            let mut body_context = context.clone();
            body_context.insert(RcValue::var(DbLevel(context.size)), ann_value);

            check_term_ty(&body_context, body)
        },

        Term::Universe(_) => Ok(()),

        _ => {
            let synth_ty = synth_term(context, term)?;
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
