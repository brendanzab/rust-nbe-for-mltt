//! Elaboration of the implicit syntax into the explicit syntax
//!
//! Performs the following:
//!
//! - name resolution
//! - pattern compilation (TODO)
//! - bidirectional type checking
//! - elaboration of holes (TODO)

use im;
use mltt_core::nbe::{self, NbeError};
use mltt_core::syntax::core;
use mltt_core::syntax::domain::{self, RcType, RcValue, Value};
use mltt_core::syntax::{DbIndex, DbLevel, UniverseLevel};

use crate::syntax::raw;

/// Local elaboration context
#[derive(Debug, Clone, PartialEq)]
pub struct Context<'term> {
    names: im::Vector<Option<&'term String>>,
    values: domain::Env,
    tys: domain::Env,
}

impl<'term> Context<'term> {
    pub fn new() -> Context<'term> {
        Context {
            names: im::Vector::new(),
            values: domain::Env::new(),
            tys: domain::Env::new(),
        }
    }

    pub fn insert(&mut self, ident: impl Into<Option<&'term String>>, value: RcValue, ty: RcType) {
        self.names.push_front(ident.into());
        self.values.push_front(value);
        self.tys.push_front(ty);
    }

    pub fn lookup_ty(&self, ident: &str) -> Option<(DbIndex, &RcType)> {
        let index = self
            .names
            .iter()
            .map(|n| n.map(String::as_str))
            .position(|n| Some(ident) == n)?;
        let ty = self.tys.get(index)?;
        Some((DbIndex(index as u32), ty))
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
    AmbiguousTerm(raw::RcTerm),
    UnboundVariable(String),
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

/// Check that a term conforms to a given type
pub fn check<'term>(
    context: &Context<'term>,
    size: u32,
    term: &'term raw::RcTerm,
    expected_ty: &RcType,
) -> Result<core::RcTerm, TypeError> {
    match *term.inner {
        raw::Term::Let(ref ident, ref raw_def, ref raw_body) => {
            let (def, def_ty) = synth(context, size, raw_def)?;
            let def_value = nbe::eval(&def, &context.values)?;
            let body = {
                let mut context = context.clone();
                context.insert(ident, def_value, def_ty);
                check(&context, size + 1, raw_body, expected_ty)?
            };

            Ok(core::RcTerm::from(core::Term::Let(def, body)))
        },

        raw::Term::FunType(ref ident, ref raw_param_ty, ref raw_body_ty) => {
            let param_ty = check_ty(context, size, raw_param_ty)?;
            let param_ty_value = nbe::eval(&param_ty, &context.values)?;
            let body_ty = {
                let mut context = context.clone();
                context.insert(ident, RcValue::var(DbLevel(size)), param_ty_value);
                check_ty(&context, size + 1, raw_body_ty)?
            };

            Ok(core::RcTerm::from(core::Term::FunType(param_ty, body_ty)))
        },
        raw::Term::FunIntro(ref ident, ref body) => match *expected_ty.inner {
            Value::FunType(ref param_ty, ref body_ty) => {
                let param = RcValue::var(DbLevel(size));
                let body_ty = nbe::do_closure_app(body_ty, param.clone())?;
                let body = {
                    let mut context = context.clone();
                    context.insert(ident, param, param_ty.clone());
                    check(&context, size + 1, body, &body_ty)?
                };

                Ok(core::RcTerm::from(core::Term::FunIntro(body)))
            },
            _ => Err(TypeError::ExpectedFunType {
                found: expected_ty.clone(),
            }),
        },

        raw::Term::PairType(ref ident, ref raw_fst_ty, ref raw_snd_ty) => {
            let fst_ty = check_ty(context, size, raw_fst_ty)?;
            let fst_ty_value = nbe::eval(&fst_ty, &context.values)?;
            let snd_ty = {
                let mut context = context.clone();
                context.insert(ident, RcValue::var(DbLevel(size)), fst_ty_value);
                check_ty(&context, size + 1, raw_snd_ty)?
            };

            Ok(core::RcTerm::from(core::Term::PairType(fst_ty, snd_ty)))
        },
        raw::Term::PairIntro(ref raw_fst, ref raw_snd) => match *expected_ty.inner {
            Value::PairType(ref fst_ty, ref snd_ty) => {
                let fst = check(context, size, raw_fst, fst_ty)?;
                let fst_value = nbe::eval(&fst, &context.values)?;
                let snd_ty_value = nbe::do_closure_app(snd_ty, fst_value)?;
                let snd = check(context, size, raw_snd, &snd_ty_value)?;

                Ok(core::RcTerm::from(core::Term::PairIntro(fst, snd)))
            },
            _ => Err(TypeError::ExpectedPairType {
                found: expected_ty.clone(),
            }),
        },

        raw::Term::Universe(term_level) => match *expected_ty.inner {
            Value::Universe(ann_level) if term_level < ann_level => {
                Ok(core::RcTerm::from(core::Term::Universe(term_level)))
            },
            _ => Err(TypeError::ExpectedUniverse {
                over: Some(term_level),
                found: expected_ty.clone(),
            }),
        },

        _ => {
            let (synth, synth_ty) = synth(context, size, term)?;
            check_subtype(size, &synth_ty, expected_ty)?;
            Ok(synth)
        },
    }
}

/// Synthesize the type of the term
pub fn synth<'term>(
    context: &Context<'term>,
    size: u32,
    raw_term: &'term raw::RcTerm,
) -> Result<(core::RcTerm, RcType), TypeError> {
    match *raw_term.inner {
        raw::Term::Var(ref ident) => match context.lookup_ty(ident.as_str()) {
            None => Err(TypeError::UnboundVariable(ident.clone())),
            Some((index, ann)) => Ok((core::RcTerm::from(core::Term::Var(index)), ann.clone())),
        },
        raw::Term::Let(ref ident, ref raw_def, ref raw_body) => {
            let (def, def_ty) = synth(context, size, raw_def)?;
            let def_value = nbe::eval(&def, &context.values)?;
            let (body, body_ty) = {
                let mut context = context.clone();
                context.insert(ident, def_value, def_ty);
                synth(&context, size + 1, raw_body)?
            };

            Ok((core::RcTerm::from(core::Term::Let(def, body)), body_ty))
        },
        raw::Term::Ann(ref raw_term, ref raw_ann) => {
            let ann = check_ty(context, size, raw_ann)?;
            let ann_value = nbe::eval(&ann, &context.values)?;
            let term = check(context, size, raw_term, &ann_value)?;

            Ok((term, ann_value))
        },

        raw::Term::FunApp(ref raw_fun, ref raw_arg) => {
            let (fun, fun_ty) = synth(context, size, raw_fun)?;
            match *fun_ty.inner {
                Value::FunType(ref param_ty, ref body_ty) => {
                    let arg = check(context, size, raw_arg, param_ty)?;
                    let arg_value = nbe::eval(&arg, &context.values)?;
                    let term = core::RcTerm::from(core::Term::FunApp(fun, arg));

                    Ok((term, nbe::do_closure_app(body_ty, arg_value)?))
                },
                _ => Err(TypeError::ExpectedFunType {
                    found: fun_ty.clone(),
                }),
            }
        },

        raw::Term::PairFst(ref raw_pair) => {
            let (pair, pair_ty) = synth(context, size, raw_pair)?;
            match *pair_ty.inner {
                Value::PairType(ref fst_ty, _) => {
                    let fst = core::RcTerm::from(core::Term::PairFst(pair.clone()));
                    Ok((fst, fst_ty.clone()))
                },
                _ => Err(TypeError::ExpectedPairType {
                    found: pair_ty.clone(),
                }),
            }
        },
        raw::Term::PairSnd(ref raw_pair) => {
            let (pair, pair_ty) = synth(context, size, raw_pair)?;
            match *pair_ty.inner {
                Value::PairType(_, ref snd_ty) => {
                    let fst = core::RcTerm::from(core::Term::PairFst(pair.clone()));
                    let fst_value = nbe::eval(&fst, &context.values)?;
                    let snd = core::RcTerm::from(core::Term::PairSnd(pair));

                    Ok((snd, nbe::do_closure_app(snd_ty, fst_value)?))
                },
                _ => Err(TypeError::ExpectedPairType {
                    found: pair_ty.clone(),
                }),
            }
        },

        _ => Err(TypeError::AmbiguousTerm(raw_term.clone())),
    }
}

/// Check that the given term is a type
pub fn check_ty<'term>(
    context: &Context<'term>,
    size: u32,
    raw_term: &'term raw::RcTerm,
) -> Result<core::RcTerm, TypeError> {
    match *raw_term.inner {
        raw::Term::Let(ref ident, ref raw_def, ref raw_body) => {
            let (def, def_ty) = synth(context, size, raw_def)?;
            let def_value = nbe::eval(&def, &context.values)?;
            let body = {
                let mut context = context.clone();
                context.insert(ident, def_value, def_ty);
                check_ty(&context, size + 1, raw_body)?
            };

            Ok(core::RcTerm::from(core::Term::Let(def, body)))
        },

        raw::Term::FunType(ref ident, ref raw_param_ty, ref raw_body_ty) => {
            let param_ty = check_ty(context, size, raw_param_ty)?;
            let param_ty_value = nbe::eval(&param_ty, &context.values)?;
            let body_ty = {
                let mut context = context.clone();
                context.insert(ident, RcValue::var(DbLevel(size)), param_ty_value);
                check_ty(&context, size + 1, raw_body_ty)?
            };

            Ok(core::RcTerm::from(core::Term::FunType(param_ty, body_ty)))
        },

        raw::Term::PairType(ref ident, ref raw_fst_ty, ref raw_snd_ty) => {
            let fst_ty = check_ty(context, size, raw_fst_ty)?;
            let fst_ty_value = nbe::eval(&fst_ty, &context.values)?;
            let snd_ty = {
                let mut snd_ty_context = context.clone();
                snd_ty_context.insert(ident, RcValue::var(DbLevel(size)), fst_ty_value);
                check_ty(&snd_ty_context, size + 1, raw_snd_ty)?
            };

            Ok(core::RcTerm::from(core::Term::PairType(fst_ty, snd_ty)))
        },

        raw::Term::Universe(level) => Ok(core::RcTerm::from(core::Term::Universe(level))),

        _ => {
            let (term, term_ty) = synth(context, size, raw_term)?;
            match *term_ty.inner {
                Value::Universe(_) => Ok(term),
                _ => Err(TypeError::ExpectedUniverse {
                    over: None,
                    found: term_ty,
                }),
            }
        },
    }
}
