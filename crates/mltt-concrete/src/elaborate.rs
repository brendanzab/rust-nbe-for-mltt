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
use std::error::Error;
use std::fmt;

use crate::syntax::raw;

/// Local elaboration context
#[derive(Debug, Clone, PartialEq)]
pub struct Context<'term> {
    /// Number of local entries
    level: DbLevel,
    /// Values to be used during evaluation
    values: domain::Env,
    /// The user-defined names and type annotations of the binders we have passed over
    binders: im::Vector<(Option<&'term String>, RcType)>,
}

impl<'term> Context<'term> {
    /// Create a new, empty context
    pub fn new() -> Context<'term> {
        Context {
            level: DbLevel(0),
            values: domain::Env::new(),
            binders: im::Vector::new(),
        }
    }

    /// Number of local entries in the context
    pub fn level(&self) -> DbLevel {
        self.level
    }

    /// Values to be used during evaluation
    pub fn values(&self) -> &domain::Env {
        &self.values
    }

    /// Add a new local entry to the context
    pub fn insert_local(
        &mut self,
        name: impl Into<Option<&'term String>>,
        value: RcValue,
        ty: RcType,
    ) {
        self.level += 1;
        self.values.push_front(value);
        self.binders.push_front((name.into(), ty));
    }

    /// Add a new binder to the context, returning a value that points to the parameter
    pub fn insert_binder(&mut self, name: impl Into<Option<&'term String>>, ty: RcType) -> RcValue {
        let param = RcValue::var(self.level());
        self.insert_local(name, param.clone(), ty);
        param
    }

    /// Lookup the de-bruijn index and the type annotation of a binder in the
    /// context using a user-defined name
    pub fn lookup_binder(&self, name: &str) -> Option<(DbIndex, &RcType)> {
        for (i, &(ref n, ref ty)) in self.binders.iter().enumerate() {
            if Some(name) == n.map(String::as_str) {
                return Some((DbIndex(i as u32), ty));
            }
        }
        None
    }

    /// Evaluate a term using the evaluation environment
    pub fn eval(&self, term: &core::RcTerm) -> Result<domain::RcValue, NbeError> {
        nbe::eval(term, self.values())
    }

    /// Expect that `ty1` is a subtype of `ty2` in the current context
    pub fn expect_subtype(&self, ty1: &RcType, ty2: &RcType) -> Result<(), TypeError> {
        if nbe::check_subtype(self.level(), ty1, ty2)? {
            Ok(())
        } else {
            Err(TypeError::ExpectedSubtype(ty1.clone(), ty2.clone()))
        }
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

impl Error for TypeError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match *self {
            TypeError::Nbe(ref error) => Some(error),
            _ => None,
        }
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypeError::ExpectedFunType { .. } => write!(f, "expected function type"),
            TypeError::ExpectedPairType { .. } => write!(f, "expected function type"),
            TypeError::ExpectedUniverse { over, .. } => match over {
                None => write!(f, "expected universe"),
                Some(level) => write!(f, "expected universe over level `{}`", level.0),
            },
            TypeError::ExpectedSubtype(..) => write!(f, "not a subtype"),
            TypeError::AmbiguousTerm(..) => write!(f, "could not infer the type"),
            TypeError::UnboundVariable(ref name) => write!(f, "unbound variable `{}`", name),
            TypeError::Nbe(ref err) => err.fmt(f),
        }
    }
}

/// Check that a given term conforms to an expected type
pub fn check_term<'term>(
    context: &Context<'term>,
    term: &'term raw::RcTerm,
    expected_ty: &RcType,
) -> Result<core::RcTerm, TypeError> {
    match *term.inner {
        raw::Term::Let(ref name, ref raw_def, ref raw_body) => {
            let (def, def_ty) = synth_term(context, raw_def)?;
            let def_value = context.eval(&def)?;
            let body = {
                let mut context = context.clone();
                context.insert_local(name, def_value, def_ty);
                check_term(&context, raw_body, expected_ty)?
            };

            Ok(core::RcTerm::from(core::Term::Let(def, body)))
        },

        raw::Term::FunType(ref name, ref raw_param_ty, ref raw_body_ty) => {
            let param_ty = check_term_ty(context, raw_param_ty)?;
            let param_ty_value = context.eval(&param_ty)?;
            let body_ty = {
                let mut context = context.clone();
                context.insert_binder(name, param_ty_value);
                check_term_ty(&context, raw_body_ty)?
            };

            Ok(core::RcTerm::from(core::Term::FunType(param_ty, body_ty)))
        },
        raw::Term::FunIntro(ref name, ref body) => match *expected_ty.inner {
            Value::FunType(ref param_ty, ref body_ty) => {
                let mut context = context.clone();
                let param = context.insert_binder(name, param_ty.clone());
                let body_ty = nbe::do_closure_app(body_ty, param.clone())?;
                let body = check_term(&context, body, &body_ty)?;

                Ok(core::RcTerm::from(core::Term::FunIntro(body)))
            },
            _ => Err(TypeError::ExpectedFunType {
                found: expected_ty.clone(),
            }),
        },

        raw::Term::PairType(ref name, ref raw_fst_ty, ref raw_snd_ty) => {
            let fst_ty = check_term_ty(context, raw_fst_ty)?;
            let fst_ty_value = context.eval(&fst_ty)?;
            let snd_ty = {
                let mut context = context.clone();
                context.insert_binder(name, fst_ty_value);
                check_term_ty(&context, raw_snd_ty)?
            };

            Ok(core::RcTerm::from(core::Term::PairType(fst_ty, snd_ty)))
        },
        raw::Term::PairIntro(ref raw_fst, ref raw_snd) => match *expected_ty.inner {
            Value::PairType(ref fst_ty, ref snd_ty) => {
                let fst = check_term(context, raw_fst, fst_ty)?;
                let fst_value = context.eval(&fst)?;
                let snd_ty_value = nbe::do_closure_app(snd_ty, fst_value)?;
                let snd = check_term(context, raw_snd, &snd_ty_value)?;

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
            let (synth, synth_ty) = synth_term(context, term)?;
            context.expect_subtype(&synth_ty, expected_ty)?;
            Ok(synth)
        },
    }
}

/// Synthesize the type of the given term
pub fn synth_term<'term>(
    context: &Context<'term>,
    raw_term: &'term raw::RcTerm,
) -> Result<(core::RcTerm, RcType), TypeError> {
    match *raw_term.inner {
        raw::Term::Var(ref name) => match context.lookup_binder(name.as_str()) {
            None => Err(TypeError::UnboundVariable(name.clone())),
            Some((index, ann)) => Ok((core::RcTerm::from(core::Term::Var(index)), ann.clone())),
        },
        raw::Term::Let(ref name, ref raw_def, ref raw_body) => {
            let (def, def_ty) = synth_term(context, raw_def)?;
            let def_value = context.eval(&def)?;
            let (body, body_ty) = {
                let mut context = context.clone();
                context.insert_local(name, def_value, def_ty);
                synth_term(&context, raw_body)?
            };

            Ok((core::RcTerm::from(core::Term::Let(def, body)), body_ty))
        },
        raw::Term::Ann(ref raw_term, ref raw_ann) => {
            let ann = check_term_ty(context, raw_ann)?;
            let ann_value = context.eval(&ann)?;
            let term = check_term(context, raw_term, &ann_value)?;

            Ok((term, ann_value))
        },

        raw::Term::FunApp(ref raw_fun, ref raw_arg) => {
            let (fun, fun_ty) = synth_term(context, raw_fun)?;
            match *fun_ty.inner {
                Value::FunType(ref param_ty, ref body_ty) => {
                    let arg = check_term(context, raw_arg, param_ty)?;
                    let arg_value = context.eval(&arg)?;
                    let term = core::RcTerm::from(core::Term::FunApp(fun, arg));

                    Ok((term, nbe::do_closure_app(body_ty, arg_value)?))
                },
                _ => Err(TypeError::ExpectedFunType {
                    found: fun_ty.clone(),
                }),
            }
        },

        raw::Term::PairFst(ref raw_pair) => {
            let (pair, pair_ty) = synth_term(context, raw_pair)?;
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
            let (pair, pair_ty) = synth_term(context, raw_pair)?;
            match *pair_ty.inner {
                Value::PairType(_, ref snd_ty) => {
                    let fst = core::RcTerm::from(core::Term::PairFst(pair.clone()));
                    let fst_value = context.eval(&fst)?;
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
pub fn check_term_ty<'term>(
    context: &Context<'term>,
    raw_term: &'term raw::RcTerm,
) -> Result<core::RcTerm, TypeError> {
    match *raw_term.inner {
        raw::Term::Let(ref name, ref raw_def, ref raw_body) => {
            let (def, def_ty) = synth_term(context, raw_def)?;
            let def_value = context.eval(&def)?;
            let body = {
                let mut context = context.clone();
                context.insert_local(name, def_value, def_ty);
                check_term_ty(&context, raw_body)?
            };

            Ok(core::RcTerm::from(core::Term::Let(def, body)))
        },

        raw::Term::FunType(ref name, ref raw_param_ty, ref raw_body_ty) => {
            let param_ty = check_term_ty(context, raw_param_ty)?;
            let param_ty_value = context.eval(&param_ty)?;
            let body_ty = {
                let mut context = context.clone();
                context.insert_binder(name, param_ty_value);
                check_term_ty(&context, raw_body_ty)?
            };

            Ok(core::RcTerm::from(core::Term::FunType(param_ty, body_ty)))
        },

        raw::Term::PairType(ref name, ref raw_fst_ty, ref raw_snd_ty) => {
            let fst_ty = check_term_ty(context, raw_fst_ty)?;
            let fst_ty_value = context.eval(&fst_ty)?;
            let snd_ty = {
                let mut snd_ty_context = context.clone();
                snd_ty_context.insert_binder(name, fst_ty_value);
                check_term_ty(&snd_ty_context, raw_snd_ty)?
            };

            Ok(core::RcTerm::from(core::Term::PairType(fst_ty, snd_ty)))
        },

        raw::Term::Universe(level) => Ok(core::RcTerm::from(core::Term::Universe(level))),

        _ => {
            let (term, term_ty) = synth_term(context, raw_term)?;
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
