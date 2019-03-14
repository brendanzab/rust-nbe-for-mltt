//! Bidirectional type checking of the core syntax
//!
//! This is used to verify that the core syntax is correctly formed, for
//! debugging purposes.

use std::error::Error;
use std::fmt;

use crate::nbe::{self, NbeError};
use crate::syntax::core::{Item, RcTerm, Term};
use crate::syntax::domain::{RcType, RcValue, Value};
use crate::syntax::{AppMode, Env, Label, LiteralIntro, LiteralType, UniverseLevel, VarLevel};

/// Local type checking context.
#[derive(Debug, Clone, PartialEq)]
pub struct Context {
    /// Number of local entries.
    level: VarLevel,
    /// Values to be used during evaluation.
    values: Env<RcValue>,
    /// Types of the entries in the context.
    tys: Env<RcType>,
}

impl Context {
    /// Create a new, empty context
    pub fn new() -> Context {
        Context {
            level: VarLevel(0),
            values: Env::new(),
            tys: Env::new(),
        }
    }

    /// Number of local entries in the context
    pub fn level(&self) -> VarLevel {
        self.level
    }

    /// Values to be used during evaluation
    pub fn values(&self) -> &Env<RcValue> {
        &self.values
    }

    /// Types of the entries in the context
    pub fn tys(&self) -> &Env<RcType> {
        &self.tys
    }

    /// Add a local definition to the context.
    pub fn local_define(&mut self, value: RcValue, ty: RcType) {
        self.level += 1;
        self.values.add_entry(value);
        self.tys.add_entry(ty);
    }

    /// Add a bound variable the context, returning a variable that points to
    /// the correct binder.
    pub fn local_bind(&mut self, ty: RcType) -> RcValue {
        let param = RcValue::var(self.level());
        self.local_define(param.clone(), ty);
        param
    }

    /// Evaluate a term using the evaluation environment
    pub fn eval(&self, term: &RcTerm) -> Result<RcValue, NbeError> {
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

impl Default for Context {
    fn default() -> Context {
        let mut context = Context::new();
        let u0 = RcValue::from(Value::Universe(UniverseLevel(0)));
        let lit_ty = |ty| RcValue::from(Value::LiteralType(ty));

        context.local_define(lit_ty(LiteralType::String), u0.clone());
        context.local_define(lit_ty(LiteralType::Char), u0.clone());
        context.local_define(lit_ty(LiteralType::U8), u0.clone());
        context.local_define(lit_ty(LiteralType::U16), u0.clone());
        context.local_define(lit_ty(LiteralType::U32), u0.clone());
        context.local_define(lit_ty(LiteralType::U64), u0.clone());
        context.local_define(lit_ty(LiteralType::S8), u0.clone());
        context.local_define(lit_ty(LiteralType::S16), u0.clone());
        context.local_define(lit_ty(LiteralType::S32), u0.clone());
        context.local_define(lit_ty(LiteralType::S64), u0.clone());
        context.local_define(lit_ty(LiteralType::F32), u0.clone());
        context.local_define(lit_ty(LiteralType::F64), u0.clone());

        context
    }
}

/// An error produced during type checking
#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    ExpectedFunType { found: RcType },
    ExpectedPairType { found: RcType },
    ExpectedUniverse { found: RcType },
    ExpectedSubtype(RcType, RcType),
    AmbiguousTerm(RcTerm),
    UnboundVariable,
    NoFieldInType(Label),
    UnexpectedField { found: Label, expected: Label },
    UnexpectedAppMode { found: AppMode, expected: AppMode },
    TooManyFieldsFound,
    NotEnoughFieldsProvided,
    Nbe(NbeError),
}

impl From<NbeError> for TypeError {
    fn from(src: NbeError) -> TypeError {
        TypeError::Nbe(src)
    }
}

impl Error for TypeError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            TypeError::Nbe(error) => Some(error),
            _ => None,
        }
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::ExpectedFunType { .. } => write!(f, "expected function type"),
            TypeError::ExpectedPairType { .. } => write!(f, "expected function type"),
            TypeError::ExpectedUniverse { .. } => write!(f, "expected universe"),
            TypeError::ExpectedSubtype(..) => write!(f, "not a subtype"),
            TypeError::AmbiguousTerm(..) => write!(f, "could not infer the type"),
            TypeError::UnboundVariable => write!(f, "unbound variable"),
            TypeError::NoFieldInType(label) => write!(f, "no field in type `{}`", label),
            TypeError::UnexpectedField { found, expected } => write!(
                f,
                "unexpected field, found `{}`, but expected `{}`",
                found, expected,
            ),
            TypeError::UnexpectedAppMode { found, expected } => write!(
                f,
                "unexpected application mode, found `{:?}`, but expected `{:?}`",
                found, expected,
            ),
            TypeError::TooManyFieldsFound => write!(f, "too many fields found"),
            TypeError::NotEnoughFieldsProvided => write!(f, "not enough fields provided"),
            TypeError::Nbe(err) => err.fmt(f),
        }
    }
}

/// Check that this is a valid module
pub fn check_module(context: &Context, items: &[Item]) -> Result<(), TypeError> {
    let mut context = context.clone();

    for item in items {
        log::trace!("checking item:\t\t{}", item.label);

        log::trace!("checking declaration:\t{}", item.term_ty);
        synth_universe(&context, &item.term_ty)?;
        let term_ty = context.eval(&item.term_ty)?;

        log::trace!("checking definition:\t{}", item.term);
        check_term(&context, &item.term, &term_ty)?;
        let value = context.eval(&item.term)?;

        log::trace!("validated item:\t\t{}", item.label);
        context.local_define(value, term_ty);
    }

    Ok(())
}

/// Ensures that the given term is a universe, returning the level of that universe
fn synth_universe(context: &Context, term: &RcTerm) -> Result<UniverseLevel, TypeError> {
    let ty = synth_term(context, term)?;
    match ty.as_ref() {
        Value::Universe(level) => Ok(*level),
        _ => Err(TypeError::ExpectedUniverse { found: ty.clone() }),
    }
}

/// Check that a term conforms to a given type
pub fn check_term(context: &Context, term: &RcTerm, expected_ty: &RcType) -> Result<(), TypeError> {
    log::trace!("checking term:\t\t{}", term);

    match term.as_ref() {
        Term::Let(def, body) => {
            let mut body_context = context.clone();
            body_context.local_define(context.eval(def)?, synth_term(context, def)?);

            check_term(&body_context, body, expected_ty)
        },

        Term::FunIntro(intro_app_mode, body) => match expected_ty.as_ref() {
            Value::FunType(ty_app_mode, param_ty, body_ty) if intro_app_mode == ty_app_mode => {
                let mut body_context = context.clone();
                let param = body_context.local_bind(param_ty.clone());
                let body_ty = nbe::do_closure_app(body_ty, param)?;

                check_term(&body_context, body, &body_ty)
            },
            Value::FunType(ty_app_mode, _, _) => Err(TypeError::UnexpectedAppMode {
                found: intro_app_mode.clone(),
                expected: ty_app_mode.clone(),
            }),
            _ => Err(TypeError::ExpectedFunType {
                found: expected_ty.clone(),
            }),
        },

        Term::RecordIntro(intro_fields) => {
            let mut context = context.clone();
            let mut expected_ty = expected_ty.clone();

            for (label, term) in intro_fields {
                if let Value::RecordTypeExtend(expected_label, expected_term_ty, rest) =
                    expected_ty.as_ref()
                {
                    if label != expected_label {
                        return Err(TypeError::UnexpectedField {
                            found: label.clone(),
                            expected: expected_label.clone(),
                        });
                    }

                    check_term(&context, term, expected_term_ty)?;
                    let term_value = context.eval(term)?;

                    context.local_define(term_value.clone(), expected_term_ty.clone());
                    expected_ty = nbe::do_closure_app(&rest, term_value)?;
                } else {
                    return Err(TypeError::TooManyFieldsFound);
                }
            }

            if let Value::RecordTypeEmpty = expected_ty.as_ref() {
                Ok(())
            } else {
                Err(TypeError::NotEnoughFieldsProvided)
            }
        },

        _ => context.expect_subtype(&synth_term(context, term)?, expected_ty),
    }
}

/// Synthesize the type of the term
pub fn synth_term(context: &Context, term: &RcTerm) -> Result<RcType, TypeError> {
    use std::cmp;

    log::trace!("synthesizing term:\t\t{}", term);

    match term.as_ref() {
        Term::Var(index) => match context.tys().lookup_entry(*index) {
            None => Err(TypeError::UnboundVariable),
            Some(ann) => Ok(ann.clone()),
        },
        Term::LiteralType(_) => Ok(RcValue::from(Value::Universe(UniverseLevel(0)))),
        Term::LiteralIntro(literal_intro) => {
            Ok(RcValue::from(Value::LiteralType(match literal_intro {
                LiteralIntro::String(_) => LiteralType::String,
                LiteralIntro::Char(_) => LiteralType::Char,
                LiteralIntro::U8(_) => LiteralType::U8,
                LiteralIntro::U16(_) => LiteralType::U16,
                LiteralIntro::U32(_) => LiteralType::U32,
                LiteralIntro::U64(_) => LiteralType::U64,
                LiteralIntro::S8(_) => LiteralType::S8,
                LiteralIntro::S16(_) => LiteralType::S16,
                LiteralIntro::S32(_) => LiteralType::S32,
                LiteralIntro::S64(_) => LiteralType::S64,
                LiteralIntro::F32(_) => LiteralType::F32,
                LiteralIntro::F64(_) => LiteralType::F64,
            })))
        },
        Term::Let(def, body) => {
            let mut body_context = context.clone();
            let def_ty = synth_term(context, def)?;
            body_context.local_define(context.eval(def)?, def_ty);

            synth_term(&body_context, body)
        },

        Term::FunType(_app_mode, param_ty, body_ty) => {
            let param_level = synth_universe(context, param_ty)?;
            let param_ty_value = context.eval(param_ty)?;

            let mut body_ty_context = context.clone();
            body_ty_context.local_bind(param_ty_value);

            let body_level = synth_universe(&body_ty_context, body_ty)?;

            Ok(RcValue::from(Value::Universe(cmp::max(
                param_level,
                body_level,
            ))))
        },
        Term::FunIntro(_, _) => Err(TypeError::AmbiguousTerm(term.clone())),

        Term::FunElim(fun, arg_app_mode, arg) => {
            let fun_ty = synth_term(context, fun)?;
            match fun_ty.as_ref() {
                Value::FunType(ty_app_mode, arg_ty, body_ty) if arg_app_mode == ty_app_mode => {
                    check_term(context, arg, arg_ty)?;
                    let arg_value = context.eval(arg)?;
                    Ok(nbe::do_closure_app(body_ty, arg_value)?)
                },
                Value::FunType(ty_app_mode, _, _) => Err(TypeError::UnexpectedAppMode {
                    found: arg_app_mode.clone(),
                    expected: ty_app_mode.clone(),
                }),
                _ => Err(TypeError::ExpectedFunType {
                    found: fun_ty.clone(),
                }),
            }
        },

        Term::RecordType(ty_fields) => {
            let mut context = context.clone();
            let mut max_level = UniverseLevel(0);

            for (_, _, ty) in ty_fields {
                let ty_level = synth_universe(&context, &ty)?;
                context.local_bind(context.eval(&ty)?);
                max_level = cmp::max(max_level, ty_level);
            }

            Ok(RcValue::from(Value::Universe(max_level)))
        },
        Term::RecordIntro(_) => Err(TypeError::AmbiguousTerm(term.clone())),
        Term::RecordElim(record, label) => {
            let mut record_ty = synth_term(context, record)?;

            while let Value::RecordTypeExtend(current_label, current_ty, rest) = record_ty.as_ref()
            {
                if label == current_label {
                    return Ok(current_ty.clone());
                } else {
                    let label = current_label.clone();
                    let expr = RcTerm::from(Term::RecordElim(record.clone(), label));
                    record_ty = nbe::do_closure_app(rest, context.eval(&expr)?)?;
                }
            }

            Err(TypeError::NoFieldInType(label.clone()))
        },

        Term::Universe(level) => Ok(RcValue::from(Value::Universe(*level + 1))),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::syntax::VarIndex;

    #[test]
    fn local_binds() {
        let mut context = Context::new();

        let ty1 = RcValue::from(Value::Universe(UniverseLevel(0)));
        let ty2 = RcValue::from(Value::Universe(UniverseLevel(1)));
        let ty3 = RcValue::from(Value::Universe(UniverseLevel(2)));

        let param1 = context.local_bind(ty1.clone());
        let param2 = context.local_bind(ty2.clone());
        let param3 = context.local_bind(ty3.clone());

        assert_eq!(param1, RcValue::from(Value::var(VarLevel(0))));
        assert_eq!(param2, RcValue::from(Value::var(VarLevel(1))));
        assert_eq!(param3, RcValue::from(Value::var(VarLevel(2))));

        assert_eq!(context.tys().lookup_entry(VarIndex(2)).unwrap(), &ty1);
        assert_eq!(context.tys().lookup_entry(VarIndex(1)).unwrap(), &ty2);
        assert_eq!(context.tys().lookup_entry(VarIndex(0)).unwrap(), &ty3);
    }
}
