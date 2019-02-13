//! Normalization by evaluation
//!
//! Here we implement a full normalization algorithm by first implementing
//! evaluation to `Value`s in weak-head-normal-form, and then reading it back
//! `Normal` terms.

use std::error::Error;
use std::fmt;

use crate::syntax::core::{RcTerm, Term};
use crate::syntax::domain::{self, Closure, RcType, RcValue, Value};
use crate::syntax::normal::{self, Normal, RcNormal};
use crate::syntax::{DbIndex, DbLevel, Label};

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

impl Error for NbeError {}

impl fmt::Display for NbeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "failed to normalize: {}", self.message)
    }
}

/// Return the field in from a record
fn do_record_proj(record: &RcValue, label: &Label) -> Result<RcValue, NbeError> {
    match record.as_ref() {
        Value::RecordIntro(fields) => match fields.iter().find(|(l, _)| l == label) {
            Some((_, term)) => Ok(term.clone()),
            None => Err(NbeError::new(format!(
                "do_record_proj: field `{}` not found in record",
                label.0,
            ))),
        },
        Value::Neutral(record_ne) => {
            let proj = domain::RcNeutral::from(domain::Neutral::RecordProj(
                record_ne.clone(),
                label.clone(),
            ));
            Ok(RcValue::from(Value::Neutral(proj)))
        },
        _ => Err(NbeError::new("do_record_proj: not a record")),
    }
}

/// Apply a closure to an argument
pub fn do_closure_app(closure: &Closure, arg: RcValue) -> Result<RcValue, NbeError> {
    let mut env = closure.env.clone();
    env.push_front(arg);
    eval(&closure.term, &env)
}

/// Apply a function to an argument
pub fn do_fun_app(fun: &RcValue, arg: RcValue) -> Result<RcValue, NbeError> {
    match fun.as_ref() {
        Value::FunIntro(_, body) => do_closure_app(body, arg),
        Value::Neutral(fun) => {
            let body = domain::RcNeutral::from(domain::Neutral::FunApp(fun.clone(), arg.clone()));
            Ok(RcValue::from(Value::Neutral(body)))
        },
        _ => Err(NbeError::new("do_ap: not a function")),
    }
}

/// Evaluate a term in the environment that corresponds to the context in which
/// the term was typed.
pub fn eval(term: &RcTerm, env: &domain::Env) -> Result<RcValue, NbeError> {
    match term.as_ref() {
        Term::Var(DbIndex(index)) => match env.get(*index as usize) {
            Some(value) => Ok(value.clone()),
            None => Err(NbeError::new("eval: variable not found")),
        },
        Term::Literal(literal) => Ok(RcValue::from(Value::Literal(literal.clone()))),
        Term::Let(def, /* _, */ body) => {
            let def = eval(def, env)?;
            let mut env = env.clone();
            env.push_front(def);
            eval(body, &env)
        },

        // Functions
        Term::FunType(param_ty, body_ty) => {
            let param_ty = eval(param_ty, env)?;
            let body_ty = Closure::new(body_ty.clone(), env.clone());

            Ok(RcValue::from(Value::FunType(param_ty, body_ty)))
        },
        Term::FunIntro(param_ty, body) => {
            let param_ty = eval(param_ty, env)?;
            let body = Closure::new(body.clone(), env.clone());

            Ok(RcValue::from(Value::FunIntro(param_ty, body)))
        },
        Term::FunApp(fun, arg) => do_fun_app(&eval(fun, env)?, eval(arg, env)?),

        // Records
        Term::RecordType(fields) => match fields.split_first() {
            None => Ok(RcValue::from(Value::RecordTypeEmpty)),
            Some(((_, label, ty), rest)) => {
                let label = label.clone();
                let ty = eval(ty, env)?;
                let rest_fields = rest.iter().cloned().collect(); // FIXME: Seems expensive?
                let rest = Closure::new(RcTerm::from(Term::RecordType(rest_fields)), env.clone());

                Ok(RcValue::from(Value::RecordTypeExtend(label, ty, rest)))
            },
        },
        Term::RecordIntro(fields) => {
            let fields = fields
                .iter()
                .map(|(label, term)| Ok((label.clone(), eval(term, env)?)))
                .collect::<Result<_, _>>()?;

            Ok(RcValue::from(Value::RecordIntro(fields)))
        },
        Term::RecordProj(record, label) => do_record_proj(&eval(record, env)?, label),

        // Universes
        Term::Universe(level) => Ok(RcValue::from(Value::Universe(*level))),
    }
}

/// Quote back a term into normal form
pub fn read_back_term(level: DbLevel, term: &RcValue) -> Result<RcNormal, NbeError> {
    match term.as_ref() {
        Value::Neutral(term) => {
            let neutral = read_back_neutral(level, term)?;

            Ok(RcNormal::from(Normal::Neutral(neutral)))
        },

        // Literals
        Value::Literal(literal) => Ok(RcNormal::from(Normal::Literal(literal.clone()))),

        // Functions
        Value::FunType(param_ty, body_ty) => {
            let param = RcValue::var(level);
            let param_ty = read_back_term(level, param_ty)?;
            let body_ty = read_back_term(level + 1, &do_closure_app(body_ty, param)?)?;

            Ok(RcNormal::from(Normal::FunType(param_ty, body_ty)))
        },
        Value::FunIntro(param_ty, body) => {
            let param = RcValue::var(level);
            let param_ty = read_back_term(level, &param_ty)?;
            let body = read_back_term(level + 1, &do_closure_app(body, param)?)?;

            Ok(RcNormal::from(Normal::FunIntro(param_ty, body)))
        },

        // Records
        Value::RecordTypeExtend(label, term_ty, rest_ty) => {
            let mut level = level;

            let term = RcValue::var(level);
            let term_ty = read_back_term(level, term_ty)?;

            let mut rest_ty = do_closure_app(rest_ty, term)?;
            let mut field_tys = vec![(label.clone(), term_ty)];

            while let Value::RecordTypeExtend(next_label, next_term_ty, next_rest_ty) =
                rest_ty.as_ref()
            {
                level += 1;
                let next_term = RcValue::var(level);

                field_tys.push((next_label.clone(), read_back_term(level, next_term_ty)?));
                rest_ty = do_closure_app(next_rest_ty, next_term)?;
            }

            Ok(RcNormal::from(Normal::RecordType(field_tys)))
        },
        Value::RecordTypeEmpty => Ok(RcNormal::from(Normal::RecordType(Vec::new()))),
        Value::RecordIntro(fields) => {
            let fields = fields
                .iter()
                .map(|(label, term)| Ok((label.clone(), read_back_term(level, term)?)))
                .collect::<Result<_, _>>()?;

            Ok(RcNormal::from(Normal::RecordIntro(fields)))
        },

        // Universes
        Value::Universe(level) => Ok(RcNormal::from(Normal::Universe(*level))),
    }
}

/// Quote back a neutral term into normal form
pub fn read_back_neutral(
    level: DbLevel,
    neutral: &domain::RcNeutral,
) -> Result<normal::RcNeutral, NbeError> {
    match &neutral.as_ref() {
        domain::Neutral::Var(var_level) => {
            let index = DbIndex(level.0 - (var_level.0 + 1));

            Ok(normal::RcNeutral::from(normal::Neutral::Var(index)))
        },
        domain::Neutral::FunApp(fun, arg) => {
            let fun = read_back_neutral(level, fun)?;
            let arg = read_back_term(level, arg)?;

            Ok(normal::RcNeutral::from(normal::Neutral::FunApp(fun, arg)))
        },
        domain::Neutral::RecordProj(record, label) => {
            let record = read_back_neutral(level, record)?;
            let label = label.clone();

            Ok(normal::RcNeutral::from(normal::Neutral::RecordProj(
                record, label,
            )))
        },
    }
}

/// Check whether a semantic type is a subtype of another
pub fn check_subtype(level: DbLevel, ty1: &RcType, ty2: &RcType) -> Result<bool, NbeError> {
    match (&ty1.as_ref(), &ty2.as_ref()) {
        (&Value::Neutral(term1), &Value::Neutral(term2)) => {
            let term1 = read_back_neutral(level, term1)?;
            let term2 = read_back_neutral(level, term2)?;

            Ok(term1 == term2)
        },
        (&Value::FunType(param_ty1, body_ty1), &Value::FunType(param_ty2, body_ty2)) => {
            let param = RcValue::var(level);

            Ok(check_subtype(level, param_ty2, param_ty1)? && {
                let body_ty1 = do_closure_app(body_ty1, param.clone())?;
                let body_ty2 = do_closure_app(body_ty2, param)?;
                check_subtype(level + 1, &body_ty1, &body_ty2)?
            })
        },
        (
            &Value::RecordTypeExtend(label1, term_ty1, rest_ty1),
            &Value::RecordTypeExtend(label2, term_ty2, rest_ty2),
        ) => {
            let term = RcValue::var(level);

            Ok(
                // FIXME: Could stack overflow here?
                label1 == label2 && check_subtype(level, term_ty1, term_ty2)? && {
                    let rest_ty1 = do_closure_app(rest_ty1, term.clone())?;
                    let rest_ty2 = do_closure_app(rest_ty2, term)?;
                    check_subtype(level + 1, &rest_ty1, &rest_ty2)?
                },
            )
        },
        (&Value::RecordTypeEmpty, &Value::RecordTypeEmpty) => Ok(true),
        (&Value::Universe(level1), &Value::Universe(level2)) => Ok(level1 <= level2),
        _ => Ok(false),
    }
}
