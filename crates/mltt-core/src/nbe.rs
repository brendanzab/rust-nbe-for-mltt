//! Normalization by evaluation
//!
//! Here we implement a full normalization algorithm by first implementing
//! evaluation to `Value`s in weak-head-normal-form, and then reading it back
//! `Normal` terms.

use std::error::Error;
use std::fmt;

use crate::syntax::core::{RcTerm, Term};
use crate::syntax::domain::{Closure, Elim, Head, RcType, RcValue, Spine, Value};
use crate::syntax::{AppMode, Env, Label, VarIndex, VarLevel};

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
fn do_record_elim(record: &RcValue, label: &Label) -> Result<RcValue, NbeError> {
    match record.as_ref() {
        Value::RecordIntro(fields) => match fields.iter().find(|(l, _)| l == label) {
            Some((_, term)) => Ok(term.clone()),
            None => Err(NbeError::new(format!(
                "do_record_elim: field `{}` not found in record",
                label.0,
            ))),
        },
        Value::Neutral(head, spine) => {
            let mut spine = spine.clone();
            spine.push(Elim::Record(label.clone()));
            Ok(RcValue::from(Value::Neutral(*head, spine)))
        },
        _ => Err(NbeError::new("do_record_elim: not a record")),
    }
}

/// Apply a closure to an argument
pub fn do_closure_app(closure: &Closure, arg: RcValue) -> Result<RcValue, NbeError> {
    let mut env = closure.env.clone();
    env.add_entry(arg);
    eval(&closure.term, &env)
}

/// Apply a function to an argument
pub fn do_fun_elim(fun: &RcValue, app_mode: AppMode, arg: RcValue) -> Result<RcValue, NbeError> {
    match fun.as_ref() {
        Value::FunIntro(fun_app_mode, body) => {
            if *fun_app_mode == app_mode {
                do_closure_app(body, arg)
            } else {
                Err(NbeError::new(format!(
                    "do_ap: unexpected application mode - {:?} != {:?}",
                    fun_app_mode, app_mode,
                )))
            }
        },
        Value::Neutral(head, spine) => {
            let mut spine = spine.clone();
            spine.push(Elim::Fun(app_mode, arg));
            Ok(RcValue::from(Value::Neutral(*head, spine)))
        },
        _ => Err(NbeError::new("do_ap: not a function")),
    }
}

/// Evaluate a term in the environment that corresponds to the context in which
/// the term was typed.
pub fn eval(term: &RcTerm, env: &Env<RcValue>) -> Result<RcValue, NbeError> {
    match term.as_ref() {
        Term::Var(index) => match env.lookup_entry(*index) {
            Some(value) => {
                log::trace!("lookup value: {} -> {:?}", index, value);

                let mut value = value.clone();
                value.lift(env.shift());
                Ok(value.clone())
            },
            None => Err(NbeError::new("eval: variable not found")),
        },
        Term::LiteralType(literal_ty) => Ok(RcValue::from(Value::LiteralType(literal_ty.clone()))),
        Term::LiteralIntro(literal_intro) => {
            Ok(RcValue::from(Value::LiteralIntro(literal_intro.clone())))
        },
        Term::Let(def, body) => {
            let def = eval(def, env)?;
            let mut env = env.clone();
            env.add_entry(def);
            eval(body, &env)
        },
        Term::Lift(term, shift) => {
            let mut env = env.clone();
            env.lift(*shift);
            eval(term, &env)
        },

        // Functions
        Term::FunType(app_mode, param_ty, body_ty) => {
            let app_mode = app_mode.clone();
            let param_ty = eval(param_ty, env)?;
            let body_ty = Closure::new(body_ty.clone(), env.clone());

            Ok(RcValue::from(Value::FunType(app_mode, param_ty, body_ty)))
        },
        Term::FunIntro(app_mode, body) => {
            let app_mode = app_mode.clone();
            let body = Closure::new(body.clone(), env.clone());

            Ok(RcValue::from(Value::FunIntro(app_mode, body)))
        },
        Term::FunElim(fun, app_mode, arg) => {
            let fun = eval(fun, env)?;
            let app_mode = app_mode.clone();
            let arg = eval(arg, env)?;

            do_fun_elim(&fun, app_mode, arg)
        },

        // Records
        Term::RecordType(fields) => match fields.split_first() {
            None => Ok(RcValue::from(Value::RecordTypeEmpty)),
            Some(((_, label, ty), rest)) => {
                let label = label.clone();
                let ty = eval(ty, env)?;
                // FIXME: Seems expensive?
                let rest_fields = RcTerm::from(Term::RecordType(rest.iter().cloned().collect()));
                let rest = Closure::new(rest_fields, env.clone());

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
        Term::RecordElim(record, label) => do_record_elim(&eval(record, env)?, label),

        // Universes
        Term::Universe(level) => Ok(RcValue::from(Value::Universe(*level + env.shift()))),
    }
}

/// Read a value back into the core syntax, normalizing as required.
pub fn read_back_term(level: VarLevel, term: &RcValue) -> Result<RcTerm, NbeError> {
    match term.as_ref() {
        Value::Neutral(head, spine) => read_back_neutral(level, *head, spine),

        // Literals
        Value::LiteralType(literal_ty) => Ok(RcTerm::from(Term::LiteralType(literal_ty.clone()))),
        Value::LiteralIntro(literal_intro) => {
            Ok(RcTerm::from(Term::LiteralIntro(literal_intro.clone())))
        },

        // Functions
        Value::FunType(app_mode, param_ty, body_ty) => {
            let app_mode = app_mode.clone();
            let param = RcValue::var(level);
            let param_ty = read_back_term(level, param_ty)?;
            let body_ty = read_back_term(level + 1, &do_closure_app(body_ty, param)?)?;

            Ok(RcTerm::from(Term::FunType(app_mode, param_ty, body_ty)))
        },
        Value::FunIntro(app_mode, body) => {
            let app_mode = app_mode.clone();
            let param = RcValue::var(level);
            let body = read_back_term(level + 1, &do_closure_app(body, param)?)?;

            Ok(RcTerm::from(Term::FunIntro(app_mode, body)))
        },

        // Records
        Value::RecordTypeExtend(label, term_ty, rest_ty) => {
            let mut level = level;

            let term = RcValue::var(level);
            let term_ty = read_back_term(level, term_ty)?;

            let mut rest_ty = do_closure_app(rest_ty, term)?;
            let mut field_tys = vec![(String::new(), label.clone(), term_ty)];

            while let Value::RecordTypeExtend(next_label, next_term_ty, next_rest_ty) =
                rest_ty.as_ref()
            {
                level += 1;
                let next_term = RcValue::var(level);

                field_tys.push((
                    String::new(),
                    next_label.clone(),
                    read_back_term(level, next_term_ty)?,
                ));
                rest_ty = do_closure_app(next_rest_ty, next_term)?;
            }

            Ok(RcTerm::from(Term::RecordType(field_tys)))
        },
        Value::RecordTypeEmpty => Ok(RcTerm::from(Term::RecordType(Vec::new()))),
        Value::RecordIntro(fields) => {
            let fields = fields
                .iter()
                .map(|(label, term)| Ok((label.clone(), read_back_term(level, term)?)))
                .collect::<Result<_, _>>()?;

            Ok(RcTerm::from(Term::RecordIntro(fields)))
        },

        // Universes
        Value::Universe(level) => Ok(RcTerm::from(Term::Universe(*level))),
    }
}

/// Read a neutral value back into the core syntax, normalizing as required.
pub fn read_back_neutral(level: VarLevel, head: Head, spine: &Spine) -> Result<RcTerm, NbeError> {
    let head = match head {
        Head::Var(var_level) => RcTerm::from(Term::Var(VarIndex(level.0 - (var_level.0 + 1)))),
    };

    spine.iter().fold(Ok(head), |acc, elim| match elim {
        Elim::Fun(app_mode, arg) => Ok(RcTerm::from(Term::FunElim(
            acc?,
            app_mode.clone(),
            read_back_term(level, arg)?,
        ))),
        Elim::Record(label) => Ok(RcTerm::from(Term::RecordElim(acc?, label.clone()))),
    })
}

/// Check whether a semantic type is a subtype of another
pub fn check_subtype(level: VarLevel, ty1: &RcType, ty2: &RcType) -> Result<bool, NbeError> {
    match (&ty1.as_ref(), &ty2.as_ref()) {
        (&Value::Neutral(head1, spine1), &Value::Neutral(head2, spine2)) => {
            let term1 = read_back_neutral(level, *head1, spine1)?;
            let term2 = read_back_neutral(level, *head2, spine2)?;

            Ok(term1 == term2)
        },
        (&Value::LiteralType(literal_ty1), &Value::LiteralType(literal_ty2)) => {
            Ok(literal_ty1 == literal_ty2)
        },
        (
            &Value::FunType(app_mode1, param_ty1, body_ty1),
            &Value::FunType(app_mode2, param_ty2, body_ty2),
        ) if app_mode1 == app_mode2 => {
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
