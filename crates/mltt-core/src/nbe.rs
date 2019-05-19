//! Normalization by evaluation.
//!
//! Here we implement a full normalization algorithm by first implementing
//! evaluation to `Value`s in weak-head-normal-form, and then reading it back
//! `Normal` terms.

use std::rc::Rc;

use crate::domain::{AppClosure, Elim, Head, LiteralClosure, RcType, RcValue, Spine, Value};
use crate::syntax::{Item, RcTerm, Term};
use crate::{meta, prim, var, AppMode, Label};

/// Evaluate a primitive.
pub fn eval_prim<'spine>(
    prims: &prim::Env,
    prim_name: &prim::Name,
    spine: &'spine [Elim],
) -> Result<(RcValue, &'spine [Elim]), String> {
    let prim = prims
        .lookup_entry(prim_name)
        .ok_or_else(|| format!("eval: primitive not found: {:?}", prim_name))?;

    match prim.interpret(spine) {
        Some(result) => result,
        None => Ok((RcValue::prim(prim_name.clone()), spine)),
    }
}

/// Evaluate an eliminator.
pub fn eval_elim(
    prims: &prim::Env,
    metas: &meta::Env,
    head: RcValue,
    elim: &Elim,
) -> Result<RcValue, String> {
    match elim {
        Elim::Literal(closure) => eval_literal_elim(prims, metas, head, closure.clone()),
        Elim::Fun(app_mode, arg) => eval_fun_elim(prims, metas, head, app_mode, arg.clone()),
        Elim::Record(label) => eval_record_elim(head, label),
    }
}

/// Case split on a literal.
pub fn eval_literal_elim(
    prims: &prim::Env,
    metas: &meta::Env,
    scrutinee: RcValue,
    closure: LiteralClosure,
) -> Result<RcValue, String> {
    match scrutinee.as_ref() {
        Value::LiteralIntro(literal_intro) => {
            let index = closure.clauses.binary_search_by(|(l, _)| {
                l.partial_cmp(literal_intro).unwrap() // NaN?
            });

            let clause_body = match index {
                Ok(index) => &closure.clauses.get(index).unwrap().1,
                Err(_) => &closure.default,
            };
            eval_term(prims, metas, &closure.values, clause_body)
        },
        Value::Neutral(head, spine) => {
            let mut spine = spine.clone();
            spine.push(Elim::Literal(closure));
            Ok(RcValue::from(Value::Neutral(head.clone(), spine)))
        },
        _ => Err("eval_literal_elim: not a literal".to_owned()),
    }
}

/// Return the field in from a record.
pub fn eval_record_elim(record: RcValue, label: &Label) -> Result<RcValue, String> {
    match record.as_ref() {
        Value::RecordIntro(fields) => match fields.iter().find(|(l, _)| l == label) {
            Some((_, term)) => Ok(term.clone()),
            None => Err(format!(
                "eval_record_elim: field `{}` not found in record",
                label.0,
            )),
        },
        Value::Neutral(head, spine) => {
            let mut spine = spine.clone();
            spine.push(Elim::Record(label.clone()));
            // TODO: If head is `primitive`, and arity == number of initial spine apps in NF
            Ok(RcValue::from(Value::Neutral(head.clone(), spine)))
        },
        _ => Err("eval_record_elim: not a record".to_owned()),
    }
}

/// Apply a function to an argument.
pub fn eval_fun_elim(
    prims: &prim::Env,
    metas: &meta::Env,
    fun: RcValue,
    app_mode: &AppMode,
    arg: RcValue,
) -> Result<RcValue, String> {
    match fun.as_ref() {
        Value::FunIntro(fun_app_mode, _, body) => {
            if fun_app_mode == app_mode {
                app_closure(prims, metas, body, arg)
            } else {
                Err(format!(
                    "eval_ap: unexpected application mode - {:?} != {:?}",
                    fun_app_mode, app_mode,
                ))
            }
        },
        Value::Neutral(head, spine) => {
            let mut spine = spine.clone();
            spine.push(Elim::Fun(app_mode.clone(), arg));
            // TODO: If head is `primitive`, and arity == number of initial spine apps in NF
            Ok(RcValue::from(Value::Neutral(head.clone(), spine)))
        },
        _ => Err("eval_ap: not a function".to_owned()),
    }
}

/// Apply a closure to an argument.
pub fn app_closure(
    prims: &prim::Env,
    metas: &meta::Env,
    closure: &AppClosure,
    arg: RcValue,
) -> Result<RcValue, String> {
    let mut values = closure.values.clone();
    values.add_entry(arg);
    eval_term(prims, metas, &values, &closure.term)
}

/// Instantiate a closure in an environment of the given size.
pub fn inst_closure(
    prims: &prim::Env,
    metas: &meta::Env,
    size: var::Size,
    closure: &AppClosure,
) -> Result<RcValue, String> {
    app_closure(prims, metas, closure, RcValue::var(size.next_level()))
}

/// Evaluate a term in the environment that corresponds to the context in which
/// the term was typed.
pub fn eval_term(
    prims: &prim::Env,
    metas: &meta::Env,
    values: &var::Env<RcValue>,
    term: &RcTerm,
) -> Result<RcValue, String> {
    match term.as_ref() {
        Term::Var(var_index) => match values.lookup_entry(*var_index) {
            Some(value) => Ok(value.clone()),
            None => Err("eval: variable not found".to_owned()),
        },
        Term::Meta(meta_level) => match metas.lookup_solution(*meta_level) {
            Some((_, meta::Solution::Solved(value), _)) => Ok(value.clone()),
            Some((_, meta::Solution::Unsolved, _)) => Ok(RcValue::meta(*meta_level)),
            None => Err("eval: metavariable not found".to_owned()),
        },
        Term::Prim(prim_name) => Ok(eval_prim(prims, prim_name, &[])?.0),

        Term::Ann(term, _) => eval_term(prims, metas, values, term),
        Term::Let(items, body) => {
            let mut values = values.clone();
            for item in items {
                if let Item::Definition(_, _, term) = item {
                    values.add_entry(eval_term(prims, metas, &values, term)?);
                }
            }
            eval_term(prims, metas, &values, body)
        },

        // Literals
        Term::LiteralType(literal_ty) => Ok(RcValue::literal_ty(literal_ty.clone())),
        Term::LiteralIntro(literal_intro) => Ok(RcValue::literal_intro(literal_intro.clone())),
        Term::LiteralElim(scrutinee, clauses, default_body) => {
            let scrutinee = eval_term(prims, metas, values, scrutinee)?;
            let closure =
                LiteralClosure::new(clauses.clone(), default_body.clone(), values.clone());

            eval_literal_elim(prims, metas, scrutinee, closure)
        },

        // Functions
        Term::FunType(app_mode, name_hint, param_ty, body_ty) => {
            let app_mode = app_mode.clone();
            let name_hint = name_hint.clone();
            let param_ty = eval_term(prims, metas, values, param_ty)?;
            let body_ty = AppClosure::new(body_ty.clone(), values.clone());

            Ok(RcValue::from(Value::FunType(
                app_mode, name_hint, param_ty, body_ty,
            )))
        },
        Term::FunIntro(app_mode, name_hint, body) => {
            let app_mode = app_mode.clone();
            let name_hint = name_hint.clone();
            let body = AppClosure::new(body.clone(), values.clone());

            Ok(RcValue::from(Value::FunIntro(app_mode, name_hint, body)))
        },
        Term::FunElim(fun, app_mode, arg) => {
            let fun = eval_term(prims, metas, values, fun)?;
            let arg = eval_term(prims, metas, values, arg)?;

            eval_fun_elim(prims, metas, fun, app_mode, arg)
        },

        // Records
        Term::RecordType(fields) => match fields.split_first() {
            None => Ok(RcValue::from(Value::RecordTypeEmpty)),
            Some(((doc, label, name_hint, ty), rest)) => {
                let doc = doc.clone();
                let label = label.clone();
                let name_hint = name_hint.clone();
                let ty = eval_term(prims, metas, values, ty)?;
                let rest_fields = rest.iter().cloned().collect(); // FIXME: Seems expensive?
                let rest =
                    AppClosure::new(RcTerm::from(Term::RecordType(rest_fields)), values.clone());

                Ok(RcValue::from(Value::RecordTypeExtend(
                    doc, label, name_hint, ty, rest,
                )))
            },
        },
        Term::RecordIntro(fields) => {
            let fields = fields
                .iter()
                .map(|(label, term)| Ok((label.clone(), eval_term(prims, metas, values, term)?)))
                .collect::<Result<_, String>>()?;

            Ok(RcValue::from(Value::RecordIntro(fields)))
        },
        Term::RecordElim(record, label) => {
            eval_record_elim(eval_term(prims, metas, values, record)?, label)
        },

        // Universes
        Term::Universe(level) => Ok(RcValue::universe(*level)),
    }
}

/// Read a value back into the core syntax, normalizing as required.
pub fn read_back_value(
    prims: &prim::Env,
    metas: &meta::Env,
    size: var::Size,
    term: &RcValue,
) -> Result<RcTerm, String> {
    match term.as_ref() {
        Value::Neutral(head, spine) => read_back_neutral(prims, metas, size, head, spine),

        // Literals
        Value::LiteralType(literal_ty) => Ok(RcTerm::literal_ty(literal_ty.clone())),
        Value::LiteralIntro(literal_intro) => Ok(RcTerm::literal_intro(literal_intro.clone())),

        // Functions
        Value::FunType(app_mode, name_hint, param_ty, body_ty) => {
            let app_mode = app_mode.clone();
            let name_hint = name_hint.clone();
            let body_ty = inst_closure(prims, metas, size, body_ty)?;
            let param_ty = read_back_value(prims, metas, size, param_ty)?;
            let body_ty = read_back_value(prims, metas, size + 1, &body_ty)?;

            Ok(RcTerm::from(Term::FunType(
                app_mode, name_hint, param_ty, body_ty,
            )))
        },
        Value::FunIntro(app_mode, name_hint, body) => {
            let app_mode = app_mode.clone();
            let name_hint = name_hint.clone();
            let body = inst_closure(prims, metas, size, body)?;
            let body = read_back_value(prims, metas, size + 1, &body)?;

            Ok(RcTerm::from(Term::FunIntro(app_mode, name_hint, body)))
        },

        // Records
        Value::RecordTypeExtend(doc, label, name_hint, term_ty, rest_ty) => {
            let mut size = size;

            let term_ty = read_back_value(prims, metas, size, term_ty)?;

            let mut rest_ty = inst_closure(prims, metas, size, rest_ty)?;
            let mut field_tys = vec![(doc.clone(), label.clone(), name_hint.clone(), term_ty)];

            while let Value::RecordTypeExtend(doc, label, name_hint, next_term_ty, next_rest_ty) =
                rest_ty.as_ref()
            {
                size += 1;
                let next_term_ty = read_back_value(prims, metas, size, next_term_ty)?;
                field_tys.push((doc.clone(), label.clone(), name_hint.clone(), next_term_ty));
                rest_ty = inst_closure(prims, metas, size, next_rest_ty)?;
            }

            Ok(RcTerm::from(Term::RecordType(field_tys)))
        },
        Value::RecordTypeEmpty => Ok(RcTerm::from(Term::RecordType(Vec::new()))),
        Value::RecordIntro(fields) => {
            let fields = fields
                .iter()
                .map(|(label, term)| {
                    Ok((label.clone(), read_back_value(prims, metas, size, term)?))
                })
                .collect::<Result<_, String>>()?;

            Ok(RcTerm::from(Term::RecordIntro(fields)))
        },

        // Universes
        Value::Universe(level) => Ok(RcTerm::universe(*level)),
    }
}

/// Read a neutral value back into the core syntax, normalizing as required.
pub fn read_back_neutral(
    prims: &prim::Env,
    metas: &meta::Env,
    size: var::Size,
    head: &Head,
    spine: &Spine,
) -> Result<RcTerm, String> {
    let (head, spine) = match head {
        Head::Var(var_level) => (RcTerm::var(size.index(*var_level)), &spine[..]),
        Head::Meta(meta_index) => (RcTerm::meta(*meta_index), &spine[..]),
        Head::Prim(prim_name) => {
            let (value, spine) = eval_prim(prims, prim_name, &spine)?;
            (read_back_value(prims, metas, size, &value)?, spine)
        },
    };

    spine.iter().fold(Ok(head), |acc, elim| match elim {
        Elim::Literal(closure) => {
            let clauses = Rc::from(
                closure
                    .clauses
                    .iter()
                    .map(|(literal_intro, body)| {
                        let body = eval_term(prims, metas, &closure.values, body)?;
                        let body = read_back_value(prims, metas, size, &body)?;
                        Ok((literal_intro.clone(), body))
                    })
                    .collect::<Result<Vec<_>, String>>()?,
            );
            let default_body = eval_term(prims, metas, &closure.values, &closure.default)?;
            let default_body = read_back_value(prims, metas, size, &default_body)?;

            Ok(RcTerm::from(Term::LiteralElim(acc?, clauses, default_body)))
        },
        Elim::Fun(app_mode, arg) => {
            let arg = read_back_value(prims, metas, size, &arg)?;

            Ok(RcTerm::from(Term::FunElim(acc?, app_mode.clone(), arg)))
        },
        Elim::Record(label) => Ok(RcTerm::from(Term::RecordElim(acc?, label.clone()))),
    })
}

/// Fully normalize a term by first evaluating it, then reading it back.
pub fn normalize_term(
    prims: &prim::Env,
    metas: &meta::Env,
    values: &var::Env<RcValue>,
    term: &RcTerm,
) -> Result<RcTerm, String> {
    let value = eval_term(prims, metas, values, term)?;
    read_back_value(prims, metas, values.size(), &value)
}

/// Evaluate a value further, if it's now possible due to updates made to the
/// metavariable solutions.
pub fn force_value(
    prims: &prim::Env,
    metas: &meta::Env,
    value: &RcValue,
) -> Result<RcValue, String> {
    match value.as_ref() {
        Value::Neutral(Head::Meta(meta_level), spine) => match metas.lookup_solution(*meta_level) {
            Some((_, meta::Solution::Solved(value), _)) => {
                let value = spine.iter().fold(Ok(value.clone()), |head, elim| {
                    eval_elim(prims, metas, head?, elim)
                })?;
                force_value(prims, metas, &value)
            },
            Some((_, meta::Solution::Unsolved, _)) | None => Ok(value.clone()),
        },
        _ => Ok(value.clone()),
    }
}

/// Check whether a semantic type is a subtype of another.
pub fn check_subtype(
    prims: &prim::Env,
    metas: &meta::Env,
    size: var::Size,
    ty1: &RcType,
    ty2: &RcType,
) -> Result<bool, String> {
    match (
        force_value(prims, metas, ty1)?.as_ref(),
        force_value(prims, metas, ty2)?.as_ref(),
    ) {
        (Value::Neutral(head1, spine1), Value::Neutral(head2, spine2)) => {
            let term1 = read_back_neutral(prims, metas, size, head1, spine1)?;
            let term2 = read_back_neutral(prims, metas, size, head2, spine2)?;

            Ok(Term::alpha_eq(&term1, &term2))
        },
        (Value::LiteralType(literal_ty1), Value::LiteralType(literal_ty2)) => {
            Ok(literal_ty1 == literal_ty2)
        },
        (
            Value::FunType(app_mode1, _, param_ty1, body_ty1),
            Value::FunType(app_mode2, _, param_ty2, body_ty2),
        ) if app_mode1 == app_mode2 => Ok(check_subtype(prims, metas, size, param_ty2, param_ty1)?
            && {
                let body_ty1 = inst_closure(prims, metas, size, body_ty1)?;
                let body_ty2 = inst_closure(prims, metas, size, body_ty2)?;
                check_subtype(prims, metas, size + 1, &body_ty1, &body_ty2)?
            }),
        (
            Value::RecordTypeExtend(_, label1, _, term_ty1, rest_ty1),
            Value::RecordTypeExtend(_, label2, _, term_ty2, rest_ty2),
        ) if label1 == label2 => Ok(check_subtype(prims, metas, size, term_ty1, term_ty2)? && {
            let rest_ty1 = inst_closure(prims, metas, size, rest_ty1)?;
            let rest_ty2 = inst_closure(prims, metas, size, rest_ty2)?;
            check_subtype(prims, metas, size + 1, &rest_ty1, &rest_ty2)?
        }),
        (Value::RecordTypeEmpty, Value::RecordTypeEmpty) => Ok(true),
        (Value::Universe(level1), Value::Universe(level2)) => Ok(level1 <= level2),
        _ => Ok(false),
    }
}
