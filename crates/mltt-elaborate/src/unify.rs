//! Unification of values.

use language_reporting::{Diagnostic, Label as DiagnosticLabel};
use mltt_core::literal::{LiteralIntro, LiteralType};
use mltt_core::{domain, global, meta, prim, syntax, var, AppMode};
use mltt_span::FileSpan;
use std::rc::Rc;

use crate::nbe;

/// Check that all entries in a spine are bound variables.
fn check_spine(
    globals: &global::Env,
    prims: &prim::Env,
    metas: &meta::Env,
    span: FileSpan,
    spine: &domain::Spine,
) -> Result<im::Vector<var::Level>, Diagnostic<FileSpan>> {
    spine
        .iter()
        .map(|elim| {
            if let domain::Elim::Fun(_, arg) = elim {
                if let domain::Value::Neutral(domain::Head::Var(var_level), spine) =
                    nbe::force_value(globals, prims, metas, span, arg)?.as_ref()
                {
                    if spine.is_empty() {
                        return Ok(*var_level);
                    }
                }
            }

            // TODO: is this a bug?
            // FIXME: really confusing error?
            Err(Diagnostic::new_error("non-variable in meta spine")
                .with_label(DiagnosticLabel::new_primary(span)))
        })
        .collect()
}

/// Scope check + occurs check a solution candidate.
fn check_solution(
    env_size: var::Size,
    span: FileSpan,
    head: meta::Index,
    bound_levels: &im::Vector<var::Level>,
    rhs: &Rc<syntax::Term>,
) -> Result<(), Diagnostic<FileSpan>> {
    match rhs.as_ref() {
        // Scope check
        syntax::Term::Var(rhs_var_index) => {
            if bound_levels
                .iter()
                .any(|var_level| env_size.index(*var_level) == *rhs_var_index)
            {
                // FIXME: Better error message
                let message = format!("solution scope error: `?{}`", head.0);
                Err(Diagnostic::new_error(message).with_label(DiagnosticLabel::new_primary(span)))
            } else {
                Ok(())
            }
        },
        // Occurs check
        syntax::Term::Meta(rhs_meta_level) => {
            if *rhs_meta_level == head {
                // FIXME: Better error message
                let message = format!("occurs check: `?{}`", head.0);
                Err(Diagnostic::new_error(message).with_label(DiagnosticLabel::new_primary(span)))
            } else {
                Ok(())
            }
        },
        syntax::Term::Global(_) => Ok(()),
        syntax::Term::Prim(_) => Ok(()),

        syntax::Term::Ann(term, term_ty) => {
            check_solution(env_size, span, head, bound_levels, term)?;
            check_solution(env_size, span, head, bound_levels, term_ty)?;

            Ok(())
        },
        syntax::Term::Let(_, _) => Err(Diagnostic::new_bug("attempted to unify let expressions")
            .with_label(DiagnosticLabel::new_primary(span))),

        syntax::Term::LiteralType(_) => Ok(()),
        syntax::Term::LiteralIntro(_) => Ok(()),
        syntax::Term::LiteralElim(scrutinee, clauses, default_clause) => {
            check_solution(env_size, span, head, bound_levels, scrutinee)?;
            for (_, body) in clauses.iter() {
                check_solution(env_size, span, head, bound_levels, body)?;
            }
            check_solution(env_size, span, head, bound_levels, default_clause)?;
            Ok(())
        },

        syntax::Term::FunType(_, _, param_ty, body_ty) => {
            check_solution(env_size, span, head, bound_levels, param_ty)?;
            check_solution(env_size + 1, span, head, bound_levels, body_ty)?;
            Ok(())
        },
        syntax::Term::FunIntro(_, _, body) => {
            check_solution(env_size + 1, span, head, bound_levels, body)?;
            Ok(())
        },
        syntax::Term::FunElim(fun, _, arg) => {
            check_solution(env_size, span, head, bound_levels, fun)?;
            check_solution(env_size, span, head, bound_levels, arg)?;
            Ok(())
        },

        syntax::Term::RecordType(ty_fields) => {
            for (i, (_, _, _, term)) in ty_fields.iter().enumerate() {
                check_solution(env_size + i as u32, span, head, bound_levels, term)?;
            }
            Ok(())
        },
        syntax::Term::RecordIntro(intro_fields) => {
            for (_, term) in intro_fields.iter() {
                check_solution(env_size, span, head, bound_levels, term)?;
            }
            Ok(())
        },
        syntax::Term::RecordElim(record, _) => {
            check_solution(env_size, span, head, bound_levels, record)
        },

        syntax::Term::Universe(_) => Ok(()),
    }
}

/// Solve metavariables in the case where a metavariable has been found in a
/// head position.
fn solve_neutral(
    globals: &global::Env,
    prims: &prim::Env,
    metas: &mut meta::Env,
    values: &var::Env<Rc<domain::Value>>,
    span: FileSpan,
    head: meta::Index,
    spine: &domain::Spine,
    rhs: &Rc<domain::Value>,
) -> Result<(), Diagnostic<FileSpan>> {
    let bound_levels = check_spine(globals, prims, metas, span, spine)?;
    let rhs = nbe::read_back_value(globals, prims, metas, values.size(), None, rhs)?;

    check_solution(values.size(), span, head, &bound_levels, &rhs)?;

    let rhs = bound_levels.iter().rev().fold(rhs, |acc, _| {
        Rc::from(syntax::Term::FunIntro(AppMode::Explicit, None, acc))
    });

    let rhs_value = nbe::eval_term(globals, prims, metas, &var::Env::new(), None, &rhs)?;

    metas.add_solved(head, rhs_value);

    Ok(())
}

/// Unify two values. If unification succeeds, the `value1` should be
/// definitionally equal to, or a subtype of of `value2` in the updated
/// metavariable environment.
pub fn unify_values(
    globals: &global::Env,
    prims: &prim::Env,
    metas: &mut meta::Env,
    values: &var::Env<Rc<domain::Value>>,
    span: FileSpan,
    value1: &Rc<domain::Value>,
    value2: &Rc<domain::Value>,
) -> Result<(), Diagnostic<FileSpan>> {
    log::trace!("unifying values");

    fn instantiate_value(
        values: &var::Env<Rc<domain::Value>>,
    ) -> (Rc<domain::Value>, var::Env<Rc<domain::Value>>) {
        let mut values = values.clone();
        let value = Rc::from(domain::Value::var(values.size().next_level()));
        values.add_entry(value.clone());
        (value, values)
    }

    fn unification_error(
        span: FileSpan,
        _value1: &Rc<domain::Value>,
        _value2: &Rc<domain::Value>,
    ) -> Result<(), Diagnostic<FileSpan>> {
        // FIXME: Better error message
        Err(Diagnostic::new_error("can't unify").with_label(DiagnosticLabel::new_primary(span)))
    }

    match (
        nbe::force_value(globals, prims, metas, span, value1)?.as_ref(),
        nbe::force_value(globals, prims, metas, span, value2)?.as_ref(),
    ) {
        (domain::Value::Neutral(head1, spine1), domain::Value::Neutral(head2, spine2))
            if head1 == head2 && spine1.len() == spine2.len() =>
        {
            for (elim1, elim2) in Iterator::zip(spine1.iter(), spine2.iter()) {
                match (elim1, elim2) {
                    (domain::Elim::Fun(app_mode1, arg1), domain::Elim::Fun(app_mode2, arg2))
                        if app_mode1 == app_mode2 =>
                    {
                        unify_values(globals, prims, metas, values, span, arg1, arg2)?;
                    }
                    (domain::Elim::Record(l1), domain::Elim::Record(l2)) if l1 == l2 => {},
                    (domain::Elim::Literal(lc1), domain::Elim::Literal(lc2)) => {
                        // Hum, guessing here??
                        let (sc, values) = instantiate_value(values);
                        let lc1 = lc1.clone();
                        let lc2 = lc2.clone();
                        let val1 = nbe::eval_literal_elim(globals, prims, metas, sc.clone(), lc1)?;
                        let val2 = nbe::eval_literal_elim(globals, prims, metas, sc.clone(), lc2)?;
                        unify_values(globals, prims, metas, &values, span, &val1, &val2)?;
                    },
                    (_, _) => unification_error(span, value1, value2)?,
                }
            }
            Ok(())
        }
        (domain::Value::Neutral(domain::Head::Meta(meta_level), spine), _) => solve_neutral(
            globals,
            prims,
            metas,
            values,
            span,
            *meta_level,
            spine,
            value2,
        ),
        (_, domain::Value::Neutral(domain::Head::Meta(meta_level), spine)) => solve_neutral(
            globals,
            prims,
            metas,
            values,
            span,
            *meta_level,
            spine,
            value1,
        ),

        (
            domain::Value::LiteralIntro(literal_intro1),
            domain::Value::LiteralIntro(literal_intro2),
        ) if LiteralIntro::alpha_eq(literal_intro1, literal_intro2) => Ok(()),
        (domain::Value::LiteralType(literal_ty1), domain::Value::LiteralType(literal_ty2))
            if LiteralType::alpha_eq(literal_ty1, literal_ty2) =>
        {
            Ok(())
        },

        (
            domain::Value::FunType(app_mode1, _, param_ty1, body_ty1),
            domain::Value::FunType(app_mode2, _, param_ty2, body_ty2),
        ) if app_mode1 == app_mode2 => {
            unify_values(globals, prims, metas, values, span, param_ty1, param_ty2)?;

            let (param, values) = instantiate_value(values);
            let body_ty1 = nbe::app_closure(globals, prims, metas, body_ty1, param.clone())?;
            let body_ty2 = nbe::app_closure(globals, prims, metas, body_ty2, param.clone())?;

            unify_values(globals, prims, metas, &values, span, &body_ty1, &body_ty2)?;

            Ok(())
        },
        (
            domain::Value::FunIntro(app_mode1, _, body1),
            domain::Value::FunIntro(app_mode2, _, body2),
        ) if app_mode1 == app_mode2 => {
            let (param, values) = instantiate_value(values);
            let body1 = nbe::app_closure(globals, prims, metas, body1, param.clone())?;
            let body2 = nbe::app_closure(globals, prims, metas, body2, param.clone())?;

            unify_values(globals, prims, metas, &values, span, &body1, &body2)?;

            Ok(())
        },

        // Eta conversion (η-conversion) for functions:
        //
        // ```text
        // (fun x => f x) == f
        // ```
        //
        // # Resources
        //
        // - https://ncatlab.org/nlab/show/eta-conversion
        // - https://en.wikipedia.org/wiki/Lambda_calculus#%CE%B7-conversion
        (domain::Value::FunIntro(app_mode1, _, body1), _) => {
            let (param, values) = instantiate_value(values);
            let body1 = nbe::app_closure(globals, prims, metas, body1, param.clone())?;
            let body2 =
                nbe::eval_fun_elim(globals, prims, metas, value2.clone(), app_mode1, param)?;

            unify_values(globals, prims, metas, &values, span, &body1, &body2)?;

            Ok(())
        },
        (_, domain::Value::FunIntro(app_mode2, _, body2)) => {
            let (param, values) = instantiate_value(values);
            let body2 = nbe::app_closure(globals, prims, metas, body2, param.clone())?;
            let body1 =
                nbe::eval_fun_elim(globals, prims, metas, value1.clone(), app_mode2, param)?;

            unify_values(globals, prims, metas, &values, span, &body1, &body2)?;

            Ok(())
        },

        (
            domain::Value::RecordTypeExtend(_, label1, _, value_ty1, rest_ty1),
            domain::Value::RecordTypeExtend(_, label2, _, value_ty2, rest_ty2),
        ) if label1 == label2 => {
            unify_values(globals, prims, metas, values, span, value_ty1, value_ty2)?;

            let (value, values) = instantiate_value(values);
            let rest_ty1 = nbe::app_closure(globals, prims, metas, rest_ty1, value.clone())?;
            let rest_ty2 = nbe::app_closure(globals, prims, metas, rest_ty2, value.clone())?;

            unify_values(globals, prims, metas, &values, span, &rest_ty1, &rest_ty2)?;

            Ok(())
        },
        (domain::Value::RecordTypeEmpty, domain::Value::RecordTypeEmpty) => Ok(()),
        (domain::Value::RecordIntro(fields1), domain::Value::RecordIntro(fields2))
            if fields1.len() == fields2.len() =>
        {
            let mut values = values.clone();
            for ((label1, value1), (label2, value2)) in
                Iterator::zip(fields1.iter(), fields2.iter())
            {
                if label1 == label2 {
                    unify_values(globals, prims, metas, &values, span, value1, value2)?;
                    values.add_entry(Rc::from(domain::Value::var(values.size().next_level())));
                } else {
                    unification_error(span, value1, value2)?;
                }
            }
            Ok(())
        }

        // Eta conversion (η-conversion) for records:
        //
        // ```text
        // record { l1 =  r.l1, .. } == r
        // ```
        //
        // # Resources
        //
        // - https://ncatlab.org/nlab/show/eta-conversion
        // - https://en.wikipedia.org/wiki/Lambda_calculus#%CE%B7-conversion
        // - https://agda.readthedocs.io/en/latest/language/record-types.html#eta-expansion
        (domain::Value::RecordIntro(fields1), _) => {
            let mut values = values.clone();
            for (label1, value1) in fields1 {
                let value2 = nbe::eval_record_elim(value2.clone(), label1)?;
                unify_values(globals, prims, metas, &values, span, value1, &value2)?;
                values.add_entry(Rc::from(domain::Value::var(values.size().next_level())));
            }
            Ok(())
        },
        (_, domain::Value::RecordIntro(fields2)) => {
            let mut values = values.clone();
            for (label2, value2) in fields2 {
                let value1 = nbe::eval_record_elim(value1.clone(), label2)?;
                unify_values(globals, prims, metas, &values, span, &value1, value2)?;
                values.add_entry(Rc::from(domain::Value::var(values.size().next_level())));
            }
            Ok(())
        },

        (domain::Value::Universe(level1), domain::Value::Universe(level2)) if level1 <= level2 => {
            Ok(())
        },

        (_, _) => unification_error(span, value1, value2),
    }
}
