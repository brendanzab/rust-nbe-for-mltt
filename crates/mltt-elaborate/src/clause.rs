//! Elaboration of lists clauses to case trees.

use language_reporting::{Diagnostic, Label as DiagnosticLabel};
use mltt_concrete::{IntroParam, Pattern, Term};
use mltt_core::syntax::{core, domain, AppMode};
use mltt_span::FileSpan;
use std::borrow::Cow;

use super::{check_term, do_closure_app, synth_term, synth_universe, Context};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Top-level Implementation
////////////////////////////////////////////////////////////////////////////////////////////////////

/// The state of a pattern clause, part-way through evaluation
pub struct Clause<'file> {
    /// The parameters that are still waiting to be elaborated
    concrete_params: &'file [IntroParam<'file>],
    /// The expected body type for this clause
    concrete_body_ty: Option<&'file Term<'file>>,
    /// The concrete body of this clause
    concrete_body: &'file Term<'file>,
}

impl<'file> Clause<'file> {
    pub fn new(
        concrete_params: &'file [IntroParam<'file>],
        concrete_body_ty: Option<&'file Term<'file>>,
        concrete_body: &'file Term<'file>,
    ) -> Clause<'file> {
        Clause {
            concrete_params,
            concrete_body_ty,
            concrete_body,
        }
    }
}

/// Check that a given clause conforms to an expected type, and elaborates
/// it into a case tree.
///
/// Returns the elaborated term.
pub fn check_clause(
    context: &Context,
    mut clause: Clause<'_>,
    expected_ty: &domain::RcType,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    let mut context = context.clone();
    let mut param_app_modes = Vec::new();
    let mut expected_ty = expected_ty.clone();

    while let Some((head_param, rest_params)) = clause.concrete_params.split_first() {
        clause.concrete_params = rest_params;

        loop {
            let (app_mode, param_ty, next_body_ty) =
                check_next_expected_param(&mut std::iter::empty(), &expected_ty)?;

            let pattern = check_param_app_mode(head_param, &app_mode)?;
            let var_name = match pattern.as_ref() {
                None => None,
                Some(pattern) => match pattern.as_ref() {
                    Pattern::Var(var_name) => Some(var_name.slice.to_owned()),
                },
            };

            param_app_modes.push(app_mode);
            let param_var = context.local_bind(var_name, param_ty.clone());
            if let Some(next_body_ty) = next_body_ty {
                expected_ty = do_closure_app(&next_body_ty, param_var)?;
            }

            if pattern.is_some() {
                break;
            }
        }
    }

    let body = check_clause_body(&context, &clause, &expected_ty)?;

    Ok(done(vec![], param_app_modes, body))
}

/// Synthesize the type of the clauses, elaborating them into a case tree.
///
/// Returns the elaborated term and its synthesized type.
pub fn synth_clause(
    context: &Context,
    clause: Clause<'_>,
) -> Result<(core::RcTerm, domain::RcType), Diagnostic<FileSpan>> {
    if let Some(param) = clause.concrete_params.first() {
        // TODO: We will be able to type this once we have annotated patterns!
        return Err(
            Diagnostic::new_error("unable to infer the type of parameter")
                .with_label(DiagnosticLabel::new_primary(param.span())),
        );
    }

    synth_clause_body(&context, &clause)
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper functions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Check that a given parameter matches the expected application mode, and
/// return the pattern inside it.
fn check_param_app_mode<'param, 'file>(
    param: &'param IntroParam<'file>,
    expected_app_mode: &AppMode,
) -> Result<Option<Cow<'param, Pattern<'file>>>, Diagnostic<FileSpan>> {
    match (param, expected_app_mode) {
        (IntroParam::Explicit(pattern), AppMode::Explicit) => Ok(Some(Cow::Borrowed(pattern))),
        (IntroParam::Implicit(_, intro_label, pattern), AppMode::Implicit(ty_label))
            if intro_label.slice == ty_label.0 =>
        {
            match pattern {
                None => Ok(Some(Cow::Owned(Pattern::Var(intro_label.clone())))),
                Some(pattern) => Ok(Some(Cow::Borrowed(pattern))),
            }
        },
        (_, AppMode::Implicit(_)) => Ok(None),
        (IntroParam::Implicit(span, _, _), AppMode::Explicit) => {
            let message = "unexpected implicit parameter pattern";
            Err(Diagnostic::new_error(message).with_label(
                DiagnosticLabel::new_primary(*span).with_message("this parameter is not needed"),
            ))
        },
    }
}

/// Get the next expected parameter, by checking, in order:
///
/// - the next type synthesized from the scrutinees (if it exists)
/// - the next parameter from the expected type (if it exists)
fn check_next_expected_param<'ty>(
    expected_scrutinee_param_tys: &mut impl Iterator<Item = domain::RcType>,
    expected_ty: &'ty domain::RcType,
) -> Result<(AppMode, domain::RcValue, Option<&'ty domain::AppClosure>), Diagnostic<FileSpan>> {
    match expected_scrutinee_param_tys.next() {
        Some(param_ty) => Ok((AppMode::Explicit, param_ty, None)),
        None => match expected_ty.as_ref() {
            domain::Value::FunType(app_mode, param_ty, body_ty) => {
                Ok((app_mode.clone(), param_ty.clone(), Some(body_ty)))
            },
            _ => unimplemented!("too many patterns given"),
            // _ => Err(
            //     Diagnostic::new_error("too many parameters provided").with_label(
            //         DiagnosticLabel::new_primary(head_param_span)
            //             .with_message("try removing this parameter"),
            //     ),
            // ),
        },
    }
}

/// Check that the body of the given clause conforms to they expected type, and
/// elaborate it.
fn check_clause_body(
    context: &Context,
    clause: &Clause<'_>,
    expected_body_ty: &domain::RcType,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    match clause.concrete_body_ty {
        None => check_term(&context, clause.concrete_body, &expected_body_ty),
        Some(concrete_body_ty) => {
            let (body_ty, _) = synth_universe(&context, concrete_body_ty)?;
            let body_ty = context.eval(concrete_body_ty.span(), &body_ty)?;
            let body = check_term(&context, clause.concrete_body, &body_ty)?;
            // TODO: Ensure that this is respecting variance correctly!
            context.expect_subtype(clause.concrete_body.span(), &body_ty, &expected_body_ty)?;
            Ok(body)
        },
    }
}

/// Synthesize the type of the body of a clause, and elaborate it.
fn synth_clause_body(
    context: &Context,
    clause: &Clause<'_>,
) -> Result<(core::RcTerm, domain::RcType), Diagnostic<FileSpan>> {
    match clause.concrete_body_ty {
        None => synth_term(context, clause.concrete_body),
        Some(concrete_body_ty) => {
            let (body_ty, _) = synth_universe(context, concrete_body_ty)?;
            let body_ty = context.eval(concrete_body_ty.span(), &body_ty)?;
            let body = check_term(context, clause.concrete_body, &body_ty)?;
            Ok((body, body_ty))
        },
    }
}

/// Finish elaborating the patterns into a case tree.
fn done(
    args: Vec<core::RcTerm>,
    param_app_modes: Vec<AppMode>,
    body: core::RcTerm,
) -> core::RcTerm {
    let term = param_app_modes
        .into_iter()
        .rev()
        .fold(body, |acc, app_mode| {
            core::RcTerm::from(core::Term::FunIntro(app_mode, acc))
        });

    args.into_iter().fold(term, |acc, arg| {
        core::RcTerm::from(core::Term::FunElim(acc, AppMode::Explicit, arg))
    })
}
