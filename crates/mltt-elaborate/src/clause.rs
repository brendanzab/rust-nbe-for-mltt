//! Elaboration of lists clauses to case trees.

use language_reporting::{Diagnostic, Label as DiagnosticLabel};
use mltt_concrete::{IntroParam, Pattern, Term};
use mltt_core::syntax::{core, domain, AppMode, LiteralIntro};
use mltt_span::FileSpan;
use std::borrow::Cow;
use std::rc::Rc;

use super::{check_term, do_closure_app, literal, synth_term, synth_universe, Context};

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

    while let (Some((app_mode, param_ty, next_body_ty)), Some((head_param, rest_params))) = (
        next_expected_param(&expected_ty),
        clause.concrete_params.split_first(),
    ) {
        let var_name = match check_param_app_mode(head_param, &app_mode)? {
            None => None,
            Some(pattern) => {
                clause.concrete_params = rest_params;
                match pattern.as_ref() {
                    Pattern::Var(var_name) => Some(var_name.to_string()),
                    Pattern::LiteralIntro(_, literal) => {
                        return Err(Diagnostic::new_error("non-exhaustive patterns").with_label(
                            DiagnosticLabel::new_primary(literal.span())
                                .with_message("use a case expression for matching on literals"),
                        ));
                    },
                }
            },
        };

        param_app_modes.push(app_mode);
        let param_var = context.local_bind(var_name, param_ty.clone());
        expected_ty = do_closure_app(context.prims(), next_body_ty, param_var)?;
    }

    let body = check_clause_body(&context, &clause, &expected_ty)?;

    Ok(done(param_app_modes, body))
}

/// The state of a pattern clause, part-way through evaluation
pub struct CaseClause<'file> {
    /// The pattern for this case clause
    pattern: &'file Pattern<'file>,
    /// The concrete body of this clause
    body: &'file Term<'file>,
}

impl<'file> CaseClause<'file> {
    pub fn new(pattern: &'file Pattern<'file>, body: &'file Term<'file>) -> CaseClause<'file> {
        CaseClause { pattern, body }
    }
}

/// Check that the given case clauses conform to the expected type, and
/// elaborate them into a case tree.
pub fn check_case<'file>(
    context: &Context,
    span: FileSpan,
    scrutinee: &Term<'file>,
    clauses: Vec<CaseClause<'file>>,
    expected_ty: &domain::RcType,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    // TODO: Merge with `check_clause`
    // TODO: Zero or more scrutinees
    // TODO: One-or-more patterns per case clause

    match clauses.split_last() {
        None => Err(Diagnostic::new_error("non-exhaustive patterns").with_label(
            DiagnosticLabel::new_primary(span).with_message("empty patterns are not yet supported"),
        )),
        Some((default_clause, literal_clauses)) => {
            let mut context = context.clone();

            let (scrutinee_term, scrutinee_ty) = synth_term(&context, scrutinee)?;
            let scrutinee_value = context.eval(scrutinee.span(), &scrutinee_term)?;
            let scrutinee_var = domain::RcValue::var(context.level());
            context.local_define(None, scrutinee_value, scrutinee_ty.clone());

            let mut literal_branches =
                Vec::<(LiteralIntro, core::RcTerm)>::with_capacity(literal_clauses.len());

            for literal_clause in literal_clauses {
                match literal_clause.pattern {
                    Pattern::LiteralIntro(kind, literal) => {
                        let literal_intro = literal::check(&context, *kind, literal, &scrutinee_ty)?;
                        let body = check_term(&context, &literal_clause.body, expected_ty)?;

                        match literal_branches
                            .binary_search_by(|(l, _)| l.partial_cmp(&literal_intro).unwrap()) // NaN?
                        {
                            Ok(index) => literal_branches.insert(index + 1, (literal_intro, body)),
                            Err(index) => literal_branches.insert(index, (literal_intro, body)),
                        }
                    },
                    _ => {
                        return Err(
                            Diagnostic::new_error("variable literal pattern").with_label(
                                DiagnosticLabel::new_primary(literal_clause.pattern.span())
                                    .with_message("literal pattern expected here"),
                            ),
                        );
                    },
                }
            }

            let default = match default_clause.pattern {
                Pattern::Var(name) => {
                    let mut context = context.clone();

                    let var_var = domain::RcValue::var(context.level());
                    context.local_define(name.to_string(), scrutinee_var.clone(), scrutinee_ty);
                    let body = check_term(&context, &default_clause.body, expected_ty)?;

                    core::RcTerm::from(core::Term::Let(context.read_back(None, &var_var)?, body))
                },
                _ => {
                    return Err(
                        Diagnostic::new_error("expected variable pattern").with_label(
                            DiagnosticLabel::new_primary(default_clause.pattern.span())
                                .with_message("default case expected here"),
                        ),
                    );
                },
            };

            Ok(core::RcTerm::from(core::Term::Let(
                scrutinee_term,
                core::RcTerm::from(core::Term::LiteralElim(
                    context.read_back(None, &scrutinee_var)?,
                    Rc::from(literal_branches),
                    default,
                )),
            )))
        },
    }
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

/// Get the next expected parameter
fn next_expected_param<'ty>(
    expected_ty: &'ty domain::RcType,
) -> Option<(AppMode, domain::RcValue, &'ty domain::AppClosure)> {
    match expected_ty.as_ref() {
        domain::Value::FunType(app_mode, param_ty, body_ty) => {
            Some((app_mode.clone(), param_ty.clone(), body_ty))
        },
        _ => None,
    }
}

/// Check that a given parameter matches the expected application mode, and
/// return the pattern inside it.
fn check_param_app_mode<'param, 'file>(
    param: &'param IntroParam<'file>,
    expected_app_mode: &AppMode,
) -> Result<Option<Cow<'param, Pattern<'file>>>, Diagnostic<FileSpan>> {
    match (param, expected_app_mode) {
        (IntroParam::Explicit(pattern), AppMode::Explicit) => Ok(Some(Cow::Borrowed(pattern))),
        (IntroParam::Implicit(_, intro_label, pattern), AppMode::Implicit(ty_label))
        | (IntroParam::Instance(_, intro_label, pattern), AppMode::Instance(ty_label))
            if intro_label.slice == ty_label.0 =>
        {
            match pattern {
                None => Ok(Some(Cow::Owned(Pattern::Var(intro_label.clone())))),
                Some(pattern) => Ok(Some(Cow::Borrowed(pattern))),
            }
        },
        (_, AppMode::Implicit(_)) | (_, AppMode::Instance(_)) => Ok(None),
        (IntroParam::Implicit(span, _, _), AppMode::Explicit)
        | (IntroParam::Instance(span, _, _), AppMode::Explicit) => {
            let message = "unexpected parameter pattern";
            Err(Diagnostic::new_error(message).with_label(
                DiagnosticLabel::new_primary(*span).with_message("this parameter is not needed"),
            ))
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
fn done(param_app_modes: Vec<AppMode>, body: core::RcTerm) -> core::RcTerm {
    param_app_modes
        .into_iter()
        .rev()
        .fold(body, |acc, app_mode| {
            core::RcTerm::from(core::Term::FunIntro(app_mode, acc))
        })
}
