//! Elaboration of lists clauses to case trees.

use language_reporting::{Diagnostic, Label as DiagnosticLabel};
use mltt_concrete::{IntroParam, LiteralKind, Pattern, SpannedString, Term};
use mltt_core::literal::LiteralIntro;
use mltt_core::{domain, meta, syntax, AppMode, DocString};
use mltt_span::FileSpan;
use std::rc::Rc;

use super::{check_term, literal, synth_term, synth_universe, Context, MetaInsertion};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Top-level Implementation
////////////////////////////////////////////////////////////////////////////////////////////////////

/// The state of a pattern clause, part-way through evaluation
pub struct Clause<'file> {
    /// The parameters that are still waiting to be elaborated
    params: &'file [IntroParam<'file>],
    /// The expected body type for this clause
    body_ty: Option<&'file Term<'file>>,
    /// The concrete body of this clause
    body: &'file Term<'file>,
}

impl<'file> Clause<'file> {
    pub fn new(
        params: &'file [IntroParam<'file>],
        body_ty: Option<&'file Term<'file>>,
        body: &'file Term<'file>,
    ) -> Clause<'file> {
        Clause {
            params,
            body_ty,
            body,
        }
    }
}

/// Check that a given clause conforms to an expected type, and elaborates
/// it into a case tree.
///
/// Returns the elaborated term.
pub fn check_clause(
    context: &Context,
    metas: &mut meta::Env,
    mut clause: Clause<'_>,
    expected_ty: &Rc<domain::Type>,
) -> Result<Rc<syntax::Term>, Diagnostic<FileSpan>> {
    let mut context = context.clone();
    let mut params = Vec::new();
    let mut expected_ty = expected_ty.clone();

    while let (Some((app_mode, param_ty, next_body_ty)), Some((head_param, rest_params))) = (
        next_expected_param(&expected_ty),
        clause.params.split_first(),
    ) {
        let (param_var, name_hint) = match check_param_app_mode(head_param, &app_mode)? {
            CheckedPattern::Var(None) => (context.add_fresh_param(param_ty), None),
            CheckedPattern::Var(Some(var_name)) => {
                clause.params = rest_params;
                (
                    context.add_param(var_name, param_ty),
                    Some(var_name.to_string()),
                )
            },
            CheckedPattern::LiteralIntro(_, literal) => {
                return Err(Diagnostic::new_error("non-exhaustive patterns").with_label(
                    DiagnosticLabel::new_primary(literal.span())
                        .with_message("use a case expression for matching on literals"),
                ));
            },
        };

        params.push((app_mode, name_hint));
        expected_ty = context.app_closure(metas, next_body_ty, param_var)?;
    }

    let body = check_clause_body(&context, metas, &clause, &expected_ty)?;

    Ok(done(Vec::new(), params, body))
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
    metas: &mut meta::Env,
    span: FileSpan,
    scrutinee: &Term<'file>,
    clauses: Vec<CaseClause<'file>>,
    expected_ty: &Rc<domain::Type>,
) -> Result<Rc<syntax::Term>, Diagnostic<FileSpan>> {
    // TODO: Merge with `check_clause`
    // TODO: Zero or more scrutinees
    // TODO: One-or-more patterns per case clause

    match clauses.split_last() {
        None => Err(Diagnostic::new_error("non-exhaustive patterns").with_label(
            DiagnosticLabel::new_primary(span).with_message("empty patterns are not yet supported"),
        )),
        Some((default_clause, literal_clauses)) => {
            let mut context = context.clone();

            let (checked_scrutinee, (param_level, param_ty)) = {
                let scrutinee_level = context.values().size().next_level();
                let (scrutinee_term, scrutinee_ty) =
                    synth_term(MetaInsertion::Yes, &context, metas, scrutinee)?;
                let scrutinee_value =
                    context.eval_term(metas, scrutinee.span(), &scrutinee_term)?;
                context.add_fresh_defn(scrutinee_value, scrutinee_ty.clone());

                ((scrutinee_term, None), (scrutinee_level, scrutinee_ty))
            };

            let mut literal_branches =
                Vec::<(LiteralIntro, Rc<syntax::Term>)>::with_capacity(literal_clauses.len());

            for literal_clause in literal_clauses {
                match literal_clause.pattern {
                    Pattern::LiteralIntro(kind, literal) => {
                        let literal_intro =
                            literal::check(&context, metas, *kind, literal, &param_ty)?;
                        let body = check_term(&context, metas, &literal_clause.body, expected_ty)?;

                        match literal_branches
                            .binary_search_by(|(l, _)| l.partial_cmp(&literal_intro).unwrap()) // NaN?
                        {
                            Ok(_) => {}, // TODO: Warn about duplicated patterns?
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

            let default_body = match default_clause.pattern {
                Pattern::Var(name) => {
                    let mut context = context.clone();
                    context.add_name(name, param_level);
                    check_term(&context, metas, &default_clause.body, expected_ty)?
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

            let body = Rc::from(syntax::Term::LiteralElim(
                Rc::from(syntax::Term::var(
                    context.values().size().index(param_level),
                )),
                Rc::from(literal_branches),
                default_body,
            ));

            Ok(done(vec![checked_scrutinee], Vec::new(), body))
        },
    }
}

/// Synthesize the type of the clauses, elaborating them into a case tree.
///
/// Returns the elaborated term and its synthesized type.
pub fn synth_clause(
    context: &Context,
    metas: &mut meta::Env,
    clause: Clause<'_>,
) -> Result<(Rc<syntax::Term>, Rc<domain::Type>), Diagnostic<FileSpan>> {
    if let Some(param) = clause.params.first() {
        // TODO: We will be able to type this once we have annotated patterns!
        return Err(
            Diagnostic::new_error("unable to infer the type of parameter")
                .with_label(DiagnosticLabel::new_primary(param.span())),
        );
    }

    synth_clause_body(&context, metas, &clause)
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper functions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Get the next expected parameter
fn next_expected_param<'ty>(
    expected_ty: &'ty Rc<domain::Type>,
) -> Option<(AppMode, Rc<domain::Value>, &'ty domain::AppClosure)> {
    match expected_ty.as_ref() {
        domain::Value::FunType(app_mode, _, param_ty, body_ty) => {
            Some((app_mode.clone(), param_ty.clone(), body_ty))
        },
        _ => None,
    }
}

enum CheckedPattern<'file> {
    Var(Option<SpannedString<'file>>),
    LiteralIntro(LiteralKind, SpannedString<'file>),
}

impl<'file> From<&Pattern<'file>> for CheckedPattern<'file> {
    fn from(src: &Pattern<'file>) -> CheckedPattern<'file> {
        match src {
            Pattern::Var(name) => CheckedPattern::Var(Some(name.clone())),
            Pattern::LiteralIntro(kind, src) => CheckedPattern::LiteralIntro(*kind, src.clone()),
        }
    }
}

/// Check that a given parameter matches the expected application mode, and
/// return the pattern inside it.
fn check_param_app_mode<'param, 'file>(
    param: &'param IntroParam<'file>,
    expected_app_mode: &AppMode,
) -> Result<CheckedPattern<'file>, Diagnostic<FileSpan>> {
    match (param, expected_app_mode) {
        (IntroParam::Explicit(pattern), AppMode::Explicit) => Ok(CheckedPattern::from(pattern)),
        (IntroParam::Implicit(_, intro_label, pattern), AppMode::Implicit(ty_label))
        | (IntroParam::Instance(_, intro_label, pattern), AppMode::Instance(ty_label))
            if intro_label.slice == ty_label.0 =>
        {
            match pattern {
                None => Ok(CheckedPattern::Var(Some(intro_label.clone()))),
                Some(pattern) => Ok(CheckedPattern::from(pattern)),
            }
        },
        (_, AppMode::Implicit(_)) | (_, AppMode::Instance(_)) => Ok(CheckedPattern::Var(None)),
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
    metas: &mut meta::Env,
    clause: &Clause<'_>,
    expected_body_ty: &Rc<domain::Type>,
) -> Result<Rc<syntax::Term>, Diagnostic<FileSpan>> {
    match clause.body_ty {
        None => check_term(&context, metas, clause.body, &expected_body_ty),
        Some(body_ty) => {
            let body_ty_span = body_ty.span();
            let (body_ty, _) = synth_universe(&context, metas, body_ty)?;
            let body_ty_value = context.eval_term(metas, body_ty_span, &body_ty)?;
            let body = check_term(&context, metas, clause.body, &body_ty_value)?;
            // TODO: Ensure that this is respecting variance correctly!
            context.unify_values(metas, clause.body.span(), &body_ty_value, &expected_body_ty)?;

            Ok(Rc::from(syntax::Term::ann(body, body_ty)))
        },
    }
}

/// Synthesize the type of the body of a clause, and elaborate it.
fn synth_clause_body(
    context: &Context,
    metas: &mut meta::Env,
    clause: &Clause<'_>,
) -> Result<(Rc<syntax::Term>, Rc<domain::Type>), Diagnostic<FileSpan>> {
    match clause.body_ty {
        None => synth_term(MetaInsertion::Yes, context, metas, clause.body),
        Some(body_ty) => {
            let body_ty_span = body_ty.span();
            let (body_ty, _) = synth_universe(context, metas, body_ty)?;
            let body_ty_value = context.eval_term(metas, body_ty_span, &body_ty)?;
            let body = check_term(context, metas, clause.body, &body_ty_value)?;

            Ok((Rc::from(syntax::Term::ann(body, body_ty)), body_ty_value))
        },
    }
}

/// Finish elaborating the patterns into a case tree.
fn done(
    scrutinees: Vec<(Rc<syntax::Term>, Option<Rc<syntax::Term>>)>,
    params: Vec<(AppMode, Option<String>)>,
    body: Rc<syntax::Term>,
) -> Rc<syntax::Term> {
    let items = scrutinees
        .into_iter()
        .map(|(scrutinee, scrutinee_ty)| {
            syntax::Item::Definition(
                DocString::from(""),
                None,
                None,
                match scrutinee_ty {
                    None => scrutinee,
                    Some(scrutinee_ty) => Rc::from(syntax::Term::ann(scrutinee, scrutinee_ty)),
                },
            )
        })
        .collect::<Vec<_>>();

    let body = params
        .into_iter()
        .rev()
        .fold(body, |acc, (app_mode, name_hint)| {
            Rc::from(syntax::Term::FunIntro(app_mode, name_hint, acc))
        });

    if items.is_empty() {
        body
    } else {
        Rc::from(syntax::Term::Let(items, body))
    }
}
