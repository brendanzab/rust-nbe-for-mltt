//! Elaboration of lists clauses to case trees.

use language_reporting::{Diagnostic, Label as DiagnosticLabel};
use mltt_concrete::{IntroParam, Pattern, SpannedString, Term};
use mltt_core::literal::LiteralIntro;
use mltt_core::{domain, meta, syntax, var, AppMode, DocString};
use mltt_span::FileSpan;
use std::collections::VecDeque;
use std::rc::Rc;

use super::{check_term, literal, synth_term, synth_universe, Context, MetaInsertion};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Top-level Implementation
////////////////////////////////////////////////////////////////////////////////////////////////////

/// A pattern clause.
pub struct Clause<'file> {
    /// The parameters that are still waiting to be elaborated
    params: &'file [IntroParam<'file>],
    /// The patterns that have currently been discovered by comparing to the
    /// expected application mode (from the type).
    checked_patterns: VecDeque<CheckedPattern<'file>>,
    /// The variable binders we have traversed over.
    ///
    /// We'll add these to the context once we are ready to elaborate the body
    /// of the clause.
    binders: Vec<(Option<SpannedString<'file>>, ExpectedParam)>,
    /// The expected body type for this clause.
    body_ty: Option<&'file Term<'file>>,
    /// The concrete body of this clause.
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
            checked_patterns: VecDeque::new(),
            binders: Vec::new(),
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
    case_span: FileSpan,
    clause: Clause<'_>,
    expected_ty: &Rc<domain::Type>,
) -> Result<Rc<syntax::Term>, Diagnostic<FileSpan>> {
    check_clauses(context, metas, case_span, &[], vec![clause], expected_ty)
}

/// Synthesize the type of a clause, elaborating it into a case tree.
///
/// Returns the elaborated term and its synthesized type.
pub fn synth_clause(
    context: &Context,
    metas: &mut meta::Env,
    case_span: FileSpan,
    clause: Clause<'_>,
) -> Result<(Rc<syntax::Term>, Rc<domain::Type>), Diagnostic<FileSpan>> {
    synth_clauses(context, metas, case_span, &[], vec![clause])
}

/// Check that the given clauses conform to an expected type, and elaborate
/// them into a case tree.
///
/// Returns the elaborated term.
pub fn check_clauses(
    context: &Context,
    metas: &mut meta::Env,
    _case_span: FileSpan,
    scrutinees: &[Term<'_>],
    clauses: Vec<Clause<'_>>,
    expected_ty: &Rc<domain::Type>,
) -> Result<Rc<syntax::Term>, Diagnostic<FileSpan>> {
    let mut context = context.clone();

    let (scrutinees, params, expected_params, clauses, body_ty) =
        intro_params(&mut context, metas, scrutinees, clauses, expected_ty)?;
    // FIXME: not the right level
    let default = Rc::from(syntax::Term::FunElim(
        Rc::from(syntax::Term::prim("abort")),
        AppMode::Explicit,
        Rc::from(syntax::Term::literal_intro(
            "entered unreachable code".to_owned(),
        )),
    ));
    let body = check_branches(
        &context,
        metas,
        &expected_params,
        clauses,
        &default,
        &body_ty,
    )?;

    Ok(done(scrutinees, params, body))
}

/// Synthesize the type of the clauses, elaborating them into a case tree.
///
/// Returns the elaborated term and its synthesized type.
pub fn synth_clauses(
    context: &Context,
    metas: &mut meta::Env,
    case_span: FileSpan,
    scrutinees: &[Term<'_>],
    clauses: Vec<Clause<'_>>,
) -> Result<(Rc<syntax::Term>, Rc<domain::Type>), Diagnostic<FileSpan>> {
    // TODO: replicate the behaviour of `check_clauses`

    match clauses.split_first() {
        Some((clause, [])) => {
            if let Some(param) = clause.params.first() {
                // TODO: We will be able to type this once we have annotated patterns!
                return Err(
                    Diagnostic::new_error("unable to infer the type of parameter")
                        .with_label(DiagnosticLabel::new_primary(param.span())),
                );
            }

            synth_clause_body(&context, metas, clause)
        },
        Some((_, _)) => Err(
            Diagnostic::new_error("multi clause functions are not yet supported")
                .with_label(DiagnosticLabel::new_primary(case_span)),
        ),
        None => Err(
            Diagnostic::new_error("empty case matches are not yet supported")
                .with_label(DiagnosticLabel::new_primary(case_span)),
        ),
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper types
////////////////////////////////////////////////////////////////////////////////////////////////////

enum CheckedPattern<'file> {
    Var(Option<SpannedString<'file>>),
    LiteralIntro(LiteralIntro),
}

#[derive(Clone)]
struct ExpectedParam {
    level: var::Level,
    var: Rc<domain::Value>,
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper functions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Introduce the parameters that we need for this set of clauses
fn intro_params<'file>(
    context: &mut Context,
    metas: &mut meta::Env,
    scrutinees: &[Term<'_>],
    mut clauses: Vec<Clause<'file>>,
    expected_ty: &Rc<domain::Type>,
) -> Result<
    (
        Vec<(Rc<syntax::Term>, Option<Rc<syntax::Term>>)>,
        Vec<(AppMode, Option<String>)>,
        Vec<ExpectedParam>,
        Vec<Clause<'file>>,
        Rc<domain::Type>,
    ),
    Diagnostic<FileSpan>,
> {
    use self::CheckedPattern::Var;

    log::trace!("introduce parameters");

    let mut scrutinees_iter = scrutinees.iter();
    let mut checked_scrutinees = Vec::with_capacity(scrutinees.len());
    let mut params = Vec::with_capacity(scrutinees.len());
    let mut expected_params = Vec::with_capacity(scrutinees.len());
    let mut expected_ty = expected_ty.clone();

    while let Some((app_mode, param_ty, param_step)) =
        next_expected_param(context, metas, &mut scrutinees_iter, &expected_ty)?
    {
        let mut is_done = false;

        for clause in &mut clauses {
            match (is_done, clause.params.split_first()) {
                (false, Some((param, params))) => {
                    match check_param(context, metas, param, app_mode, &param_ty)? {
                        pattern @ Var(None) => clause.checked_patterns.push_back(pattern),
                        pattern => {
                            clause.params = params;
                            clause.checked_patterns.push_back(pattern);
                        },
                    }
                },
                (true, Some((param, params))) => {
                    let span = match params.last() {
                        None => param.span(),
                        Some(last_param) => FileSpan::merge(param.span(), last_param.span()),
                    };
                    return Err(Diagnostic::new_error("too many parameters")
                        .with_label(DiagnosticLabel::new_primary(span)));
                },
                (false, None) => is_done = true,
                (true, None) => continue,
            }
        }

        if is_done {
            break;
        }

        let param_level = context.values().size().next_level();
        match param_step {
            ParamStep::Scrutinee(param_term, param_ty_term, param_value) => {
                context.add_fresh_defn(param_value, param_ty.clone());
                checked_scrutinees.push((param_term, param_ty_term));
                expected_params.push(ExpectedParam {
                    level: param_level,
                    var: Rc::from(domain::Value::var(param_level)),
                });
            },
            ParamStep::Param(name_hint, next_body_ty) => {
                let param_var = context.add_fresh_param(param_ty.clone());
                params.push((app_mode.clone(), name_hint));
                expected_params.push(ExpectedParam {
                    level: param_level,
                    var: param_var.clone(),
                });
                expected_ty = context.app_closure(metas, next_body_ty, param_var)?;
            },
        }
    }

    Ok((
        checked_scrutinees,
        params,
        expected_params,
        clauses,
        expected_ty,
    ))
}

enum ParamStep<'ty> {
    Scrutinee(
        Rc<syntax::Term>,
        Option<Rc<syntax::Term>>,
        Rc<domain::Value>,
    ),
    Param(Option<String>, &'ty domain::AppClosure),
}

/// Get the next expected parameter from the expected type
fn next_expected_param<'file, 'ty>(
    context: &Context,
    metas: &mut meta::Env,
    scrutinees: &mut impl Iterator<Item = &'file Term<'file>>,
    expected_ty: &'ty Rc<domain::Type>,
) -> Result<Option<(&'ty AppMode, Rc<domain::Type>, ParamStep<'ty>)>, Diagnostic<FileSpan>> {
    match scrutinees.next() {
        Some(scrutinee) => {
            let (param_term, param_ty) =
                synth_term(MetaInsertion::Yes, &context, metas, &scrutinee)?;
            let param_value = context.eval_term(metas, scrutinee.span(), &param_term)?;
            Ok(Some((
                &AppMode::Explicit,
                param_ty,
                ParamStep::Scrutinee(param_term, None, param_value),
            )))
        },
        None => match expected_ty.as_ref() {
            domain::Value::FunType(app_mode, name_hint, param_ty, body_ty) => Ok(Some((
                app_mode,
                param_ty.clone(),
                ParamStep::Param(name_hint.clone(), body_ty),
            ))),
            _ => Ok(None),
        },
    }
}

/// Check that a given parameter matches the expected application mode, and
/// return the pattern inside it.
fn check_param<'file>(
    context: &Context,
    metas: &mut meta::Env,
    param: &'file IntroParam<'file>,
    expected_app_mode: &AppMode,
    expected_ty: &Rc<domain::Type>,
) -> Result<CheckedPattern<'file>, Diagnostic<FileSpan>> {
    log::trace!("check param:\t{}\tapp mode:\t{}", param, expected_app_mode);

    let check_pattern = |pattern: &Pattern<'file>| match pattern {
        Pattern::Var(name) => Ok(CheckedPattern::Var(Some(name.clone()))),
        Pattern::LiteralIntro(kind, src) => {
            let literal_intro = literal::check(&context, metas, *kind, src, expected_ty)?;
            Ok(CheckedPattern::LiteralIntro(literal_intro))
        },
    };

    match (param, expected_app_mode) {
        (IntroParam::Explicit(pattern), AppMode::Explicit) => check_pattern(pattern),
        (IntroParam::Implicit(_, intro_label, pattern), AppMode::Implicit(ty_label))
        | (IntroParam::Instance(_, intro_label, pattern), AppMode::Instance(ty_label))
            if intro_label.slice == ty_label.0 =>
        {
            match pattern {
                None => Ok(CheckedPattern::Var(Some(intro_label.clone()))),
                Some(pattern) => check_pattern(pattern),
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

/// Implements the 'mixture rule' and the 'empty rule'
fn check_branches(
    context: &Context,
    metas: &mut meta::Env,
    params: &[ExpectedParam],
    clauses: Vec<Clause<'_>>,
    default: &Rc<syntax::Term>,
    expected_body_ty: &Rc<domain::Type>,
) -> Result<Rc<syntax::Term>, Diagnostic<FileSpan>> {
    log::trace!("check branches");

    match params.split_first() {
        None => check_branches_empty(context, metas, clauses, default, expected_body_ty),
        Some(params) => {
            check_branches_mixture(context, metas, params, clauses, default, expected_body_ty)
        },
    }
}

/// Implements the 'empty rule'
fn check_branches_empty(
    context: &Context,
    metas: &mut meta::Env,
    clauses: Vec<Clause<'_>>,
    _default: &Rc<syntax::Term>,
    expected_body_ty: &Rc<domain::Type>,
) -> Result<Rc<syntax::Term>, Diagnostic<FileSpan>> {
    log::trace!("check branches empty");

    // foldr FATBAR default [body | ([], body) <- clauses]

    // > Regarding the fat bar, I implemented that as something like
    // > `t1 [] t2 == let f () = t2 in t1[fail/f()]`, plus some inlining
    // > of `f` when it's only used once or very small
    //
    // - [Ollef](https://gitter.im/pikelet-lang/Lobby?at=5c91f5bc8aa66959b63dfa40)

    // for clause in clauses.iter().rev() {
    //     let body = check_clause_body(context, metas, clause, expected_body_ty)?;
    // }

    // Ok(Rc::from(syntax::Term::Let(
    //     default.clone(),
    //     unimplemented!("check_branches"),
    // )))

    match clauses.split_first() {
        Some((clause, [])) => check_clause_body(context, metas, clause, expected_body_ty),
        Some((_, _)) => Err(Diagnostic::new_error(
            "case matches with duplicate patterns are not yet supported",
        )),
        None => Err(Diagnostic::new_error(
            "empty case matches are not yet supported",
        )),
    }
}

enum PatternGroup<'file> {
    Var(Vec<Clause<'file>>),
    LiteralIntro(Vec<(LiteralIntro, Vec<Clause<'file>>)>),
}

// Group patterns by the kind of the first pattern in each clause
fn group_first_patterns<'file>(
    param: &ExpectedParam,
    clauses: Vec<Clause<'file>>,
) -> Vec<PatternGroup<'file>> {
    let mut groups = Vec::new();
    for mut clause in clauses {
        match clause.checked_patterns.pop_front() {
            None => panic!("not enough patterns"),
            Some(CheckedPattern::Var(name)) => {
                // Introduce the appropriate binder when we see a variable
                clause.binders.push((name, param.clone()));

                match groups.last_mut() {
                    Some(PatternGroup::Var(clauses)) => clauses.push(clause),
                    _ => groups.push(PatternGroup::Var(vec![clause])),
                }
            },
            Some(CheckedPattern::LiteralIntro(literal_intro)) => match groups.last_mut() {
                Some(PatternGroup::LiteralIntro(clauses)) => match clauses
                    .binary_search_by(|(l, _)| l.partial_cmp(&literal_intro).unwrap())
                {
                    Ok(index) => clauses.get_mut(index).unwrap().1.push(clause),
                    Err(index) => clauses.insert(index, (literal_intro, vec![clause])),
                },
                _ => groups.push(PatternGroup::LiteralIntro(vec![(
                    literal_intro,
                    vec![clause],
                )])),
            },
        }
    }
    groups
}

/// Implements the 'mixture rule' and the 'variable rule'
fn check_branches_mixture<'file>(
    context: &Context,
    metas: &mut meta::Env,
    (param, params): (&ExpectedParam, &[ExpectedParam]),
    clauses: Vec<Clause<'_>>,
    default: &Rc<syntax::Term>,
    expected_body_ty: &Rc<domain::Type>,
) -> Result<Rc<syntax::Term>, Diagnostic<FileSpan>> {
    log::trace!("check branches mixture");

    group_first_patterns(param, clauses).into_iter().rev().fold(
        Ok(default.clone()),
        |default, group| match group {
            PatternGroup::Var(clauses) => {
                check_branches(context, metas, params, clauses, &default?, expected_body_ty)
            },
            PatternGroup::LiteralIntro(clauses) => {
                let params = (param, params);
                check_branches_literal(context, metas, params, clauses, &default?, expected_body_ty)
            },
        },
    )
}

/// Implements the 'literal rule' (adapted from the 'constructor rule').
fn check_branches_literal<'file>(
    context: &Context,
    metas: &mut meta::Env,
    (param, params): (&ExpectedParam, &[ExpectedParam]),
    clauses: Vec<(LiteralIntro, Vec<Clause<'file>>)>,
    default: &Rc<syntax::Term>,
    expected_body_ty: &Rc<domain::Type>,
) -> Result<Rc<syntax::Term>, Diagnostic<FileSpan>> {
    log::trace!("check branches literal");

    let scrutinee = Rc::from(syntax::Term::var(
        context.values().size().index(param.level),
    ));
    let clauses = Rc::from(
        clauses
            .into_iter()
            .map(|(literal_intro, clauses)| {
                let body =
                    check_branches(context, metas, params, clauses, default, expected_body_ty)?;
                Ok((literal_intro, body))
            })
            .collect::<Result<Vec<_>, _>>()?,
    );

    Ok(Rc::from(syntax::Term::LiteralElim(
        scrutinee,
        clauses,
        default.clone(),
    )))
}

/// Check that the body of the given clause conforms to they expected type, and
/// elaborate it.
fn check_clause_body(
    context: &Context,
    metas: &mut meta::Env,
    clause: &Clause<'_>,
    expected_body_ty: &Rc<domain::Type>,
) -> Result<Rc<syntax::Term>, Diagnostic<FileSpan>> {
    log::trace!("check clause body");

    let mut context = context.clone();

    for (name, param) in &clause.binders {
        if let Some(name) = name {
            context.add_name(name, param.level);
        }
    }

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
