//! Wrappers around the core NBE functions that return diagnostics on errors.

use language_reporting::{Diagnostic, Label as DiagnosticLabel};
use mltt_core::{domain, nbe, syntax, var, AppMode};
use mltt_span::FileSpan;

pub use mltt_core::nbe::Config;

pub fn eval_fun_elim(
    config: Config<'_>,
    fun: domain::RcValue,
    app_mode: &AppMode,
    arg: domain::RcValue,
) -> Result<domain::RcValue, Diagnostic<FileSpan>> {
    nbe::eval_fun_elim(config, fun, app_mode, arg)
        .map_err(|error| Diagnostic::new_bug(format!("failed function elimination: {}", error)))
}

pub fn eval_literal_elim(
    config: Config<'_>,
    scrutinee: domain::RcValue,
    closure: domain::LiteralClosure,
) -> Result<domain::RcValue, Diagnostic<FileSpan>> {
    nbe::eval_literal_elim(config, scrutinee, closure)
        .map_err(|error| Diagnostic::new_bug(format!("failed literal elimination: {}", error)))
}

pub fn app_closure(
    config: Config<'_>,
    closure: &domain::AppClosure,
    arg: domain::RcValue,
) -> Result<domain::RcValue, Diagnostic<FileSpan>> {
    nbe::app_closure(config, closure, arg)
        .map_err(|error| Diagnostic::new_bug(format!("failed closure application: {}", error)))
}

pub fn eval_term(
    config: Config<'_>,
    values: &var::Env<domain::RcValue>,
    span: impl Into<Option<FileSpan>>,
    term: &syntax::RcTerm,
) -> Result<domain::RcValue, Diagnostic<FileSpan>> {
    nbe::eval_term(config, values, term).map_err(|error| match span.into() {
        None => Diagnostic::new_bug(format!("failed to evaluate term: {}", error)),
        Some(span) => Diagnostic::new_bug("failed to evaluate term")
            .with_label(DiagnosticLabel::new_primary(span).with_message(error)),
    })
}

pub fn read_back_value(
    config: Config<'_>,
    env_size: var::Size,
    span: impl Into<Option<FileSpan>>,
    value: &domain::RcValue,
) -> Result<syntax::RcTerm, Diagnostic<FileSpan>> {
    nbe::read_back_value(config, env_size, value).map_err(|error| match span.into() {
        None => Diagnostic::new_bug(format!("failed to read-back value: {}", error)),
        Some(span) => Diagnostic::new_bug("failed to read-back value")
            .with_label(DiagnosticLabel::new_primary(span).with_message(error)),
    })
}

pub fn normalize_term(
    config: Config<'_>,
    values: &var::Env<domain::RcValue>,
    span: impl Into<Option<FileSpan>>,
    term: &syntax::RcTerm,
) -> Result<syntax::RcTerm, Diagnostic<FileSpan>> {
    nbe::normalize_term(config, values, term).map_err(|error| match span.into() {
        None => Diagnostic::new_bug(format!("failed to normalize term: {}", error)),
        Some(span) => Diagnostic::new_bug("failed to normalize term")
            .with_label(DiagnosticLabel::new_primary(span).with_message(error)),
    })
}

pub fn force_value(
    config: Config<'_>,
    span: impl Into<Option<FileSpan>>,
    value: &domain::RcValue,
) -> Result<domain::RcValue, Diagnostic<FileSpan>> {
    nbe::force_value(config, value).map_err(|error| match span.into() {
        None => Diagnostic::new_bug(format!("failed to force value: {}", error)),
        Some(span) => Diagnostic::new_bug("failed to force value")
            .with_label(DiagnosticLabel::new_primary(span).with_message(error)),
    })
}
