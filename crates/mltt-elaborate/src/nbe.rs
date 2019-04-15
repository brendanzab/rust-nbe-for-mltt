//! Wrappers around the core NBE functions that return diagnostics on errors.

use language_reporting::{Diagnostic, Label as DiagnosticLabel};
use mltt_core::nbe;
use mltt_core::syntax::{core, domain};
use mltt_span::FileSpan;

pub use mltt_core::nbe::PrimEnv;

pub fn app_closure(
    prims: &nbe::PrimEnv,
    closure: &domain::AppClosure,
    arg: domain::RcValue,
) -> Result<domain::RcValue, Diagnostic<FileSpan>> {
    nbe::app_closure(prims, closure, arg)
        .map_err(|error| Diagnostic::new_bug(format!("failed closure application: {}", error)))
}

pub fn eval_term(
    prims: &nbe::PrimEnv,
    values: &domain::Env,
    span: impl Into<Option<FileSpan>>,
    term: &core::RcTerm,
) -> Result<domain::RcValue, Diagnostic<FileSpan>> {
    nbe::eval_term(prims, values, term).map_err(|error| match span.into() {
        None => Diagnostic::new_bug(format!("failed to evaluate term: {}", error)),
        Some(span) => Diagnostic::new_bug("failed to evaluate term")
            .with_label(DiagnosticLabel::new_primary(span).with_message(error.message)),
    })
}

pub fn read_back_value(
    prims: &nbe::PrimEnv,
    env_size: domain::EnvSize,
    span: impl Into<Option<FileSpan>>,
    value: &domain::RcValue,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    nbe::read_back_value(prims, env_size, value).map_err(|error| match span.into() {
        None => Diagnostic::new_bug(format!("failed to read-back value: {}", error)),
        Some(span) => Diagnostic::new_bug("failed to read-back value")
            .with_label(DiagnosticLabel::new_primary(span).with_message(error.message)),
    })
}

pub fn normalize_term(
    prims: &nbe::PrimEnv,
    values: &domain::Env,
    span: impl Into<Option<FileSpan>>,
    term: &core::RcTerm,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    nbe::normalize_term(prims, values, term).map_err(|error| match span.into() {
        None => Diagnostic::new_bug(format!("failed to normalize term: {}", error)),
        Some(span) => Diagnostic::new_bug("failed to normalize term")
            .with_label(DiagnosticLabel::new_primary(span).with_message(error.message)),
    })
}

pub fn expect_subtype(
    prims: &nbe::PrimEnv,
    env_size: domain::EnvSize,
    span: FileSpan,
    ty1: &domain::RcType,
    ty2: &domain::RcType,
) -> Result<(), Diagnostic<FileSpan>> {
    match nbe::check_subtype(prims, env_size, ty1, ty2) {
        Ok(true) => Ok(()),
        Ok(false) => Err(Diagnostic::new_error("not a subtype").with_label(
            DiagnosticLabel::new_primary(span).with_message(format!(
                "`{}` is not a subtype of `{}`",
                read_back_value(prims, env_size, None, ty1).unwrap(),
                read_back_value(prims, env_size, None, ty2).unwrap(),
            )),
        )),
        Err(error) => {
            let message = format!("failed subtype check: {}", error);
            Err(Diagnostic::new_bug(message))
        },
    }
}
