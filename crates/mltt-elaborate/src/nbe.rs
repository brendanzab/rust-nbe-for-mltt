//! Wrappers around the core NBE functions that return diagnostics on errors.

use language_reporting::{Diagnostic, Label as DiagnosticLabel};
use mltt_core::{domain, meta, nbe, prim, syntax, var};
use mltt_span::FileSpan;

pub fn app_closure(
    prims: &prim::Env,
    metas: &meta::Env<domain::RcValue>,
    closure: &domain::AppClosure,
    arg: domain::RcValue,
) -> Result<domain::RcValue, Diagnostic<FileSpan>> {
    nbe::app_closure(prims, metas, closure, arg)
        .map_err(|error| Diagnostic::new_bug(format!("failed closure application: {}", error)))
}

pub fn eval_term(
    prims: &prim::Env,
    metas: &meta::Env<domain::RcValue>,
    values: &var::Env<domain::RcValue>,
    span: impl Into<Option<FileSpan>>,
    term: &syntax::RcTerm,
) -> Result<domain::RcValue, Diagnostic<FileSpan>> {
    nbe::eval_term(prims, metas, values, term).map_err(|error| match span.into() {
        None => Diagnostic::new_bug(format!("failed to evaluate term: {}", error)),
        Some(span) => Diagnostic::new_bug("failed to evaluate term")
            .with_label(DiagnosticLabel::new_primary(span).with_message(error)),
    })
}

pub fn read_back_value(
    prims: &prim::Env,
    metas: &meta::Env<domain::RcValue>,
    env_size: var::Size,
    span: impl Into<Option<FileSpan>>,
    value: &domain::RcValue,
) -> Result<syntax::RcTerm, Diagnostic<FileSpan>> {
    nbe::read_back_value(prims, metas, env_size, value).map_err(|error| match span.into() {
        None => Diagnostic::new_bug(format!("failed to read-back value: {}", error)),
        Some(span) => Diagnostic::new_bug("failed to read-back value")
            .with_label(DiagnosticLabel::new_primary(span).with_message(error)),
    })
}

pub fn normalize_term(
    prims: &prim::Env,
    metas: &meta::Env<domain::RcValue>,
    values: &var::Env<domain::RcValue>,
    span: impl Into<Option<FileSpan>>,
    term: &syntax::RcTerm,
) -> Result<syntax::RcTerm, Diagnostic<FileSpan>> {
    nbe::normalize_term(prims, metas, values, term).map_err(|error| match span.into() {
        None => Diagnostic::new_bug(format!("failed to normalize term: {}", error)),
        Some(span) => Diagnostic::new_bug("failed to normalize term")
            .with_label(DiagnosticLabel::new_primary(span).with_message(error)),
    })
}

pub fn check_subtype(
    prims: &prim::Env,
    metas: &meta::Env<domain::RcValue>,
    env_size: var::Size,
    span: FileSpan,
    ty1: &domain::RcType,
    ty2: &domain::RcType,
) -> Result<(), Diagnostic<FileSpan>> {
    match nbe::check_subtype(prims, metas, env_size, ty1, ty2) {
        Ok(true) => Ok(()),
        Ok(false) => Err(Diagnostic::new_error("not a subtype").with_label(
            DiagnosticLabel::new_primary(span).with_message(format!(
                "`{}` is not a subtype of `{}`",
                read_back_value(prims, metas, env_size, None, ty1).unwrap(),
                read_back_value(prims, metas, env_size, None, ty2).unwrap(),
            )),
        )),
        Err(error) => {
            let message = format!("failed subtype check: {}", error);
            Err(Diagnostic::new_bug(message))
        },
    }
}
