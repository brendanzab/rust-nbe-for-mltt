//! Wrappers around the core NBE functions that return diagnostics on errors.

use language_reporting::{Diagnostic, Label as DiagnosticLabel};
use mltt_core::{domain, global, meta, nbe, prim, syntax, var, AppMode, Label};
use mltt_span::FileSpan;
use std::rc::Rc;

pub fn eval_fun_elim(
    globals: &global::Env,
    prims: &prim::Env,
    metas: &meta::Env,
    fun: Rc<domain::Value>,
    app_mode: &AppMode,
    arg: Rc<domain::Value>,
) -> Result<Rc<domain::Value>, Diagnostic<FileSpan>> {
    nbe::eval_fun_elim(globals, prims, metas, fun, app_mode, arg)
        .map_err(|error| Diagnostic::new_bug(format!("failed function elimination: {}", error)))
}

pub fn eval_literal_elim(
    globals: &global::Env,
    prims: &prim::Env,
    metas: &meta::Env,
    scrutinee: Rc<domain::Value>,
    closure: domain::LiteralClosure,
) -> Result<Rc<domain::Value>, Diagnostic<FileSpan>> {
    nbe::eval_literal_elim(globals, prims, metas, scrutinee, closure)
        .map_err(|error| Diagnostic::new_bug(format!("failed literal elimination: {}", error)))
}

pub fn eval_record_elim(
    term: Rc<domain::Value>,
    label: &Label,
) -> Result<Rc<domain::Value>, Diagnostic<FileSpan>> {
    nbe::eval_record_elim(term, label)
        .map_err(|error| Diagnostic::new_bug(format!("failed record elimination: {}", error)))
}

pub fn app_closure(
    globals: &global::Env,
    prims: &prim::Env,
    metas: &meta::Env,
    closure: &domain::AppClosure,
    arg: Rc<domain::Value>,
) -> Result<Rc<domain::Value>, Diagnostic<FileSpan>> {
    nbe::app_closure(globals, prims, metas, closure, arg)
        .map_err(|error| Diagnostic::new_bug(format!("failed closure application: {}", error)))
}

pub fn eval_term(
    globals: &global::Env,
    prims: &prim::Env,
    metas: &meta::Env,
    values: &var::Env<Rc<domain::Value>>,
    span: impl Into<Option<FileSpan>>,
    term: &Rc<syntax::Term>,
) -> Result<Rc<domain::Value>, Diagnostic<FileSpan>> {
    nbe::eval_term(globals, prims, metas, values, term).map_err(|error| match span.into() {
        None => Diagnostic::new_bug(format!("failed to evaluate term: {}", error)),
        Some(span) => Diagnostic::new_bug("failed to evaluate term")
            .with_label(DiagnosticLabel::new_primary(span).with_message(error)),
    })
}

pub fn read_back_value(
    globals: &global::Env,
    prims: &prim::Env,
    metas: &meta::Env,
    env_size: var::Size,
    span: impl Into<Option<FileSpan>>,
    value: &Rc<domain::Value>,
) -> Result<Rc<syntax::Term>, Diagnostic<FileSpan>> {
    nbe::read_back_value(globals, prims, metas, env_size, value).map_err(|error| {
        match span.into() {
            None => Diagnostic::new_bug(format!("failed to read-back value: {}", error)),
            Some(span) => Diagnostic::new_bug("failed to read-back value")
                .with_label(DiagnosticLabel::new_primary(span).with_message(error)),
        }
    })
}

pub fn normalize_term(
    globals: &global::Env,
    prims: &prim::Env,
    metas: &meta::Env,
    values: &var::Env<Rc<domain::Value>>,
    span: impl Into<Option<FileSpan>>,
    term: &Rc<syntax::Term>,
) -> Result<Rc<syntax::Term>, Diagnostic<FileSpan>> {
    nbe::normalize_term(globals, prims, metas, values, term).map_err(|error| match span.into() {
        None => Diagnostic::new_bug(format!("failed to normalize term: {}", error)),
        Some(span) => Diagnostic::new_bug("failed to normalize term")
            .with_label(DiagnosticLabel::new_primary(span).with_message(error)),
    })
}

pub fn force_value(
    globals: &global::Env,
    prims: &prim::Env,
    metas: &meta::Env,
    span: impl Into<Option<FileSpan>>,
    value: &Rc<domain::Value>,
) -> Result<Rc<domain::Value>, Diagnostic<FileSpan>> {
    nbe::force_value(globals, prims, metas, value).map_err(|error| match span.into() {
        None => Diagnostic::new_bug(format!("failed to force value: {}", error)),
        Some(span) => Diagnostic::new_bug("failed to force value")
            .with_label(DiagnosticLabel::new_primary(span).with_message(error)),
    })
}
