//! Elaboration of the MLTT language's concrete syntax into its core syntax.
//!
//! Performs the following:
//!
//! - name resolution
//! - desugaring
//! - pattern compilation (TODO)
//! - bidirectional type checking
//! - elaboration of holes (TODO)

#![warn(rust_2018_idioms)]

use language_reporting::{Diagnostic, Label as DiagnosticLabel};
use mltt_concrete::{Arg, Item, Term, TypeParam};
use mltt_core::nbe;
use mltt_core::syntax::{
    core, domain, AppMode, Env, Label, LiteralIntro, LiteralType, UniverseLevel, VarIndex, VarLevel,
};
use mltt_span::FileSpan;
use std::borrow::Cow;
use std::rc::Rc;

use crate::clause::Clause;

mod clause;
mod docs;
mod literal;

/// Local elaboration context.
#[derive(Debug, Clone, PartialEq)]
pub struct Context {
    /// Number of local entries.
    level: VarLevel,
    /// Values to be used during evaluation.
    values: Env<domain::RcValue>,
    /// Type annotations of the binders we have passed over.
    tys: Env<domain::RcType>,
    /// A mapping from the user-defined names to the level in which they were
    /// bound.
    ///
    /// We associate levels to the binder names so that we can recover the
    /// correct debruijn index once we reach a variable name in a nested scope.
    /// Not all entries in the context will have a corresponding name - for
    /// example we don't define a name for non-dependent function types.
    names: im::HashMap<String, VarLevel>,
}

fn do_closure_app(
    closure: &domain::AppClosure,
    arg: domain::RcValue,
) -> Result<domain::RcValue, Diagnostic<FileSpan>> {
    nbe::do_closure_app(closure, arg)
        .map_err(|error| Diagnostic::new_bug(format!("failed closure application: {}", error)))
}

impl Context {
    /// Create a new, empty context
    pub fn new() -> Context {
        Context {
            level: VarLevel(0),
            values: Env::new(),
            tys: Env::new(),
            names: im::HashMap::new(),
        }
    }

    /// Number of local entries in the context
    pub fn level(&self) -> VarLevel {
        self.level
    }

    /// Values to be used during evaluation
    pub fn values(&self) -> &Env<domain::RcValue> {
        &self.values
    }

    /// Types of the entries in the context
    pub fn tys(&self) -> &Env<domain::RcType> {
        &self.tys
    }

    /// Add a local definition to the context.
    pub fn local_define(
        &mut self,
        name: impl Into<Option<String>>,
        value: domain::RcValue,
        ty: domain::RcType,
    ) {
        match name.into() {
            None => log::trace!("insert fresh local"),
            Some(name) => {
                log::trace!("insert named local: {}", name);
                self.names.insert(name, self.level());
            },
        }
        self.level += 1;
        self.values.add_entry(value);
        self.tys.add_entry(ty);
    }

    /// Add a bound variable the context, returning a variable that points to
    /// the correct binder.
    pub fn local_bind(
        &mut self,
        name: impl Into<Option<String>>,
        ty: domain::RcType,
    ) -> domain::RcValue {
        let param = domain::RcValue::var(self.level());
        self.local_define(name, param.clone(), ty);
        param
    }

    /// Lookup the de-bruijn index and the type annotation of a binder in the
    /// context using a user-defined name
    pub fn lookup_binder(&self, name: &str) -> Option<(VarIndex, &domain::RcType)> {
        let level = self.names.get(name)?;
        let index = VarIndex(self.level.0 - (level.0 + 1));
        log::trace!("lookup binder: {} -> @{}", name, index.0);
        let ty = self.tys().lookup_entry(index)?; // FIXME: Internal error?
        Some((index, ty))
    }

    /// Evaluate a term using the evaluation environment
    pub fn eval(
        &self,
        span: impl Into<Option<FileSpan>>,
        term: &core::RcTerm,
    ) -> Result<domain::RcValue, Diagnostic<FileSpan>> {
        nbe::eval(term, self.values()).map_err(|error| match span.into() {
            None => Diagnostic::new_bug(format!("failed to evaluate term: {}", error)),
            Some(span) => Diagnostic::new_bug("failed to evaluate term")
                .with_label(DiagnosticLabel::new_primary(span).with_message(error.message)),
        })
    }

    /// Read a value back into the core syntax, normalizing as required.
    pub fn read_back(
        &self,
        span: impl Into<Option<FileSpan>>,
        value: &domain::RcValue,
    ) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
        nbe::read_back_term(self.level(), value).map_err(|error| match span.into() {
            None => Diagnostic::new_bug(format!("failed to read-back value: {}", error)),
            Some(span) => Diagnostic::new_bug("failed to read-back value")
                .with_label(DiagnosticLabel::new_primary(span).with_message(error.message)),
        })
    }

    /// Fully normalize a term by first evaluating it, then reading it back.
    pub fn normalize(
        &self,
        span: impl Into<Option<FileSpan>>,
        term: &core::RcTerm,
    ) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
        let span = span.into();
        let value = self.eval(span, term)?;
        self.read_back(span, &value)
    }

    /// Expect that `ty1` is a subtype of `ty2` in the current context
    pub fn expect_subtype(
        &self,
        span: FileSpan,
        ty1: &domain::RcType,
        ty2: &domain::RcType,
    ) -> Result<(), Diagnostic<FileSpan>> {
        match nbe::check_subtype(self.level(), ty1, ty2) {
            Ok(true) => Ok(()),
            Ok(false) => Err(Diagnostic::new_error("not a subtype").with_label(
                DiagnosticLabel::new_primary(span).with_message(format!(
                    "`{}` is not a subtype of `{}`",
                    self.read_back(None, ty1).unwrap(),
                    self.read_back(None, ty2).unwrap(),
                )),
            )),
            Err(error) => {
                let message = format!("failed subtype check: {}", error);
                Err(Diagnostic::new_bug(message))
            },
        }
    }
}

impl Default for Context {
    fn default() -> Context {
        use mltt_core::syntax::domain::{RcValue, Value};

        let mut context = Context::new();
        let lit_ty = |ty| RcValue::from(Value::LiteralType(ty));
        let lit_intro = |lit| RcValue::from(Value::LiteralIntro(lit));
        let bool_intro = |lit| lit_intro(LiteralIntro::Bool(lit));
        let u0 = RcValue::from(Value::Universe(UniverseLevel(0)));
        let bool = lit_ty(LiteralType::Bool);

        context.local_define("String".to_owned(), lit_ty(LiteralType::String), u0.clone());
        context.local_define("Char".to_owned(), lit_ty(LiteralType::Char), u0.clone());
        context.local_define("Bool".to_owned(), bool.clone(), u0.clone());
        context.local_define("true".to_owned(), bool_intro(true), bool.clone());
        context.local_define("false".to_owned(), bool_intro(false), bool.clone());
        context.local_define("U8".to_owned(), lit_ty(LiteralType::U8), u0.clone());
        context.local_define("U16".to_owned(), lit_ty(LiteralType::U16), u0.clone());
        context.local_define("U32".to_owned(), lit_ty(LiteralType::U32), u0.clone());
        context.local_define("U64".to_owned(), lit_ty(LiteralType::U64), u0.clone());
        context.local_define("S8".to_owned(), lit_ty(LiteralType::S8), u0.clone());
        context.local_define("S16".to_owned(), lit_ty(LiteralType::S16), u0.clone());
        context.local_define("S32".to_owned(), lit_ty(LiteralType::S32), u0.clone());
        context.local_define("S64".to_owned(), lit_ty(LiteralType::S64), u0.clone());
        context.local_define("F32".to_owned(), lit_ty(LiteralType::F32), u0.clone());
        context.local_define("F64".to_owned(), lit_ty(LiteralType::F64), u0.clone());

        context
    }
}

/// Check that this is a valid module.
///
/// Returns the elaborated items.
pub fn check_module(
    context: &Context,
    concrete_items: &[Item<'_>],
) -> Result<Vec<core::Item>, Diagnostic<FileSpan>> {
    // The local elaboration context
    let mut context = context.clone();
    check_items(&mut context, concrete_items)
}

/// Check the given items and add them to the context.
///
/// Returns the elaborated items.
fn check_items(
    context: &mut Context,
    concrete_items: &[Item<'_>],
) -> Result<Vec<core::Item>, Diagnostic<FileSpan>> {
    // Declarations that may be waiting to be defined
    let mut forward_declarations = im::HashMap::new();
    // The elaborated items
    let mut core_items = {
        let expected_defn_count = concrete_items.iter().filter(|i| i.is_definition()).count();
        Vec::with_capacity(expected_defn_count)
    };

    for concrete_item in concrete_items {
        use im::hashmap::Entry;

        match concrete_item {
            Item::Declaration(declaration) => {
                let label = declaration.label.slice;
                let concrete_body_ty = &declaration.body_ty;

                log::trace!("checking declaration:\t\t{}\t: {}", label, concrete_body_ty);

                match forward_declarations.entry(label) {
                    // No previous declaration for this name was seen, so we can
                    // go-ahead and type check, elaborate, and then add it to
                    // the context
                    Entry::Vacant(entry) => {
                        let (body_ty, _) = synth_universe(&context, &concrete_body_ty)?;
                        // Ensure that we evaluate the forward declaration in
                        // the current context - if we wait until later more
                        // definitions might have come in to scope!
                        let body_ty = context.eval(concrete_body_ty.span(), &body_ty)?;
                        entry.insert(Some((&declaration.docs, body_ty)));
                    },
                    // There's a declaration for this name already pending - we
                    // can't add a new one!
                    Entry::Occupied(_) => {
                        return Err(Diagnostic::new_error("already declared")
                            .with_label(DiagnosticLabel::new_primary(declaration.label.span())));
                    },
                }
            },
            Item::Definition(definition) => {
                let label = definition.label.slice;
                let params = &definition.params;
                let body_ty = definition.body_ty.as_ref();
                let body = &definition.body;

                log::trace!("checking definition:\t\t{}\t= {}", label, body);

                let (doc, term, term_span, ty) = match forward_declarations.entry(label) {
                    // No prior declaration was found, so we'll try synthesizing
                    // its type instead
                    Entry::Vacant(entry) => {
                        let docs = docs::concat(&definition.docs);
                        let clause = Clause::new(params, body_ty, body);
                        let (term, ty) = clause::synth_clause(&context, clause)?;

                        entry.insert(None);

                        (docs, term, body.span(), ty)
                    },
                    // Something has happened with this declaration, let's
                    // 'take' a look!
                    Entry::Occupied(mut entry) => match entry.get_mut().take() {
                        // We found a prior declaration, so we'll use it as a
                        // basis for checking the definition
                        Some((decl_docs, ty)) => {
                            let docs = docs::merge(&definition.label, decl_docs, &definition.docs)?;
                            let clause = Clause::new(params, body_ty, body);
                            let term = clause::check_clause(&context, clause, &ty)?;

                            (docs, term, body.span(), ty)
                        },
                        // This declaration was already given a definition, so
                        // this is an error!
                        //
                        // NOTE: Some languages (eg. Haskell, Agda, Idris, and
                        // Erlang) turn duplicate definitions into case matches.
                        // Languages like Elm don't. What should we do here?
                        None => {
                            return Err(Diagnostic::new_error("already defined").with_label(
                                DiagnosticLabel::new_primary(definition.label.span()),
                            ));
                        },
                    },
                };
                let value = context.eval(term_span, &term)?;
                // NOTE: Not sure how expensive this readback is here!
                let term_ty = context.read_back(None, &ty)?;

                log::trace!("elaborated declaration:\t{}\t: {}", label, term_ty);
                log::trace!("elaborated definition:\t{}\t= {}", label, term);

                context.local_define(label.to_owned(), value, ty);
                core_items.push(core::Item {
                    doc,
                    label: label.to_owned(),
                    term_ty,
                    term,
                });
            },
        }
    }

    Ok(core_items)
}

/// Check that a given argument matches the expected application mode, and
/// return the term inside it.
fn check_arg_app_mode<'arg, 'file>(
    concrete_arg: &'arg Arg<'file>,
    expected_app_mode: &AppMode,
) -> Result<Cow<'arg, Term<'file>>, Diagnostic<FileSpan>> {
    match (concrete_arg, expected_app_mode) {
        (Arg::Explicit(concrete_arg), AppMode::Explicit) => Ok(Cow::Borrowed(concrete_arg)),
        (Arg::Implicit(_, intro_label, concrete_arg), AppMode::Implicit(ty_label))
        | (Arg::Instance(_, intro_label, concrete_arg), AppMode::Instance(ty_label))
            if intro_label.slice == ty_label.0 =>
        {
            match concrete_arg {
                None => Ok(Cow::Owned(Term::Var(intro_label.clone()))),
                Some(concrete_arg) => Ok(Cow::Borrowed(concrete_arg)),
            }
        },
        (_, AppMode::Implicit(ty_label)) => {
            let message = "inference of implicit arguments is not yet supported";
            Err(Diagnostic::new_error(message).with_label(
                DiagnosticLabel::new_primary(concrete_arg.span()).with_message(format!(
                    "add the explicit argument `{{{} = ..}}` here",
                    ty_label,
                )),
            ))
        },
        (_, AppMode::Instance(ty_label)) => {
            let message = "inference of instance arguments is not yet supported";
            Err(Diagnostic::new_error(message).with_label(
                DiagnosticLabel::new_primary(concrete_arg.span()).with_message(format!(
                    "add the explicit argument `{{{{{} = ..}}}}` here",
                    ty_label,
                )),
            ))
        },
        (Arg::Implicit(span, _, _), AppMode::Explicit)
        | (Arg::Instance(span, _, _), AppMode::Explicit) => {
            let message = "unexpected argument";
            Err(Diagnostic::new_error(message).with_label(
                DiagnosticLabel::new_primary(*span).with_message("this argument is not needed"),
            ))
        },
    }
}

/// Ensures that the given term is a universe, returning the level of that
/// universe and its elaborated form.
fn synth_universe(
    context: &Context,
    concrete_term: &Term<'_>,
) -> Result<(core::RcTerm, UniverseLevel), Diagnostic<FileSpan>> {
    let (term, ty) = synth_term(context, concrete_term)?;
    match ty.as_ref() {
        domain::Value::Universe(level) => Ok((term, *level)),
        _ => Err(Diagnostic::new_error("type expected").with_label(
            DiagnosticLabel::new_primary(concrete_term.span())
                .with_message(format!("found `{}`", context.read_back(None, &ty)?)),
        )),
    }
}

/// Check that a given term conforms to an expected type.
///
/// Returns the elaborated term.
pub fn check_term(
    context: &Context,
    concrete_term: &Term<'_>,
    expected_ty: &domain::RcType,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    log::trace!("checking term:\t\t{}", concrete_term);

    match concrete_term {
        Term::Parens(_, concrete_term) => check_term(context, concrete_term, expected_ty),
        Term::Let(_, concrete_items, concrete_body) => {
            let mut context = context.clone();
            let items = check_items(&mut context, concrete_items)?;
            let body = check_term(&context, concrete_body, expected_ty)?;

            Ok(items.into_iter().rev().fold(body, |acc, item| {
                // TODO: other item fields?
                core::RcTerm::from(core::Term::Let(item.term, acc))
            }))
        },
        Term::If(_, condition, consequent, alternative) => {
            let bool_ty = domain::RcValue::from(domain::Value::LiteralType(LiteralType::Bool));
            let condition = check_term(context, condition, &bool_ty)?;
            let consequent = check_term(context, consequent, expected_ty)?;
            let alternative = {
                let mut inner_context = context.clone();
                inner_context.local_bind(None, bool_ty);
                check_term(&inner_context, alternative, expected_ty)?
            };

            Ok(core::RcTerm::from(core::Term::LiteralElim(
                condition,
                Rc::from(vec![(LiteralIntro::Bool(true), consequent)]),
                alternative,
            )))
        },

        Term::Literal(concrete_literal) => literal::check(context, concrete_literal, expected_ty),

        Term::FunIntro(_, concrete_params, concrete_body) => {
            let clause = Clause::new(concrete_params, None, concrete_body);
            clause::check_clause(context, clause, expected_ty)
        },

        Term::RecordIntro(span, concrete_intro_fields) => {
            let mut context = context.clone();
            let mut fields = Vec::new();
            let mut expected_ty = expected_ty.clone();

            for concrete_intro_field in concrete_intro_fields {
                let (expected_label, expected_term_ty, rest) = match expected_ty.as_ref() {
                    domain::Value::RecordTypeExtend(label, ty, rest) => Ok((label, ty, rest)),
                    _ => Err(Diagnostic::new_error("too many fields found")
                        .with_label(DiagnosticLabel::new_primary(*span))),
                }?;

                let (found_label, params, body_ty, body) = concrete_intro_field.desugar();

                if found_label.slice == expected_label.0 {
                    let clause = Clause::new(params, body_ty, &body);
                    let term = clause::check_clause(&context, clause, expected_term_ty)?;

                    let term_value = context.eval(body.span(), &term)?;
                    let term_ty = expected_term_ty.clone();

                    fields.push((expected_label.clone(), term));
                    context.local_define(found_label.to_string(), term_value.clone(), term_ty);
                    expected_ty = do_closure_app(&rest, term_value)?;
                } else {
                    return Err(Diagnostic::new_error("field not found").with_label(
                        DiagnosticLabel::new_primary(found_label.span()).with_message(format!(
                            "expected `{}`, but found `{}`",
                            found_label, expected_label,
                        )),
                    ));
                }
            }

            if let domain::Value::RecordTypeEmpty = expected_ty.as_ref() {
                Ok(core::RcTerm::from(core::Term::RecordIntro(fields)))
            } else {
                Err(Diagnostic::new_error("not enough fields provided")
                    .with_label(DiagnosticLabel::new_primary(*span)))
            }
        },

        _ => {
            let (synth, synth_ty) = synth_term(context, concrete_term)?;
            context.expect_subtype(concrete_term.span(), &synth_ty, expected_ty)?;
            Ok(synth)
        },
    }
}

/// Synthesize the type of the given term.
///
/// Returns the elaborated term and its synthesized type.
pub fn synth_term(
    context: &Context,
    concrete_term: &Term<'_>,
) -> Result<(core::RcTerm, domain::RcType), Diagnostic<FileSpan>> {
    use std::cmp;

    log::trace!("synthesizing term:\t\t{}", concrete_term);

    match concrete_term {
        Term::Var(name) => match context.lookup_binder(&name.slice) {
            None => Err(Diagnostic::new_error("unbound variable")
                .with_label(DiagnosticLabel::new_primary(name.span()))),
            Some((index, ann)) => Ok((core::RcTerm::from(core::Term::Var(index)), ann.clone())),
        },
        Term::Hole(span) => Err(Diagnostic::new_error("ambiguous term").with_label(
            DiagnosticLabel::new_primary(*span).with_message("type annotations needed here"),
        )),

        Term::Parens(_, concrete_term) => synth_term(context, concrete_term),
        Term::Ann(concrete_term, concrete_term_ty) => {
            let (term_ty, _) = synth_universe(context, concrete_term_ty)?;
            let term_ty = context.eval(concrete_term_ty.span(), &term_ty)?;
            let term = check_term(context, concrete_term, &term_ty)?;
            Ok((term, term_ty))
        },
        Term::Let(_, concrete_items, concrete_body) => {
            let mut context = context.clone();
            let items = check_items(&mut context, concrete_items)?;
            let (body, body_ty) = synth_term(&context, concrete_body)?;

            Ok((
                items.into_iter().rev().fold(body, |acc, item| {
                    // TODO: other item fields?
                    core::RcTerm::from(core::Term::Let(item.term, acc))
                }),
                body_ty,
            ))
        },
        Term::If(span, _, _, _) => Err(Diagnostic::new_error("ambiguous term").with_label(
            DiagnosticLabel::new_primary(*span).with_message("type annotations needed here"),
        )),

        Term::Literal(concrete_literal) => literal::synth(concrete_literal),

        Term::FunType(_, concrete_params, concrete_body_ty) => {
            let mut context = context.clone();
            let mut param_tys = Vec::new();
            let mut max_level = UniverseLevel(0);

            for param in concrete_params {
                match param {
                    TypeParam::Explicit(_, param_names, concrete_param_ty) => {
                        for param_name in param_names {
                            let app_mode = AppMode::Explicit;
                            let param_ty_span = concrete_param_ty.span();
                            let (param_ty, level) = synth_universe(&context, concrete_param_ty)?;
                            let param_ty_value = context.eval(param_ty_span, &param_ty)?;

                            context.local_bind(param_name.to_string(), param_ty_value);
                            param_tys.push((app_mode, param_ty));
                            max_level = cmp::max(max_level, level);
                        }
                    },
                    TypeParam::Implicit(param_span, param_labels, concrete_param_ty) => {
                        let concrete_param_ty = concrete_param_ty.as_ref().ok_or_else(|| {
                            Diagnostic::new_error("implicit parameter is missing a type parameter")
                                .with_label(DiagnosticLabel::new_primary(*param_span).with_message(
                                    "inference of parameter annotations is not yet supported",
                                ))
                        })?;

                        for param_label in param_labels {
                            let app_mode = AppMode::Implicit(Label(param_label.to_string()));
                            let param_ty_span = concrete_param_ty.span();
                            let (param_ty, level) = synth_universe(&context, concrete_param_ty)?;
                            let param_ty_value = context.eval(param_ty_span, &param_ty)?;

                            context.local_bind(param_label.to_string(), param_ty_value);
                            param_tys.push((app_mode, param_ty));
                            max_level = cmp::max(max_level, level);
                        }
                    },
                    TypeParam::Instance(_, param_label, concrete_param_ty) => {
                        let app_mode = AppMode::Instance(Label(param_label.to_string()));
                        let param_ty_span = concrete_param_ty.span();
                        let (param_ty, level) = synth_universe(&context, concrete_param_ty)?;
                        let param_ty_value = context.eval(param_ty_span, &param_ty)?;

                        context.local_bind(param_label.to_string(), param_ty_value);
                        param_tys.push((app_mode, param_ty));
                        max_level = cmp::max(max_level, level);
                    },
                }
            }

            let (body_ty, body_level) = synth_universe(&context, concrete_body_ty)?;
            max_level = cmp::max(max_level, body_level);

            Ok((
                param_tys
                    .into_iter()
                    .rev()
                    .fold(body_ty, |acc, (app_mode, param_ty)| {
                        core::RcTerm::from(core::Term::FunType(app_mode, param_ty, acc))
                    }),
                domain::RcValue::from(domain::Value::Universe(max_level)),
            ))
        },
        Term::FunArrowType(concrete_param_ty, concrete_body_ty) => {
            let (param_ty, param_level) = synth_universe(context, concrete_param_ty)?;
            let param_ty_value = context.eval(concrete_param_ty.span(), &param_ty)?;
            let (body_ty, body_level) = {
                let mut context = context.clone();
                context.local_bind(None, param_ty_value);
                synth_universe(&context, concrete_body_ty)?
            };

            Ok((
                core::RcTerm::from(core::Term::FunType(AppMode::Explicit, param_ty, body_ty)),
                domain::RcValue::from(domain::Value::Universe(cmp::max(param_level, body_level))),
            ))
        },
        Term::FunIntro(_, concrete_params, concrete_body) => {
            let clause = Clause::new(concrete_params, None, concrete_body);
            clause::synth_clause(context, clause)
        },
        Term::FunElim(concrete_fun, concrete_args) => {
            let (mut fun, mut fun_ty) = synth_term(context, concrete_fun)?;
            for concrete_arg in concrete_args {
                let (ty_app_mode, param_ty, body_ty) = match fun_ty.as_ref() {
                    domain::Value::FunType(ty_app_mode, param_ty, body_ty) => {
                        Ok((ty_app_mode, param_ty, body_ty))
                    },
                    _ => Err(Diagnostic::new_error("expected a function").with_label(
                        DiagnosticLabel::new_primary(concrete_fun.span())
                            .with_message(format!("found: {}", context.read_back(None, &fun_ty)?)),
                    )),
                }?;

                let concrete_arg = check_arg_app_mode(concrete_arg, ty_app_mode)?;
                let arg = check_term(context, concrete_arg.as_ref(), param_ty)?;
                let arg_value = context.eval(concrete_arg.span(), &arg)?;

                fun = core::RcTerm::from(core::Term::FunElim(fun, ty_app_mode.clone(), arg));
                fun_ty = do_closure_app(body_ty, arg_value)?;
            }

            Ok((fun, fun_ty))
        },

        Term::RecordType(_, concrete_ty_fields) => {
            let mut context = context.clone();
            let mut max_level = UniverseLevel(0);

            let ty_fields = concrete_ty_fields
                .iter()
                .map(|concrete_ty_field| {
                    let docs = docs::concat(&concrete_ty_field.docs);
                    let (ty, ty_level) = synth_universe(&context, &concrete_ty_field.ann)?;
                    let ty_value = context.eval(concrete_ty_field.ann.span(), &ty)?;

                    context.local_bind(concrete_ty_field.label.to_string(), ty_value);
                    max_level = cmp::max(max_level, ty_level);

                    Ok((docs, Label(concrete_ty_field.label.to_string()), ty))
                })
                .collect::<Result<_, Diagnostic<FileSpan>>>()?;

            Ok((
                core::RcTerm::from(core::Term::RecordType(ty_fields)),
                domain::RcValue::from(domain::Value::Universe(max_level)),
            ))
        },
        Term::RecordIntro(span, intro_fields) => {
            if intro_fields.is_empty() {
                Ok((
                    core::RcTerm::from(core::Term::RecordIntro(Vec::new())),
                    domain::RcValue::from(domain::Value::RecordTypeEmpty),
                ))
            } else {
                Err(Diagnostic::new_error("ambiguous term").with_label(
                    DiagnosticLabel::new_primary(*span)
                        .with_message("type annotations needed here"),
                ))
            }
        },
        Term::RecordElim(concrete_record, label) => {
            let (record, mut record_ty) = synth_term(context, concrete_record)?;

            while let domain::Value::RecordTypeExtend(current_label, current_ty, rest) =
                record_ty.as_ref()
            {
                let expr = core::RcTerm::from(core::Term::RecordElim(
                    record.clone(),
                    current_label.clone(),
                ));

                if current_label.0 == label.slice {
                    return Ok((expr, current_ty.clone()));
                } else {
                    let expr = context.eval(None, &expr)?;
                    record_ty = do_closure_app(rest, expr)?;
                }
            }

            let message = format!("field not found: `{}`", label);
            Err(Diagnostic::new_error(message)
                .with_label(DiagnosticLabel::new_primary(label.span())))
        },

        Term::Universe(_, level) => {
            let level = match level {
                None => UniverseLevel(0),
                Some((_, level)) => UniverseLevel(*level),
            };

            Ok((
                core::RcTerm::from(core::Term::Universe(level)),
                domain::RcValue::from(domain::Value::Universe(level + 1)),
            ))
        },
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn local_binds() {
        use mltt_core::syntax::domain::{RcValue, Value};

        let mut context = Context::new();

        let ty1 = RcValue::from(Value::Universe(UniverseLevel(0)));
        let ty2 = RcValue::from(Value::Universe(UniverseLevel(1)));
        let ty3 = RcValue::from(Value::Universe(UniverseLevel(2)));

        let param1 = context.local_bind("x".to_owned(), ty1.clone());
        let param2 = context.local_bind("y".to_owned(), ty2.clone());
        let param3 = context.local_bind("z".to_owned(), ty3.clone());

        assert_eq!(param1, RcValue::from(Value::var(VarLevel(0))));
        assert_eq!(param2, RcValue::from(Value::var(VarLevel(1))));
        assert_eq!(param3, RcValue::from(Value::var(VarLevel(2))));

        assert_eq!(context.lookup_binder("x").unwrap().1, &ty1);
        assert_eq!(context.lookup_binder("y").unwrap().1, &ty2);
        assert_eq!(context.lookup_binder("z").unwrap().1, &ty3);
    }

    #[test]
    fn local_binds_shadow() {
        use mltt_core::syntax::domain::{RcValue, Value};

        let mut context = Context::new();

        let ty1 = RcValue::from(Value::Universe(UniverseLevel(0)));
        let ty2 = RcValue::from(Value::Universe(UniverseLevel(1)));
        let ty3 = RcValue::from(Value::Universe(UniverseLevel(2)));

        let param1 = context.local_bind("x".to_owned(), ty1.clone());
        let param2 = context.local_bind("x".to_owned(), ty2.clone());
        let param3 = context.local_bind("x".to_owned(), ty3.clone());

        assert_eq!(param1, RcValue::from(Value::var(VarLevel(0))));
        assert_eq!(param2, RcValue::from(Value::var(VarLevel(1))));
        assert_eq!(param3, RcValue::from(Value::var(VarLevel(2))));

        assert_eq!(context.lookup_binder("x").unwrap().1, &ty3);
    }

    #[test]
    fn local_binds_fresh() {
        use mltt_core::syntax::domain::{RcValue, Value};

        let mut context = Context::new();

        let ty1 = RcValue::from(Value::Universe(UniverseLevel(0)));
        let ty2 = RcValue::from(Value::Universe(UniverseLevel(1)));
        let ty3 = RcValue::from(Value::Universe(UniverseLevel(2)));

        let param1 = context.local_bind("x".to_owned(), ty1.clone());
        let param2 = context.local_bind(None, ty2.clone());
        let param3 = context.local_bind(None, ty3.clone());

        assert_eq!(param1, RcValue::from(Value::var(VarLevel(0))));
        assert_eq!(param2, RcValue::from(Value::var(VarLevel(1))));
        assert_eq!(param3, RcValue::from(Value::var(VarLevel(2))));

        assert_eq!(context.lookup_binder("x").unwrap().1, &ty1);
    }
}
