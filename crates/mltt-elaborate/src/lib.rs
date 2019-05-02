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
use mltt_concrete::{Arg, Item, SpannedString, Term, TypeParam};
use mltt_core::literal::{LiteralIntro, LiteralType};
use mltt_core::{domain, meta, prim, syntax, var, AppMode, DocString, Label, UniverseLevel};
use mltt_span::FileSpan;
use std::borrow::Cow;
use std::rc::Rc;

use crate::clause::{CaseClause, Clause};

mod clause;
mod literal;
mod nbe;

/// Local elaboration context.
#[derive(Debug, Clone)]
pub struct Context {
    /// Primitive entries.
    prims: prim::Env,
    /// Values to be used during evaluation.
    values: var::Env<domain::RcValue>,
    /// Types of the entries in the context.
    tys: var::Env<domain::RcType>,
    /// A mapping from the user-defined names to the level in which they were
    /// bound.
    ///
    /// We associate levels to the binder names so that we can recover the
    /// correct debruijn index once we reach a variable name in a nested scope.
    /// Not all entries in the context will have a corresponding name - for
    /// example we don't define a name for non-dependent function types.
    names: im::HashMap<String, var::Level>,
    /// Local bound levels.
    ///
    /// This is used for making spines for fresh metas.
    bound_levels: im::Vector<var::Level>,
}

impl Context {
    /// Create a new, empty context.
    pub fn new() -> Context {
        Context {
            prims: prim::Env::new(),
            values: var::Env::new(),
            tys: var::Env::new(),
            names: im::HashMap::new(),
            bound_levels: im::Vector::new(),
        }
    }

    /// Primitive entries.
    pub fn prims(&self) -> &prim::Env {
        &self.prims
    }

    /// Values to be used during evaluation.
    pub fn values(&self) -> &var::Env<domain::RcValue> {
        &self.values
    }

    /// Add a fresh definition to the context.
    pub fn add_fresh_defn(&mut self, value: domain::RcValue, ty: domain::RcType) {
        log::trace!("add fresh definition");

        self.values.add_entry(value);
        self.tys.add_entry(ty);
    }

    /// Add a definition to the context.
    pub fn add_defn(
        &mut self,
        name: impl Into<String>,
        value: domain::RcValue,
        ty: domain::RcType,
    ) {
        let name = name.into();
        log::trace!("add definition: {}", name);

        let var_level = self.values.size().next_level();
        self.names.insert(name, var_level);
        self.values.add_entry(value);
        self.tys.add_entry(ty);
    }

    /// Add a fresh parameter the context, returning a variable that points to
    /// the introduced binder.
    pub fn add_fresh_param(&mut self, ty: domain::RcType) -> domain::RcValue {
        log::trace!("add fresh parameter");

        let var_level = self.values.size().next_level();
        let value = domain::RcValue::var(var_level);
        self.values.add_entry(value.clone());
        self.tys.add_entry(ty);
        value
    }

    /// Add a parameter the context, returning a variable that points to
    /// the introduced binder.
    pub fn add_param(&mut self, name: impl Into<String>, ty: domain::RcType) -> domain::RcValue {
        let name = name.into();
        log::trace!("add parameter: {}", name);

        let var_level = self.values.size().next_level();
        self.names.insert(name, var_level);
        let value = domain::RcValue::var(var_level);
        self.values.add_entry(value.clone());
        self.tys.add_entry(ty);
        value
    }

    /// Create a fresh meta and return the meta applied to all of the currently
    /// bound vars.
    fn new_meta(&self, metas: &mut meta::Env<domain::RcValue>, span: FileSpan) -> syntax::RcTerm {
        let args = self.bound_levels.iter().map(|var_level| {
            let var_index = self.values().size().index(*var_level);
            syntax::RcTerm::var(var_index)
        });

        args.fold(
            syntax::RcTerm::from(syntax::Term::Meta(metas.add_unsolved(span))),
            |acc, arg| syntax::RcTerm::from(syntax::Term::FunElim(acc, AppMode::Explicit, arg)),
        )
    }

    /// Lookup the de-bruijn index and the type annotation of a binder in the
    /// context using a user-defined name.
    pub fn lookup_binder(&self, name: &str) -> Option<(var::Index, &domain::RcType)> {
        let var_level = self.names.get(name)?;
        let var_index = self.values().size().index(*var_level);
        let ty = self.tys.lookup_entry(var_index)?;
        log::trace!("lookup binder: {} -> {}", name, var_index);
        Some((var_index, ty))
    }

    /// Apply a closure to an argument.
    pub fn app_closure(
        &self,
        metas: &meta::Env<domain::RcValue>,
        closure: &domain::AppClosure,
        arg: domain::RcValue,
    ) -> Result<domain::RcValue, Diagnostic<FileSpan>> {
        nbe::app_closure(self.prims(), metas, closure, arg)
    }

    /// Evaluate a term using the evaluation environment
    pub fn eval_term(
        &self,
        metas: &meta::Env<domain::RcValue>,
        span: impl Into<Option<FileSpan>>,
        term: &syntax::RcTerm,
    ) -> Result<domain::RcValue, Diagnostic<FileSpan>> {
        nbe::eval_term(self.prims(), metas, self.values(), span, term)
    }

    /// Read a value back into the core syntax, normalizing as required.
    pub fn read_back_value(
        &self,
        metas: &meta::Env<domain::RcValue>,
        span: impl Into<Option<FileSpan>>,
        value: &domain::RcValue,
    ) -> Result<syntax::RcTerm, Diagnostic<FileSpan>> {
        nbe::read_back_value(self.prims(), metas, self.values().size(), span, value)
    }

    /// Fully normalize a term by first evaluating it, then reading it back.
    pub fn normalize_term(
        &self,
        metas: &meta::Env<domain::RcValue>,
        span: impl Into<Option<FileSpan>>,
        term: &syntax::RcTerm,
    ) -> Result<syntax::RcTerm, Diagnostic<FileSpan>> {
        nbe::normalize_term(self.prims(), metas, self.values(), span, term)
    }

    /// Expect that `ty1` is a subtype of `ty2` in the current context.
    pub fn check_subtype(
        &self,
        metas: &meta::Env<domain::RcValue>,
        span: FileSpan,
        ty1: &domain::RcType,
        ty2: &domain::RcType,
    ) -> Result<(), Diagnostic<FileSpan>> {
        nbe::check_subtype(self.prims(), metas, self.values().size(), span, ty1, ty2)
    }
}

impl Default for Context {
    fn default() -> Context {
        use mltt_core::domain::RcValue;
        use mltt_core::literal::LiteralType as LitType;

        let mut context = Context::new();
        let u0 = RcValue::universe(0);
        let bool = RcValue::literal_ty(LitType::Bool);

        context.add_defn("String", RcValue::literal_ty(LitType::String), u0.clone());
        context.add_defn("Char", RcValue::literal_ty(LitType::Char), u0.clone());
        context.add_defn("Bool", bool.clone(), u0.clone());
        context.add_defn("true", RcValue::literal_intro(true), bool.clone());
        context.add_defn("false", RcValue::literal_intro(false), bool.clone());
        context.add_defn("U8", RcValue::literal_ty(LitType::U8), u0.clone());
        context.add_defn("U16", RcValue::literal_ty(LitType::U16), u0.clone());
        context.add_defn("U32", RcValue::literal_ty(LitType::U32), u0.clone());
        context.add_defn("U64", RcValue::literal_ty(LitType::U64), u0.clone());
        context.add_defn("S8", RcValue::literal_ty(LitType::S8), u0.clone());
        context.add_defn("S16", RcValue::literal_ty(LitType::S16), u0.clone());
        context.add_defn("S32", RcValue::literal_ty(LitType::S32), u0.clone());
        context.add_defn("S64", RcValue::literal_ty(LitType::S64), u0.clone());
        context.add_defn("F32", RcValue::literal_ty(LitType::F32), u0.clone());
        context.add_defn("F64", RcValue::literal_ty(LitType::F64), u0.clone());

        context.prims = prim::Env::default();

        context
    }
}

/// Check that this is a valid module.
///
/// Returns the elaborated items.
pub fn check_module(
    context: &Context,
    metas: &mut meta::Env<domain::RcValue>,
    concrete_items: &[Item<'_>],
) -> Result<syntax::Module, Diagnostic<FileSpan>> {
    // The local elaboration context
    let mut context = context.clone();
    let items = check_items(&mut context, metas, concrete_items)?;

    Ok(syntax::Module { items })
}

/// Concatenate a bunch of lines of documentation into a single string, removing
/// comment prefixes if they are found.
fn concat_docs(doc_lines: &[SpannedString<'_>]) -> DocString {
    let mut doc = String::new();
    for doc_line in doc_lines {
        // Strip the `||| ` or `|||` prefix left over from tokenization
        // We assume that each line of documentation has a trailing new line
        doc.push_str(match doc_line.slice {
            doc_line if doc_line.starts_with("||| ") => &doc_line["||| ".len()..],
            doc_line if doc_line.starts_with("|||") => &doc_line["|||".len()..],
            doc_line => &doc_line[..],
        });
    }
    DocString::from(doc)
}

/// Check the given items and add them to the context.
///
/// Returns the elaborated items.
fn check_items(
    context: &mut Context,
    metas: &mut meta::Env<domain::RcValue>,
    concrete_items: &[Item<'_>],
) -> Result<Vec<syntax::Item>, Diagnostic<FileSpan>> {
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
                        let docs = concat_docs(&declaration.docs);
                        let label = Label(label.to_owned());
                        let (body_ty, _) = synth_universe(&context, metas, &concrete_body_ty)?;
                        // Ensure that we evaluate the forward declaration in
                        // the current context - if we wait until later more
                        // definitions might have come in to scope!
                        let body_ty_value =
                            context.eval_term(metas, concrete_body_ty.span(), &body_ty)?;

                        log::trace!("elaborated declaration:\t{}\t: {}", label, body_ty);

                        core_items.push(syntax::Item::Declaration(docs, label, body_ty));
                        entry.insert(Some(body_ty_value));
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

                let (term, term_span, ty) = match forward_declarations.entry(label) {
                    // No prior declaration was found, so we'll try synthesizing
                    // its type instead
                    Entry::Vacant(entry) => {
                        let clause = Clause::new(params, body_ty, body);
                        let (term, ty) = clause::synth_clause(&context, metas, clause)?;

                        entry.insert(None);

                        (term, body.span(), ty)
                    },
                    // Something has happened with this declaration, let's
                    // 'take' a look!
                    Entry::Occupied(mut entry) => match entry.get_mut().take() {
                        // We found a prior declaration, so we'll use it as a
                        // basis for checking the definition
                        Some(ty) => {
                            let clause = Clause::new(params, body_ty, body);
                            let term = clause::check_clause(&context, metas, clause, &ty)?;

                            (term, body.span(), ty)
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

                log::trace!("elaborated definition:\t{}\t= {}", label, term);

                let label = Label(label.to_owned());
                let docs = concat_docs(&definition.docs);
                let value = context.eval_term(metas, term_span, &term)?;

                context.add_defn(label.to_string(), value, ty);
                core_items.push(syntax::Item::Definition(docs, label, term));
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
    metas: &mut meta::Env<domain::RcValue>,
    concrete_term: &Term<'_>,
) -> Result<(syntax::RcTerm, UniverseLevel), Diagnostic<FileSpan>> {
    let (term, ty) = synth_term(context, metas, concrete_term)?;
    match ty.as_ref() {
        domain::Value::Universe(level) => Ok((term, *level)),
        _ => Err(Diagnostic::new_error("type expected").with_label(
            DiagnosticLabel::new_primary(concrete_term.span()).with_message(format!(
                "found `{}`",
                context.read_back_value(metas, None, &ty)?
            )),
        )),
    }
}

/// Check that a given term conforms to an expected type.
///
/// Returns the elaborated term.
pub fn check_term(
    context: &Context,
    metas: &mut meta::Env<domain::RcValue>,
    concrete_term: &Term<'_>,
    expected_ty: &domain::RcType,
) -> Result<syntax::RcTerm, Diagnostic<FileSpan>> {
    log::trace!("checking term:\t\t{}", concrete_term);

    match concrete_term {
        Term::Prim(_, name) => {
            let prim_name = prim::Name(literal::parse_string(name)?);
            match context.prims().lookup_entry(&prim_name) {
                None => Err(Diagnostic::new_error("unknown primitive")
                    .with_label(DiagnosticLabel::new_primary(name.span()))),
                Some(_) => Ok(syntax::RcTerm::prim(prim_name)),
            }
        },
        Term::Hole(span) => Ok(context.new_meta(metas, *span)),
        Term::Parens(_, concrete_term) => check_term(context, metas, concrete_term, expected_ty),
        Term::Let(_, concrete_items, concrete_body) => {
            let mut context = context.clone();
            let items = check_items(&mut context, metas, concrete_items)?;
            let body = check_term(&context, metas, concrete_body, expected_ty)?;

            Ok(syntax::RcTerm::from(syntax::Term::Let(items, body)))
        },
        Term::If(_, condition, consequent, alternative) => {
            let bool_ty = domain::RcValue::literal_ty(LiteralType::Bool);
            let condition = check_term(context, metas, condition, &bool_ty)?;
            let consequent = check_term(context, metas, consequent, expected_ty)?;
            let alternative = check_term(context, metas, alternative, expected_ty)?;

            Ok(syntax::RcTerm::from(syntax::Term::LiteralElim(
                condition,
                Rc::from(vec![(LiteralIntro::Bool(true), consequent)]),
                alternative,
            )))
        },
        Term::Case(span, scrutinee, clauses) => {
            let clauses = clauses
                .iter()
                .map(|(pattern, body)| CaseClause::new(pattern, body))
                .collect();

            clause::check_case(context, metas, *span, scrutinee, clauses, expected_ty)
        },

        Term::LiteralIntro(kind, literal) => {
            let literal_intro = literal::check(context, metas, *kind, literal, expected_ty)?;
            Ok(syntax::RcTerm::literal_intro(literal_intro))
        },

        Term::FunIntro(_, concrete_params, concrete_body) => {
            let clause = Clause::new(concrete_params, None, concrete_body);
            clause::check_clause(context, metas, clause, expected_ty)
        },

        Term::RecordIntro(span, concrete_intro_fields) => {
            let mut context = context.clone();
            let mut fields = Vec::new();
            let mut expected_ty = expected_ty.clone();

            for concrete_intro_field in concrete_intro_fields {
                let (expected_label, expected_term_ty, rest) = match expected_ty.as_ref() {
                    domain::Value::RecordTypeExtend(_, label, ty, rest) => Ok((label, ty, rest)),
                    _ => Err(Diagnostic::new_error("too many fields found")
                        .with_label(DiagnosticLabel::new_primary(*span))),
                }?;

                let (found_label, params, body_ty, body) = concrete_intro_field.desugar();

                if found_label.slice == expected_label.0 {
                    let clause = Clause::new(params, body_ty, &body);
                    let term = clause::check_clause(&context, metas, clause, expected_term_ty)?;

                    let term_value = context.eval_term(metas, body.span(), &term)?;
                    let term_ty = expected_term_ty.clone();

                    fields.push((expected_label.clone(), term));
                    context.add_defn(found_label, term_value.clone(), term_ty);
                    expected_ty = context.app_closure(metas, &rest, term_value)?;
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
                Ok(syntax::RcTerm::from(syntax::Term::RecordIntro(fields)))
            } else {
                Err(Diagnostic::new_error("not enough fields provided")
                    .with_label(DiagnosticLabel::new_primary(*span)))
            }
        },

        _ => {
            let (synth, synth_ty) = synth_term(context, metas, concrete_term)?;
            context.check_subtype(metas, concrete_term.span(), &synth_ty, expected_ty)?;
            Ok(synth)
        },
    }
}

/// Synthesize the type of the given term.
///
/// Returns the elaborated term and its synthesized type.
pub fn synth_term(
    context: &Context,
    metas: &mut meta::Env<domain::RcValue>,
    concrete_term: &Term<'_>,
) -> Result<(syntax::RcTerm, domain::RcType), Diagnostic<FileSpan>> {
    use std::cmp;

    log::trace!("synthesizing term:\t\t{}", concrete_term);

    match concrete_term {
        Term::Var(name) => match context.lookup_binder(name.slice) {
            None => Err(Diagnostic::new_error("unbound variable")
                .with_label(DiagnosticLabel::new_primary(name.span()))),
            Some((index, ann)) => Ok((syntax::RcTerm::var(index), ann.clone())),
        },
        Term::Prim(span, name) => match context
            .prims()
            .lookup_entry(&prim::Name(literal::parse_string(name)?))
        {
            None => Err(Diagnostic::new_error("unknown primitive")
                .with_label(DiagnosticLabel::new_primary(name.span()))),
            Some(_) => Err(Diagnostic::new_error("ambiguous primitive").with_label(
                DiagnosticLabel::new_primary(*span).with_message("type annotations needed here"),
            )),
        },
        Term::Hole(span) => {
            let term = context.new_meta(metas, *span);
            let ty = context.new_meta(metas, *span);
            Ok((term, context.eval_term(metas, None, &ty)?))
        },

        Term::Parens(_, concrete_term) => synth_term(context, metas, concrete_term),
        Term::Ann(concrete_term, concrete_term_ty) => {
            let (term_ty, _) = synth_universe(context, metas, concrete_term_ty)?;
            let term_ty_value = context.eval_term(metas, concrete_term_ty.span(), &term_ty)?;
            let term = check_term(context, metas, concrete_term, &term_ty_value)?;

            Ok((
                syntax::RcTerm::from(syntax::Term::Ann(term, term_ty)),
                term_ty_value,
            ))
        },
        Term::Let(_, concrete_items, concrete_body) => {
            let mut context = context.clone();
            let items = check_items(&mut context, metas, concrete_items)?;
            let (body, body_ty) = synth_term(&context, metas, concrete_body)?;

            Ok((
                syntax::RcTerm::from(syntax::Term::Let(items, body)),
                body_ty,
            ))
        },
        Term::If(span, _, _, _) => Err(Diagnostic::new_error("ambiguous term").with_label(
            DiagnosticLabel::new_primary(*span).with_message("type annotations needed here"),
        )),
        Term::Case(span, _, _) => Err(Diagnostic::new_error("ambiguous term").with_label(
            DiagnosticLabel::new_primary(*span).with_message("type annotations needed here"),
        )),

        Term::LiteralIntro(kind, literal) => {
            let (literal_intro, ty) = literal::synth(*kind, literal)?;
            let term = syntax::RcTerm::literal_intro(literal_intro);

            Ok((term, ty))
        },

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
                            let (param_ty, level) =
                                synth_universe(&context, metas, concrete_param_ty)?;
                            let param_ty_value =
                                context.eval_term(metas, param_ty_span, &param_ty)?;

                            context.add_param(param_name, param_ty_value);
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
                            let (param_ty, level) =
                                synth_universe(&context, metas, concrete_param_ty)?;
                            let param_ty_value =
                                context.eval_term(metas, param_ty_span, &param_ty)?;

                            context.add_param(param_label, param_ty_value);
                            param_tys.push((app_mode, param_ty));
                            max_level = cmp::max(max_level, level);
                        }
                    },
                    TypeParam::Instance(_, param_label, concrete_param_ty) => {
                        let app_mode = AppMode::Instance(Label(param_label.to_string()));
                        let param_ty_span = concrete_param_ty.span();
                        let (param_ty, level) = synth_universe(&context, metas, concrete_param_ty)?;
                        let param_ty_value = context.eval_term(metas, param_ty_span, &param_ty)?;

                        context.add_param(param_label, param_ty_value);
                        param_tys.push((app_mode, param_ty));
                        max_level = cmp::max(max_level, level);
                    },
                }
            }

            let (body_ty, body_level) = synth_universe(&context, metas, concrete_body_ty)?;
            max_level = cmp::max(max_level, body_level);

            Ok((
                param_tys
                    .into_iter()
                    .rev()
                    .fold(body_ty, |acc, (app_mode, param_ty)| {
                        syntax::RcTerm::from(syntax::Term::FunType(app_mode, param_ty, acc))
                    }),
                domain::RcValue::universe(max_level),
            ))
        },
        Term::FunArrowType(concrete_param_ty, concrete_body_ty) => {
            let (param_ty, param_level) = synth_universe(context, metas, concrete_param_ty)?;
            let (body_ty, body_level) = {
                let mut context = context.clone();
                let param_ty = context.eval_term(metas, concrete_param_ty.span(), &param_ty)?;
                context.add_fresh_param(param_ty);
                synth_universe(&context, metas, concrete_body_ty)?
            };

            Ok((
                syntax::RcTerm::from(syntax::Term::FunType(AppMode::Explicit, param_ty, body_ty)),
                domain::RcValue::universe(cmp::max(param_level, body_level)),
            ))
        },
        Term::FunIntro(_, concrete_params, concrete_body) => {
            let clause = Clause::new(concrete_params, None, concrete_body);
            clause::synth_clause(context, metas, clause)
        },
        Term::FunElim(concrete_fun, concrete_args) => {
            let (mut fun, mut fun_ty) = synth_term(context, metas, concrete_fun)?;
            for concrete_arg in concrete_args {
                let (ty_app_mode, param_ty, body_ty) = match fun_ty.as_ref() {
                    domain::Value::FunType(ty_app_mode, param_ty, body_ty) => {
                        Ok((ty_app_mode, param_ty, body_ty))
                    },
                    _ => Err(Diagnostic::new_error("expected a function").with_label(
                        DiagnosticLabel::new_primary(concrete_fun.span()).with_message(format!(
                            "found: {}",
                            context.read_back_value(metas, None, &fun_ty)?
                        )),
                    )),
                }?;

                let concrete_arg = check_arg_app_mode(concrete_arg, ty_app_mode)?;
                let arg = check_term(context, metas, concrete_arg.as_ref(), param_ty)?;
                let arg_value = context.eval_term(metas, concrete_arg.span(), &arg)?;

                fun = syntax::RcTerm::from(syntax::Term::FunElim(fun, ty_app_mode.clone(), arg));
                fun_ty = context.app_closure(metas, body_ty, arg_value)?;
            }

            Ok((fun, fun_ty))
        },

        Term::RecordType(_, concrete_ty_fields) => {
            let mut context = context.clone();
            let mut max_level = UniverseLevel(0);

            let ty_fields = concrete_ty_fields
                .iter()
                .map(|concrete_ty_field| {
                    let docs = concat_docs(&concrete_ty_field.docs);
                    let (ty, ty_level) = synth_universe(&context, metas, &concrete_ty_field.ann)?;
                    let ty_value = context.eval_term(metas, concrete_ty_field.ann.span(), &ty)?;

                    context.add_param(concrete_ty_field.label, ty_value);
                    max_level = cmp::max(max_level, ty_level);

                    Ok((docs, Label(concrete_ty_field.label.to_string()), ty))
                })
                .collect::<Result<_, Diagnostic<FileSpan>>>()?;

            Ok((
                syntax::RcTerm::from(syntax::Term::RecordType(ty_fields)),
                domain::RcValue::universe(max_level),
            ))
        },
        Term::RecordIntro(span, intro_fields) => {
            if intro_fields.is_empty() {
                Ok((
                    syntax::RcTerm::from(syntax::Term::RecordIntro(Vec::new())),
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
            let (record, mut record_ty) = synth_term(context, metas, concrete_record)?;

            while let domain::Value::RecordTypeExtend(_, current_label, current_ty, rest) =
                record_ty.as_ref()
            {
                let expr = syntax::RcTerm::from(syntax::Term::RecordElim(
                    record.clone(),
                    current_label.clone(),
                ));

                if current_label.0 == label.slice {
                    return Ok((expr, current_ty.clone()));
                } else {
                    let expr = context.eval_term(metas, None, &expr)?;
                    record_ty = context.app_closure(metas, rest, expr)?;
                }
            }

            let message = format!("field not found: `{}`", label);
            Err(Diagnostic::new_error(message)
                .with_label(DiagnosticLabel::new_primary(label.span())))
        },

        Term::Universe(_, level) => {
            let level = match level {
                None => UniverseLevel(0),
                Some(level) => UniverseLevel(literal::parse_int(level)?),
            };

            Ok((
                syntax::RcTerm::universe(level),
                domain::RcValue::universe(level + 1),
            ))
        },
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn add_params() {
        use mltt_core::domain::{RcValue, Value};

        let mut context = Context::new();

        let ty1 = RcValue::universe(0);
        let ty2 = RcValue::universe(1);
        let ty3 = RcValue::universe(2);

        let param1 = context.add_param("x", ty1.clone());
        let param2 = context.add_param("y", ty2.clone());
        let param3 = context.add_param("z", ty3.clone());

        assert_eq!(param1, RcValue::from(Value::var(var::Level(0))));
        assert_eq!(param2, RcValue::from(Value::var(var::Level(1))));
        assert_eq!(param3, RcValue::from(Value::var(var::Level(2))));

        assert_eq!(context.lookup_binder("x").unwrap().1, &ty1);
        assert_eq!(context.lookup_binder("y").unwrap().1, &ty2);
        assert_eq!(context.lookup_binder("z").unwrap().1, &ty3);
    }

    #[test]
    fn add_params_shadow() {
        use mltt_core::domain::{RcValue, Value};

        let mut context = Context::new();

        let ty1 = RcValue::universe(0);
        let ty2 = RcValue::universe(1);
        let ty3 = RcValue::universe(2);

        let param1 = context.add_param("x", ty1.clone());
        let param2 = context.add_param("x", ty2.clone());
        let param3 = context.add_param("x", ty3.clone());

        assert_eq!(param1, RcValue::from(Value::var(var::Level(0))));
        assert_eq!(param2, RcValue::from(Value::var(var::Level(1))));
        assert_eq!(param3, RcValue::from(Value::var(var::Level(2))));

        assert_eq!(context.lookup_binder("x").unwrap().1, &ty3);
    }

    #[test]
    fn add_params_fresh() {
        use mltt_core::domain::{RcValue, Value};

        let mut context = Context::new();

        let ty1 = RcValue::universe(0);
        let ty2 = RcValue::universe(1);
        let ty3 = RcValue::universe(2);

        let param1 = context.add_param("x", ty1.clone());
        let param2 = context.add_fresh_param(ty2.clone());
        let param3 = context.add_fresh_param(ty3.clone());

        assert_eq!(param1, RcValue::from(Value::var(var::Level(0))));
        assert_eq!(param2, RcValue::from(Value::var(var::Level(1))));
        assert_eq!(param3, RcValue::from(Value::var(var::Level(2))));

        assert_eq!(context.lookup_binder("x").unwrap().1, &ty1);
    }
}
