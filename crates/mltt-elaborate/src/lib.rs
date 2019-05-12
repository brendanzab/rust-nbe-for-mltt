//! Elaboration of the MLTT language's concrete syntax into its core syntax.
//!
//! Performs the following:
//!
//! - name resolution
//! - desugaring
//! - pattern compilation (TODO)
//! - bidirectional type checking
//! - unification of metavariables

#![warn(rust_2018_idioms)]

use language_reporting::{Diagnostic, Label as DiagnosticLabel};
use mltt_concrete::{Arg, Item, SpannedString, Term, TypeParam};
use mltt_core::literal::{LiteralIntro, LiteralType};
use mltt_core::{domain, meta, prim, syntax, AppMode, DocString, Label, UniverseLevel};
use mltt_span::FileSpan;
use std::rc::Rc;

use crate::clause::{CaseClause, Clause};
pub use crate::context::Context;

mod clause;
mod context;
mod literal;
mod nbe;
mod unify;

/// Check that this is a valid module.
///
/// Returns the elaborated module.
pub fn check_module(
    context: &Context,
    metas: &mut meta::Env,
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
    metas: &mut meta::Env,
    concrete_items: &[Item<'_>],
) -> Result<Vec<syntax::Item>, Diagnostic<FileSpan>> {
    let mut decl_count = 0;
    let mut next_decl_index = || {
        let next_index = decl_count;
        decl_count += 1;
        syntax::DeclarationIndex(next_index)
    };

    // Declarations that may be waiting to be defined
    let mut forward_decls = im::HashMap::new();
    // The elaborated items
    let expected_defn_count = concrete_items.iter().filter(|i| i.is_definition()).count();
    let mut core_items = Vec::with_capacity(expected_defn_count);

    for concrete_item in concrete_items {
        use im::hashmap::Entry;

        match concrete_item {
            Item::Declaration(decl) => {
                let name = decl.name.slice;
                let concrete_body_ty = &decl.body_ty;

                log::trace!("checking declaration:\t\t{}\t: {}", name, concrete_body_ty);

                match forward_decls.entry(name) {
                    // No previous declaration for this name was seen, so we can
                    // go-ahead and type check, elaborate, and then add it to
                    // the context
                    Entry::Vacant(entry) => {
                        let docs = concat_docs(&decl.docs);
                        let (body_ty, _) = synth_universe(&context, metas, &concrete_body_ty)?;
                        // Ensure that we evaluate the forward declaration in
                        // the current context - if we wait until later more
                        // definitions might have come in to scope!
                        let body_ty_value =
                            context.eval_term(metas, concrete_body_ty.span(), &body_ty)?;

                        log::trace!("elaborated declaration:\t{}\t: {:?}", name, body_ty);

                        let name_hint = Some(name.to_owned());
                        core_items.push(syntax::Item::Declaration(docs, name_hint, body_ty));
                        entry.insert(Some((next_decl_index(), body_ty_value)));
                    },
                    // There's a declaration for this name already pending - we
                    // can't add a new one!
                    Entry::Occupied(_) => {
                        return Err(Diagnostic::new_error("already declared")
                            .with_label(DiagnosticLabel::new_primary(decl.name.span())));
                    },
                }
            },
            Item::Definition(defn) => {
                let name = defn.name.slice;
                let body_ty = defn.body_ty.as_ref();
                let body = &defn.body;

                log::trace!("checking definition:\t\t{}\t= {}", name, body);

                let (decl_index, term, term_span, term_ty) = match forward_decls.entry(name) {
                    // No prior declaration was found, so we'll try synthesizing
                    // its type instead
                    Entry::Vacant(entry) => {
                        let clause = Clause::new(&defn.params, body_ty, body);
                        let (term, term_ty) = clause::synth_clause(&context, metas, clause)?;

                        entry.insert(None);
                        next_decl_index();

                        (None, term, body.span(), term_ty)
                    },
                    // Something has happened with this declaration, let's
                    // 'take' a look!
                    Entry::Occupied(mut entry) => match entry.get_mut().take() {
                        // We found a prior declaration, so we'll use it as a
                        // basis for checking the definition
                        Some((decl_index, term_ty)) => {
                            let clause = Clause::new(&defn.params, body_ty, body);
                            let term = clause::check_clause(&context, metas, clause, &term_ty)?;

                            (Some(decl_index), term, body.span(), term_ty)
                        },
                        // This declaration was already given a definition, so
                        // this is an error!
                        //
                        // NOTE: Some languages (eg. Haskell, Agda, Idris, and
                        // Erlang) turn duplicate definitions into case matches.
                        // Languages like Elm don't. What should we do here?
                        None => {
                            return Err(Diagnostic::new_error("already defined")
                                .with_label(DiagnosticLabel::new_primary(defn.name.span())));
                        },
                    },
                };

                log::trace!("elaborated definition:\t{}\t= {:?}", name, term);

                let docs = concat_docs(&defn.docs);
                let name_hint = Some(name.to_owned());
                let value = context.eval_term(metas, term_span, &term)?;

                context.add_defn(name, value, term_ty);
                core_items.push(syntax::Item::Definition(docs, decl_index, name_hint, term));
            },
        }
    }

    Ok(core_items)
}

/// Ensures that the given term is a universe, returning the level of that
/// universe and its elaborated form.
fn synth_universe(
    context: &Context,
    metas: &mut meta::Env,
    concrete_term: &Term<'_>,
) -> Result<(Rc<syntax::Term>, UniverseLevel), Diagnostic<FileSpan>> {
    let (term, ty) = synth_term(MetaInsertion::Yes, context, metas, concrete_term)?;
    match ty.as_ref() {
        domain::Value::Universe(level) => Ok((term, *level)),
        _ => Err(Diagnostic::new_error("type expected").with_label(
            DiagnosticLabel::new_primary(concrete_term.span()).with_message(format!(
                "found `{}`",
                context.value_to_doc(metas, &ty).pretty(1000_000_000),
            )),
        )),
    }
}

/// Check that a given term conforms to an expected type.
///
/// Returns the elaborated term.
pub fn check_term(
    context: &Context,
    metas: &mut meta::Env,
    concrete_term: &Term<'_>,
    expected_ty: &Rc<domain::Type>,
) -> Result<Rc<syntax::Term>, Diagnostic<FileSpan>> {
    log::trace!("checking term:\t\t{}", concrete_term);

    match concrete_term {
        Term::Prim(_, name) => {
            let prim_name = prim::Name(literal::parse_string(name)?);
            match context.prims().lookup_entry(&prim_name) {
                None => Err(Diagnostic::new_error("unknown primitive")
                    .with_label(DiagnosticLabel::new_primary(name.span()))),
                Some(_) => Ok(Rc::from(syntax::Term::prim(prim_name))),
            }
        },
        Term::Hole(span) => Ok(context.new_meta(metas, *span, expected_ty.clone())),
        Term::Parens(_, concrete_term) => check_term(context, metas, concrete_term, expected_ty),
        Term::Let(_, concrete_items, concrete_body) => {
            let mut context = context.clone();
            let items = check_items(&mut context, metas, concrete_items)?;
            let body = check_term(&context, metas, concrete_body, expected_ty)?;

            Ok(Rc::from(syntax::Term::Let(items, body)))
        },
        Term::If(_, condition, consequent, alternative) => {
            let bool_ty = Rc::from(domain::Value::literal_ty(LiteralType::Bool));
            let condition = check_term(context, metas, condition, &bool_ty)?;
            let consequent = check_term(context, metas, consequent, expected_ty)?;
            let alternative = check_term(context, metas, alternative, expected_ty)?;

            Ok(Rc::from(syntax::Term::LiteralElim(
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
            Ok(Rc::from(syntax::Term::literal_intro(literal_intro)))
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
                    domain::Value::RecordTypeExtend(_, label, _, ty, rest) => Ok((label, ty, rest)),
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
                Ok(Rc::from(syntax::Term::RecordIntro(fields)))
            } else {
                Err(Diagnostic::new_error("not enough fields provided")
                    .with_label(DiagnosticLabel::new_primary(*span)))
            }
        },

        _ => {
            let (synth, synth_ty) = synth_term(MetaInsertion::Yes, context, metas, concrete_term)?;
            context.unify_values(metas, concrete_term.span(), &synth_ty, expected_ty)?;
            Ok(synth)
        },
    }
}

/// Controls the insertion of metavariables when performing type synthesis.
#[derive(Debug, Copy, Clone)]
pub enum MetaInsertion<'file> {
    /// Stop inserting metavariables.
    No,
    /// Insert metavariables until we hit an explicit argument.
    Yes,
    /// Insert metavariables until a matching implicit argument is found.
    UntilImplicit(&'file str),
    /// Insert metavariables until a matching instance argument is found.
    UntilInstance(&'file str),
}

/// Insert metavariables based on the expected type.
fn insert_metas(
    meta_insertion: MetaInsertion<'_>,
    context: &Context,
    metas: &mut meta::Env,
    span: FileSpan,
    mut term: Rc<syntax::Term>,
    term_ty: &Rc<domain::Type>,
) -> Result<(Rc<syntax::Term>, Rc<domain::Type>), Diagnostic<FileSpan>> {
    use mltt_core::domain::Value::FunType;

    let mut term_ty = term_ty.clone();

    while let FunType(app_mode, _, param_ty, body_ty) = term_ty.as_ref() {
        match (meta_insertion, app_mode) {
            // The user requested we stop inserting metavariables, or
            // we have seen an explicit argument, so we stop inserting
            // metavariables.
            (MetaInsertion::No, _) | (_, AppMode::Explicit) => break,

            // FIXME: mismatches?

            // In these cases we see a matching implicit or instance argument
            // being passed, corresponding to the expected parameter in the
            // type. Therefore we stop inserting metavariables.
            (MetaInsertion::UntilImplicit(l), AppMode::Implicit(label)) if l == label.0 => break,
            (MetaInsertion::UntilInstance(l), AppMode::Instance(label)) if l == label.0 => break,

            // Based on the given type, we expected an implicit argument to be
            // applied. Instead, let's apply a metavariable argument in its
            // place, to be solved later (during unification).
            (_, AppMode::Implicit(_)) => {
                let arg = context.new_meta(metas, span, param_ty.clone());
                let arg_value = context.eval_term(metas, None, &arg)?;
                term = Rc::from(syntax::Term::FunElim(term, app_mode.clone(), arg));
                term_ty = context.app_closure(metas, body_ty, arg_value)?;
            },

            // TODO: Instance arguments
            (_, AppMode::Instance(label)) => {
                let message = "inference of instance arguments is not yet supported";
                return Err(Diagnostic::new_error(message).with_label(
                    DiagnosticLabel::new_primary(span)
                        .with_message(format!("add the argument `{{{{{} = ..}}}}` here", label)),
                ));
            },
        }
    }

    Ok((term, term_ty))
}

/// Synthesize the type of the given term.
///
/// Metavariables are inserted based on the given `meta_insertion`.
///
/// Returns the elaborated term and its synthesized type.
pub fn synth_term(
    meta_insertion: MetaInsertion<'_>,
    context: &Context,
    metas: &mut meta::Env,
    concrete_term: &Term<'_>,
) -> Result<(Rc<syntax::Term>, Rc<domain::Type>), Diagnostic<FileSpan>> {
    use std::cmp;

    log::trace!("synthesizing term:\t\t{}", concrete_term);

    match concrete_term {
        Term::Var(name) => match context.lookup_binder(name.slice) {
            None => Err(Diagnostic::new_error("unbound variable")
                .with_label(DiagnosticLabel::new_primary(name.span()))),
            Some((index, var_ty)) => {
                let span = concrete_term.span().end_span();
                let var = Rc::from(syntax::Term::var(index));
                insert_metas(meta_insertion, context, metas, span, var, var_ty)
            },
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
        Term::Hole(span) => Err(Diagnostic::new_error("ambiguous term").with_label(
            DiagnosticLabel::new_primary(*span).with_message("type annotations needed here"),
        )),

        Term::Parens(_, concrete_term) => synth_term(meta_insertion, context, metas, concrete_term),
        Term::Ann(concrete_term, concrete_term_ty) => {
            let (term_ty, _) = synth_universe(context, metas, concrete_term_ty)?;
            let term_ty_value = context.eval_term(metas, concrete_term_ty.span(), &term_ty)?;
            let term = check_term(context, metas, concrete_term, &term_ty_value)?;

            Ok((Rc::from(syntax::Term::ann(term, term_ty)), term_ty_value))
        },
        Term::Let(_, concrete_items, concrete_body) => {
            let mut context = context.clone();
            let items = check_items(&mut context, metas, concrete_items)?;
            let (body, body_ty) = synth_term(meta_insertion, &context, metas, concrete_body)?;

            Ok((Rc::from(syntax::Term::Let(items, body)), body_ty))
        },
        Term::If(span, _, _, _) => Err(Diagnostic::new_error("ambiguous term").with_label(
            DiagnosticLabel::new_primary(*span).with_message("type annotations needed here"),
        )),
        Term::Case(span, _, _) => Err(Diagnostic::new_error("ambiguous term").with_label(
            DiagnosticLabel::new_primary(*span).with_message("type annotations needed here"),
        )),

        Term::LiteralIntro(kind, literal) => {
            let (literal_intro, ty) = literal::synth(*kind, literal)?;
            let term = Rc::from(syntax::Term::literal_intro(literal_intro));

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
                        Rc::from(syntax::Term::FunType(app_mode, None, param_ty, acc))
                    }),
                Rc::from(domain::Value::universe(max_level)),
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

            let fun_ty = syntax::Term::FunType(AppMode::Explicit, None, param_ty, body_ty);
            let max_level = cmp::max(param_level, body_level);

            Ok((
                Rc::from(fun_ty),
                Rc::from(domain::Value::universe(max_level)),
            ))
        },
        Term::FunIntro(_, concrete_params, concrete_body) => {
            let clause = Clause::new(concrete_params, None, concrete_body);
            clause::synth_clause(context, metas, clause)
        },
        Term::FunElim(concrete_fun, concrete_args) => {
            let (concrete_arg, concrete_args) = match concrete_args.split_first() {
                None => return synth_term(meta_insertion, context, metas, concrete_term),
                Some(concrete_args) => concrete_args,
            };

            // FIXME: Clean up some duplication here?

            let (mut fun, mut fun_ty) = {
                let arg_meta_ins = match concrete_arg {
                    Arg::Explicit(_) => MetaInsertion::Yes,
                    Arg::Implicit(_, label, _) => MetaInsertion::UntilImplicit(label.slice),
                    Arg::Instance(_, label, _) => MetaInsertion::UntilInstance(label.slice),
                };
                synth_term(arg_meta_ins, context, metas, concrete_fun)?
            };

            match context.force_value(metas, None, &fun_ty)?.as_ref() {
                domain::Value::FunType(app_mode, _, param_ty, body_ty) => {
                    let concrete_arg_term = concrete_arg.desugar_arg_term();
                    let app_mode = app_mode.clone(); // TODO: check app mode is compatible with insertion
                    let arg = check_term(context, metas, concrete_arg_term.as_ref(), param_ty)?;
                    let arg_value = context.eval_term(metas, None, &arg)?;

                    fun = Rc::from(syntax::Term::FunElim(fun, app_mode, arg));
                    fun_ty = context.app_closure(metas, body_ty, arg_value)?;
                },
                _ => {
                    let fun_ty = context.value_to_doc(metas, &fun_ty);
                    return Err(Diagnostic::new_error("expected a function").with_label(
                        DiagnosticLabel::new_primary(concrete_fun.span())
                            .with_message(format!("found: {}", fun_ty.pretty(1000_000_000))),
                    ));
                },
            }

            for concrete_arg in concrete_args {
                let (new_fun, new_fun_ty) = {
                    let arg_span = concrete_arg.span().start_span();
                    let arg_meta_ins = match concrete_arg {
                        Arg::Explicit(_) => MetaInsertion::Yes,
                        Arg::Implicit(_, label, _) => MetaInsertion::UntilImplicit(label.slice),
                        Arg::Instance(_, label, _) => MetaInsertion::UntilInstance(label.slice),
                    };
                    insert_metas(arg_meta_ins, context, metas, arg_span, fun, &fun_ty)?
                };

                match context.force_value(metas, None, &new_fun_ty)?.as_ref() {
                    domain::Value::FunType(app_mode, _, param_ty, body_ty) => {
                        let concrete_arg_term = concrete_arg.desugar_arg_term();
                        let app_mode = app_mode.clone(); // TODO: check app mode is compatible with insertion
                        let arg = check_term(context, metas, concrete_arg_term.as_ref(), param_ty)?;
                        let arg_value = context.eval_term(metas, None, &arg)?;

                        fun = Rc::from(syntax::Term::FunElim(new_fun, app_mode, arg));
                        fun_ty = context.app_closure(metas, body_ty, arg_value)?;
                    },
                    _ => {
                        let fun_ty = context.value_to_doc(metas, &fun_ty);
                        return Err(Diagnostic::new_error("expected a function").with_label(
                            DiagnosticLabel::new_primary(concrete_fun.span())
                                .with_message(format!("found: {}", fun_ty.pretty(1000_000_000))),
                        ));
                    },
                }
            }

            let span = concrete_term.span().end_span();
            insert_metas(meta_insertion, context, metas, span, fun, &fun_ty)
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

                    Ok((docs, Label(concrete_ty_field.label.to_string()), None, ty))
                })
                .collect::<Result<_, Diagnostic<FileSpan>>>()?;

            Ok((
                Rc::from(syntax::Term::RecordType(ty_fields)),
                Rc::from(domain::Value::universe(max_level)),
            ))
        },
        Term::RecordIntro(span, intro_fields) => {
            if intro_fields.is_empty() {
                Ok((
                    Rc::from(syntax::Term::RecordIntro(Vec::new())),
                    Rc::from(domain::Value::RecordTypeEmpty),
                ))
            } else {
                Err(Diagnostic::new_error("ambiguous term").with_label(
                    DiagnosticLabel::new_primary(*span)
                        .with_message("type annotations needed here"),
                ))
            }
        },
        Term::RecordElim(concrete_record, label) => {
            let (record, mut record_ty) =
                synth_term(MetaInsertion::Yes, context, metas, concrete_record)?;

            while let domain::Value::RecordTypeExtend(_, current_label, _, current_ty, rest) =
                record_ty.as_ref()
            {
                let expr = Rc::from(syntax::Term::RecordElim(
                    record.clone(),
                    current_label.clone(),
                ));

                if current_label.0 == label.slice {
                    let span = concrete_term.span().end_span();
                    return insert_metas(meta_insertion, context, metas, span, expr, &current_ty);
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
                Rc::from(syntax::Term::universe(level)),
                Rc::from(domain::Value::universe(level + 1)),
            ))
        },
    }
}
