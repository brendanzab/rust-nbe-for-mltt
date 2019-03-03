//! Elaboration of the concrete syntax into the core syntax.
//!
//! Performs the following:
//!
//! - name resolution
//! - desugaring
//! - pattern compilation (TODO)
//! - bidirectional type checking
//! - elaboration of holes (TODO)

#![warn(rust_2018_idioms)]

use mltt_concrete::{Arg, IntroParam, Item, Pattern, RecordIntroField, Term, TypeParam};
use mltt_core::nbe::{self, NbeError};
use mltt_core::syntax::{core, domain, AppMode, DbIndex, DbLevel, Label, UniverseLevel};

mod docs;
mod errors;

pub use self::errors::TypeError;

/// Local elaboration context
#[derive(Debug, Clone, PartialEq)]
pub struct Context {
    /// Number of local entries
    level: DbLevel,
    /// Values to be used during evaluation
    values: domain::Env,
    /// The user-defined names and type annotations of the binders we have passed over
    binders: im::Vector<(Option<String>, domain::RcType)>,
}

impl Context {
    /// Create a new, empty context
    pub fn new() -> Context {
        Context {
            level: DbLevel(0),
            values: domain::Env::new(),
            binders: im::Vector::new(),
        }
    }

    /// Number of local entries in the context
    pub fn level(&self) -> DbLevel {
        self.level
    }

    /// Values to be used during evaluation
    pub fn values(&self) -> &domain::Env {
        &self.values
    }

    /// Add a local definition to the context.
    pub fn local_define(
        &mut self,
        name: impl Into<Option<String>>,
        value: domain::RcValue,
        ty: domain::RcType,
    ) {
        let name = name.into();
        match &name {
            None => log::trace!("insert fresh local"),
            Some(name) => log::trace!("insert local: {}", name),
        }
        self.level += 1;
        self.values.push_front(value);
        self.binders.push_front((name, ty));
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
    pub fn lookup_binder(&self, name: &str) -> Option<(DbIndex, &domain::RcType)> {
        Iterator::zip(0.., self.binders.iter()).find_map(|(index, (current_name, ty))| {
            match current_name {
                Some(current_name) if current_name == name => {
                    log::trace!("lookup binder: {} -> @{}", name, index);
                    Some((DbIndex(index), ty))
                },
                Some(_) | None => None,
            }
        })
    }

    /// Evaluate a term using the evaluation environment
    pub fn eval(&self, term: &core::RcTerm) -> Result<domain::RcValue, NbeError> {
        nbe::eval(term, self.values())
    }

    /// Read a value back into the core syntax, normalizing as required.
    pub fn read_back(&self, value: &domain::RcValue) -> Result<core::RcTerm, NbeError> {
        nbe::read_back_term(self.level(), value)
    }

    /// Fully normalize a term by first evaluating it, then reading it back.
    pub fn normalize(&self, term: &core::RcTerm) -> Result<core::RcTerm, NbeError> {
        let value = self.eval(term)?;
        self.read_back(&value)
    }

    /// Expect that `ty1` is a subtype of `ty2` in the current context
    pub fn expect_subtype(
        &self,
        ty1: &domain::RcType,
        ty2: &domain::RcType,
    ) -> Result<(), TypeError> {
        if nbe::check_subtype(self.level(), ty1, ty2)? {
            Ok(())
        } else {
            Err(TypeError::ExpectedSubtype(ty1.clone(), ty2.clone()))
        }
    }
}

/// Check that this is a valid module
pub fn check_module(concrete_items: &[Item]) -> Result<Vec<core::Item>, TypeError> {
    // The local elaboration context
    let mut context = Context::new();
    check_items(&mut context, concrete_items)
}

fn check_items(
    context: &mut Context,
    concrete_items: &[Item],
) -> Result<Vec<core::Item>, TypeError> {
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
                let label = &declaration.label;
                let body_ty = &declaration.body_ty;

                log::trace!("checking declaration:\t\t{}\t: {}", label, body_ty);

                match forward_declarations.entry(label) {
                    // No previous declaration for this name was seen, so we can
                    // go-ahead and type check, elaborate, and then add it to
                    // the context
                    Entry::Vacant(entry) => {
                        let (body_ty, _) = synth_universe(&context, &body_ty)?;
                        // Ensure that we evaluate the forward declaration in
                        // the current context - if we wait until later more
                        // definitions might have come in to scope!
                        //
                        // NOTE: I'm not sure how this reordering affects name
                        // binding - we might need to account for it!
                        let body_ty = context.eval(&body_ty)?;
                        entry.insert(Some((&declaration.docs, body_ty)));
                    },
                    // There's a declaration for this name already pending - we
                    // can't add a new one!
                    Entry::Occupied(_) => {
                        return Err(TypeError::AlreadyDeclared(label.clone()));
                    },
                }
            },
            Item::Definition(definition) => {
                let label = &definition.label;
                let params = &definition.params;
                let body_ty = definition.body_ty.as_ref();
                let body = &definition.body;

                log::trace!("checking definition:\t\t{}\t= {}", label, body);

                let (doc, term, ty) = match forward_declarations.entry(label) {
                    // No prior declaration was found, so we'll try synthesizing
                    // its type instead
                    Entry::Vacant(entry) => {
                        let docs = docs::concat(&definition.docs);
                        let (term, ty) = synth_clause(&context, params, body_ty, body)?;
                        entry.insert(None);
                        (docs, term, ty)
                    },
                    // Something has happened with this declaration, let's
                    // 'take' a look!
                    Entry::Occupied(mut entry) => match entry.get_mut().take() {
                        // We found a prior declaration, so we'll use it as a
                        // basis for checking the definition
                        Some((decl_docs, ty)) => {
                            let docs = docs::merge(&label, decl_docs, &definition.docs)?;
                            let term = check_clause(&context, params, body_ty, body, &ty)?;
                            (docs, term, ty)
                        },
                        // This declaration was already given a definition, so
                        // this is an error!
                        //
                        // NOTE: Some languages (eg. Haskell, Agda, Idris, and
                        // Erlang) turn duplicate definitions into case matches.
                        // Languages like Elm don't. What should we do here?
                        None => return Err(TypeError::AlreadyDefined(label.clone())),
                    },
                };
                let value = context.eval(&term)?;
                // NOTE: Not sure how expensive this readback is here!
                let term_ty = context.read_back(&ty)?;

                log::trace!("elaborated declaration:\t{}\t: {}", label, term_ty);
                log::trace!("elaborated definition:\t{}\t= {}", label, term);

                context.local_define(label.clone(), value, ty);
                core_items.push(core::Item {
                    doc,
                    label: label.clone(),
                    term_ty,
                    term,
                });
            },
        }
    }

    Ok(core_items)
}

/// Synthesize the type of an annotated term
fn synth_var(context: &Context, name: &str) -> Result<(core::RcTerm, domain::RcType), TypeError> {
    match context.lookup_binder(name) {
        None => Err(TypeError::UnboundVariable(name.to_owned())),
        Some((index, ann)) => Ok((core::RcTerm::from(core::Term::Var(index)), ann.clone())),
    }
}

/// Check that an annotated term conforms to an expected type
fn check_ann(
    context: &Context,
    concrete_term: &Term,
    concrete_term_ty: Option<&Term>,
    expected_ty: &domain::RcType,
) -> Result<core::RcTerm, TypeError> {
    match concrete_term_ty {
        None => check_term(context, concrete_term, &expected_ty),
        Some(concrete_term_ty) => {
            let (term_ty, _) = synth_universe(context, concrete_term_ty)?;
            let term_ty = context.eval(&term_ty)?;
            let term = check_term(&context, concrete_term, &term_ty)?;
            context.expect_subtype(&term_ty, &expected_ty)?;
            Ok(term)
        },
    }
}

/// Synthesize the type of an annotated term
fn synth_ann(
    context: &Context,
    concrete_term: &Term,
    concrete_term_ty: Option<&Term>,
) -> Result<(core::RcTerm, domain::RcType), TypeError> {
    match concrete_term_ty {
        None => synth_term(context, concrete_term),
        Some(concrete_term_ty) => {
            let (term_ty, _) = synth_universe(context, concrete_term_ty)?;
            let term_ty = context.eval(&term_ty)?;
            let term = check_term(context, concrete_term, &term_ty)?;
            Ok((term, term_ty))
        },
    }
}

/// Check that a given clause conforms to an expected type, and elaborates
/// it into a case tree.
fn check_clause(
    context: &Context,
    mut params: &[IntroParam],
    concrete_body_ty: Option<&Term>,
    concrete_body: &Term,
    expected_ty: &domain::RcType,
) -> Result<core::RcTerm, TypeError> {
    let mut context = context.clone();
    let mut param_tys = Vec::new();
    let mut expected_ty = expected_ty.clone();

    while let Some((head_param, rest_params)) = params.split_first() {
        params = rest_params;

        let (app_mode, var_name, param_ty, body_ty) = match (head_param, expected_ty.as_ref()) {
            // INTRO: If it is a variable a pattern, and we're expecting a
            // function type, then we'll elaborate to a function.
            (
                IntroParam::Explicit(pattern),
                domain::Value::FunType(app_mode, param_ty, body_ty),
            ) => match app_mode {
                AppMode::Explicit => match pattern {
                    Pattern::Var(var_name) => (app_mode.clone(), var_name, param_ty, body_ty),
                },
                app_mode => {
                    return Err(TypeError::UnexpectedAppMode {
                        found: AppMode::Explicit,
                        expected: app_mode.clone(),
                    });
                },
            },
            (
                IntroParam::Implicit(intro_label, pattern),
                domain::Value::FunType(app_mode, param_ty, body_ty),
            ) => match app_mode {
                AppMode::Implicit(ty_label) if *intro_label == ty_label.0 => match pattern {
                    None => (app_mode.clone(), intro_label, param_ty, body_ty),
                    Some(Pattern::Var(var_name)) => (app_mode.clone(), var_name, param_ty, body_ty),
                },
                app_mode => {
                    return Err(TypeError::UnexpectedAppMode {
                        found: AppMode::Implicit(Label(intro_label.clone())),
                        expected: app_mode.clone(),
                    });
                },
            },
            _ => {
                let found = expected_ty.clone();
                return Err(TypeError::ExpectedFunType { found });
            },
        };

        param_tys.push((app_mode, param_ty.clone()));
        let param = context.local_bind(var_name.clone(), param_ty.clone());
        expected_ty = nbe::do_closure_app(&body_ty, param.clone())?;
    }

    let body = check_ann(&context, concrete_body, concrete_body_ty, &expected_ty)?;

    Ok(param_tys
        .into_iter()
        .rev()
        .fold(body, |acc, (app_mode, _)| {
            core::RcTerm::from(core::Term::FunIntro(app_mode, acc))
        }))
}

/// Synthesize the type of a clause, elaborating it into a case tree.
fn synth_clause(
    context: &Context,
    params: &[IntroParam],
    concrete_body_ty: Option<&Term>,
    concrete_body: &Term,
) -> Result<(core::RcTerm, domain::RcType), TypeError> {
    if !params.is_empty() {
        // TODO: We will be able to type this once we have annotated patterns!
        unimplemented!("type annotations needed");
    }

    synth_ann(&context, concrete_body, concrete_body_ty)
}

/// Ensures that the given term is a universe, returning the level of that
/// universe and its elaborated form.
fn synth_universe(
    context: &Context,
    concrete_term: &Term,
) -> Result<(core::RcTerm, UniverseLevel), TypeError> {
    let (term, ty) = synth_term(context, concrete_term)?;
    match ty.as_ref() {
        domain::Value::Universe(level) => Ok((term, *level)),
        _ => Err(TypeError::ExpectedUniverse { found: ty.clone() }),
    }
}

/// Check that a given term conforms to an expected type
pub fn check_term(
    context: &Context,
    concrete_term: &Term,
    expected_ty: &domain::RcType,
) -> Result<core::RcTerm, TypeError> {
    log::trace!("checking term:\t\t{}", concrete_term);

    match concrete_term {
        Term::Literal(literal) => unimplemented!("literals: {:?}", literal),
        Term::Let(concrete_items, concrete_body) => {
            let mut context = context.clone();
            let items = check_items(&mut context, concrete_items)?;
            let body = check_term(&context, concrete_body, expected_ty)?;

            Ok(items.into_iter().rev().fold(body, |acc, item| {
                // TODO: other item fields?
                core::RcTerm::from(core::Term::Let(item.term, acc))
            }))
        },
        Term::Parens(concrete_term) => check_term(context, concrete_term, expected_ty),

        Term::FunIntro(params, concrete_body) => {
            check_clause(context, params, None, concrete_body, expected_ty)
        },

        Term::RecordIntro(concrete_intro_fields) => {
            let mut context = context.clone();
            let mut fields = Vec::new();
            let mut expected_ty = expected_ty.clone();

            for concrete_intro_field in concrete_intro_fields {
                if let domain::Value::RecordTypeExtend(expected_label, expected_term_ty, rest) =
                    expected_ty.as_ref()
                {
                    let (found_label, term) = match concrete_intro_field {
                        RecordIntroField::Punned { label } if expected_label.0 == *label => {
                            let (term, term_ty) = synth_var(&context, label)?;
                            context.expect_subtype(&term_ty, expected_term_ty)?;

                            (label.clone(), term)
                        },

                        RecordIntroField::Explicit {
                            label,
                            params,
                            body_ty,
                            body,
                        } if expected_label.0 == *label => {
                            let term = check_clause(
                                &context,
                                params,
                                body_ty.as_ref(),
                                body,
                                expected_term_ty,
                            )?;

                            (label.clone(), term)
                        },
                        RecordIntroField::Punned { label }
                        | RecordIntroField::Explicit { label, .. } => {
                            return Err(TypeError::UnexpectedField {
                                found: label.clone(),
                                expected: expected_label.0.clone(),
                            });
                        },
                    };
                    let label = expected_label.clone();
                    let term_value = context.eval(&term)?;
                    let term_ty = expected_term_ty.clone();

                    context.local_define(found_label, term_value.clone(), term_ty);
                    expected_ty = nbe::do_closure_app(&rest, term_value)?;
                    fields.push((label, term));
                } else {
                    return Err(TypeError::TooManyFieldsFound);
                }
            }

            if let domain::Value::RecordTypeEmpty = expected_ty.as_ref() {
                Ok(core::RcTerm::from(core::Term::RecordIntro(fields)))
            } else {
                Err(TypeError::NotEnoughFieldsProvided)
            }
        },

        _ => {
            let (synth, synth_ty) = synth_term(context, concrete_term)?;
            context.expect_subtype(&synth_ty, expected_ty)?;
            Ok(synth)
        },
    }
}

/// Synthesize the type of the given term
pub fn synth_term(
    context: &Context,
    concrete_term: &Term,
) -> Result<(core::RcTerm, domain::RcType), TypeError> {
    use std::cmp;

    log::trace!("synthesizing term:\t\t{}", concrete_term);

    match concrete_term {
        Term::Var(name) => synth_var(context, name),
        Term::Literal(literal) => unimplemented!("literals: {:?}", literal),
        Term::Let(concrete_items, concrete_body) => {
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
        Term::Ann(concrete_term, concrete_term_ty) => {
            synth_ann(context, concrete_term, Some(concrete_term_ty))
        },
        Term::Parens(concrete_term) => synth_term(context, concrete_term),

        Term::FunType(concrete_params, concrete_body_ty) => {
            let mut context = context.clone();
            let mut param_tys = Vec::new();
            let mut max_level = UniverseLevel(0);

            for param in concrete_params {
                match param {
                    TypeParam::Explicit(param_names, concrete_param_ty) => {
                        for param_name in param_names {
                            let app_mode = AppMode::Explicit;
                            let (param_ty, param_level) =
                                synth_universe(&context, concrete_param_ty)?;
                            context.local_bind(param_name.clone(), context.eval(&param_ty)?);
                            param_tys.push((app_mode, param_ty));
                            max_level = cmp::max(max_level, param_level);
                        }
                    },
                    TypeParam::Implicit(param_labels, Some(concrete_param_ty)) => {
                        for param_label in param_labels {
                            let app_mode = AppMode::Implicit(Label(param_label.clone()));
                            let (param_ty, param_level) =
                                synth_universe(&context, concrete_param_ty)?;
                            context.local_bind(param_label.clone(), context.eval(&param_ty)?);
                            param_tys.push((app_mode, param_ty));
                            max_level = cmp::max(max_level, param_level);
                        }
                    },
                    TypeParam::Implicit(_, None) => unimplemented!("missing implicit annotation"),
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
            let param_ty_value = context.eval(&param_ty)?;
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
        Term::FunIntro(_, _) => Err(TypeError::AmbiguousTerm(concrete_term.clone())),
        Term::FunElim(concrete_fun, concrete_args) => {
            let (mut fun, mut fun_ty) = synth_term(context, concrete_fun)?;
            for concrete_arg in concrete_args {
                if let domain::Value::FunType(ty_app_mode, param_ty, body_ty) = fun_ty.as_ref() {
                    let (arg_app_mode, arg) = match concrete_arg {
                        Arg::Explicit(concrete_arg) => (
                            AppMode::Explicit,
                            check_term(context, concrete_arg, param_ty)?,
                        ),
                        Arg::Implicit(label, Some(concrete_arg)) => (
                            AppMode::Implicit(Label(label.clone())),
                            check_term(context, concrete_arg, param_ty)?,
                        ),
                        Arg::Implicit(label, None) => (
                            AppMode::Implicit(Label(label.clone())),
                            check_term(context, &Term::Var(label.clone()), param_ty)?,
                        ),
                    };

                    if arg_app_mode == *ty_app_mode {
                        let arg_value = context.eval(&arg)?;

                        fun = core::RcTerm::from(core::Term::FunElim(fun, arg_app_mode, arg));
                        fun_ty = nbe::do_closure_app(body_ty, arg_value)?;
                    } else {
                        return Err(TypeError::UnexpectedAppMode {
                            found: arg_app_mode,
                            expected: ty_app_mode.clone(),
                        });
                    }
                } else {
                    let found = fun_ty.clone();
                    return Err(TypeError::ExpectedFunType { found });
                }
            }

            Ok((fun, fun_ty))
        },

        Term::RecordType(concrete_ty_fields) => {
            let mut context = context.clone();
            let mut max_level = UniverseLevel(0);

            let ty_fields = concrete_ty_fields
                .iter()
                .map(|concrete_ty_field| {
                    let docs = docs::concat(&concrete_ty_field.docs);
                    let (ty, ty_level) = synth_universe(&context, &concrete_ty_field.ann)?;
                    context.local_bind(concrete_ty_field.label.clone(), context.eval(&ty)?);
                    max_level = cmp::max(max_level, ty_level);
                    Ok((docs, Label(concrete_ty_field.label.clone()), ty))
                })
                .collect::<Result<_, TypeError>>()?;

            Ok((
                core::RcTerm::from(core::Term::RecordType(ty_fields)),
                domain::RcValue::from(domain::Value::Universe(max_level)),
            ))
        },
        Term::RecordIntro(_) => Err(TypeError::AmbiguousTerm(concrete_term.clone())),
        Term::RecordElim(concrete_record, label) => {
            let (record, mut record_ty) = synth_term(context, concrete_record)?;

            while let domain::Value::RecordTypeExtend(current_label, current_ty, rest) =
                record_ty.as_ref()
            {
                let expr = core::RcTerm::from(core::Term::RecordElim(
                    record.clone(),
                    current_label.clone(),
                ));

                if *label == current_label.0 {
                    return Ok((expr, current_ty.clone()));
                } else {
                    record_ty = nbe::do_closure_app(rest, context.eval(&expr)?)?;
                }
            }

            Err(TypeError::NoFieldInType(label.clone()))
        },

        Term::Universe(level) => {
            let level = UniverseLevel(level.unwrap_or(0));
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

        assert_eq!(param1, RcValue::from(Value::var(DbLevel(0))));
        assert_eq!(param2, RcValue::from(Value::var(DbLevel(1))));
        assert_eq!(param3, RcValue::from(Value::var(DbLevel(2))));

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

        assert_eq!(param1, RcValue::from(Value::var(DbLevel(0))));
        assert_eq!(param2, RcValue::from(Value::var(DbLevel(1))));
        assert_eq!(param3, RcValue::from(Value::var(DbLevel(2))));

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

        assert_eq!(param1, RcValue::from(Value::var(DbLevel(0))));
        assert_eq!(param2, RcValue::from(Value::var(DbLevel(1))));
        assert_eq!(param3, RcValue::from(Value::var(DbLevel(2))));

        assert_eq!(context.lookup_binder("x").unwrap().1, &ty1);
    }
}
