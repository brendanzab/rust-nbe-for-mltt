//! Elaboration of the concrete syntax into the core syntax.
//!
//! Performs the following:
//!
//! - name resolution
//! - desugaring
//! - pattern compilation (TODO)
//! - bidirectional type checking
//! - elaboration of holes (TODO)

use mltt_concrete::{Item, Pattern, RecordIntroField, Term};
use mltt_core::nbe::{self, NbeError};
use mltt_core::syntax::{core, domain, normal, DbIndex, DbLevel, Label, UniverseLevel};

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

    /// Add a new local definition to the context
    pub fn insert_definition(
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

    /// Add a new binder to the context, returning a value that points to the parameter
    pub fn insert_binder(
        &mut self,
        name: impl Into<Option<String>>,
        ty: domain::RcType,
    ) -> domain::RcValue {
        let param = domain::RcValue::var(self.level());
        self.insert_definition(name, param.clone(), ty);
        param
    }

    /// Lookup the de-bruijn index and the type annotation of a binder in the
    /// context using a user-defined name
    pub fn lookup_binder(&self, name: &str) -> Option<(DbIndex, &domain::RcType)> {
        for (i, (n, ty)) in self.binders.iter().enumerate() {
            if Some(name) == n.as_ref().map(String::as_str) {
                let level = DbIndex(i as u32);

                log::trace!("lookup binder: {} -> @{}", name, level.0);

                return Some((level, ty));
            }
        }
        None
    }

    /// Evaluate a term using the evaluation environment
    pub fn eval(&self, term: &core::RcTerm) -> Result<domain::RcValue, NbeError> {
        nbe::eval(term, self.values())
    }

    /// Read back a value into normal form
    pub fn read_back(&self, value: &domain::RcValue) -> Result<normal::RcNormal, NbeError> {
        nbe::read_back_term(self.level(), value)
    }

    /// Fully normalize a term
    pub fn normalize(&self, term: &core::RcTerm) -> Result<normal::RcNormal, NbeError> {
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
    // Declarations that may be waiting to be defined
    let mut forward_declarations = im::HashMap::new();
    // The local elaboration context
    let mut context = Context::new();
    // The elaborated items
    let mut core_items = {
        let expected_defn_count = concrete_items.iter().filter(|i| i.is_definition()).count();
        Vec::with_capacity(expected_defn_count)
    };

    for concrete_item in concrete_items {
        use im::hashmap::Entry;

        match concrete_item {
            Item::Declaration(declaration) => {
                log::trace!(
                    "checking declaration:\t\t{}\t: {}",
                    declaration.label,
                    declaration.ann,
                );

                match forward_declarations.entry(&declaration.label) {
                    // No previous declaration for this name was seen, so we can
                    // go-ahead and type check, elaborate, and then add it to
                    // the context
                    Entry::Vacant(entry) => {
                        let (ty, _) = synth_universe(&context, &declaration.ann)?;
                        // Ensure that we evaluate the forward declaration in
                        // the current context - if we wait until later more
                        // definitions might have come in to scope!
                        //
                        // NOTE: I'm not sure how this reordering affects name
                        // binding - we might need to account for it!
                        let ty = context.eval(&ty)?;
                        entry.insert(Some((&declaration.docs, ty)));
                    },
                    // There's a declaration for this name already pending - we
                    // can't add a new one!
                    Entry::Occupied(_) => {
                        return Err(TypeError::AlreadyDeclared(declaration.label.clone()));
                    },
                }
            },
            Item::Definition(definition) => {
                log::trace!(
                    "checking definition:\t\t{}\t= {}",
                    definition.label,
                    definition.body,
                );

                let patterns = &definition.patterns;
                let body_ty = definition.body_ty.as_ref();
                let body = &definition.body;

                let (doc, term, ty) = match forward_declarations.entry(&definition.label) {
                    // No prior declaration was found, so we'll try synthesizing
                    // its type instead
                    Entry::Vacant(entry) => {
                        let docs = docs::concat(&definition.docs);
                        let (term, ty) = synth_clause(&context, patterns, body_ty, body)?;
                        entry.insert(None);
                        (docs, term, ty)
                    },
                    // Something has happened with this declaration, let's
                    // 'take' a look!
                    Entry::Occupied(mut entry) => match entry.get_mut().take() {
                        // We found a prior declaration, so we'll use it as a
                        // basis for checking the definition
                        Some((decl_docs, ty)) => {
                            let docs = docs::merge(&definition.label, decl_docs, &definition.docs)?;
                            let term = check_clause(&context, patterns, body_ty, body, &ty)?;
                            (docs, term, ty)
                        },
                        // This declaration was already given a definition, so
                        // this is an error!
                        //
                        // NOTE: Some languages (eg. Haskell, Agda, Idris, and
                        // Erlang) turn duplicate definitions into case matches.
                        // Languages like Elm don't. What should we do here?
                        None => return Err(TypeError::AlreadyDefined(definition.label.clone())),
                    },
                };
                let value = context.eval(&term)?;
                // NOTE: Not sure how expensive this readback is here! We should
                // definitely investigate fusing the conversion between
                // `value::Value -> normal::Normal -> core::Term` by way of
                // visitors...
                let term_ty = core::RcTerm::from(&context.read_back(&ty)?);

                log::trace!(
                    "elaborated declaration:\t{}\t: {}",
                    definition.label,
                    term_ty
                );
                log::trace!("elaborated definition:\t{}\t= {}", definition.label, term);

                context.insert_definition(definition.label.clone(), value, ty);
                core_items.push(core::Item {
                    doc,
                    label: definition.label.clone(),
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

/// Check that a given pattern clause conforms to an expected type, elaborating
/// it into a case tree.
fn check_clause(
    context: &Context,
    mut patterns: &[Pattern],
    concrete_body_ty: Option<&Term>,
    concrete_body: &Term,
    expected_ty: &domain::RcType,
) -> Result<core::RcTerm, TypeError> {
    let mut context = context.clone();
    let mut param_tys = Vec::new();
    let mut expected_ty = expected_ty.clone();

    while let Some((head_pattern, rest_patterns)) = patterns.split_first() {
        patterns = rest_patterns;
        match (head_pattern, expected_ty.as_ref()) {
            // INTRO: If it is a variable a pattern, and we're expecting a function
            // type, then we'll elaborate to a function.
            (Pattern::Var(var_name), domain::Value::FunType(param_ty, body_ty)) => {
                param_tys.push(param_ty.clone());
                let param = context.insert_binder(var_name.clone(), param_ty.clone());
                expected_ty = nbe::do_closure_app(&body_ty, param.clone())?;
            },
            _ => {
                let found = expected_ty.clone();
                return Err(TypeError::ExpectedFunType { found });
            },
        }
    }

    let body = check_ann(&context, concrete_body, concrete_body_ty, &expected_ty)?;

    Ok(param_tys
        .iter()
        .rev()
        .fold(body, |acc, _| core::RcTerm::from(core::Term::FunIntro(acc))))
}

/// Synthesize the type of a clause, elaborating it into a case tree.
fn synth_clause(
    context: &Context,
    patterns: &[Pattern],
    concrete_body_ty: Option<&Term>,
    concrete_body: &Term,
) -> Result<(core::RcTerm, domain::RcType), TypeError> {
    if !patterns.is_empty() {
        // TODO: We will be able to type this once we have annotated patterns!
        unimplemented!("type annotations needed");
    }

    let (body, body_ty) = synth_ann(&context, concrete_body, concrete_body_ty)?;

    Ok((
        patterns
            .iter()
            .fold(body, |acc, _| core::RcTerm::from(core::Term::FunIntro(acc))),
        body_ty,
    ))
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
        Term::Let(def_name, concrete_def, concrete_body) => {
            let (def, def_ty) = synth_term(context, concrete_def)?;
            let def_value = context.eval(&def)?;
            let body = {
                let mut context = context.clone();
                context.insert_definition(def_name.clone(), def_value, def_ty);
                check_term(&context, concrete_body, expected_ty)?
            };

            Ok(core::RcTerm::from(core::Term::Let(def, body)))
        },
        Term::Parens(concrete_term) => check_term(context, concrete_term, expected_ty),

        Term::FunIntro(patterns, concrete_body) => {
            check_clause(context, patterns, None, concrete_body, expected_ty)
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
                            patterns,
                            body_ty,
                            body,
                        } if expected_label.0 == *label => {
                            let term = check_clause(
                                &context,
                                patterns,
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

                    context.insert_definition(found_label, term_value.clone(), term_ty);
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
        Term::Let(def_name, concrete_def, concrete_body) => {
            let (def, def_ty) = synth_term(context, concrete_def)?;
            let def_value = context.eval(&def)?;
            let (body, body_ty) = {
                let mut context = context.clone();
                context.insert_definition(def_name.clone(), def_value, def_ty);
                synth_term(&context, concrete_body)?
            };

            Ok((core::RcTerm::from(core::Term::Let(def, body)), body_ty))
        },
        Term::Ann(concrete_term, concrete_term_ty) => {
            synth_ann(context, concrete_term, Some(concrete_term_ty))
        },
        Term::Parens(concrete_term) => synth_term(context, concrete_term),

        Term::FunType(concrete_params, concrete_body_ty) => {
            let mut context = context.clone();
            let mut param_tys = Vec::new();
            let mut max_level = UniverseLevel::from(0);

            for (param_names, concrete_param_ty) in concrete_params {
                for param_name in param_names {
                    let (param_ty, param_level) = synth_universe(&context, concrete_param_ty)?;
                    context.insert_binder(param_name.clone(), context.eval(&param_ty)?);
                    param_tys.push(param_ty);
                    max_level = cmp::max(max_level, param_level);
                }
            }

            let (body_ty, body_level) = synth_universe(&context, concrete_body_ty)?;
            max_level = cmp::max(max_level, body_level);

            Ok((
                param_tys.into_iter().rev().fold(body_ty, |acc, param_ty| {
                    core::RcTerm::from(core::Term::FunType(param_ty, acc))
                }),
                domain::RcValue::from(domain::Value::Universe(max_level)),
            ))
        },
        Term::FunArrowType(concrete_param_ty, concrete_body_ty) => {
            let (param_ty, param_level) = synth_universe(context, concrete_param_ty)?;
            let param_ty_value = context.eval(&param_ty)?;
            let (body_ty, body_level) = {
                let mut context = context.clone();
                context.insert_binder(None, param_ty_value);
                synth_universe(&context, concrete_body_ty)?
            };

            Ok((
                core::RcTerm::from(core::Term::FunType(param_ty, body_ty)),
                domain::RcValue::from(domain::Value::Universe(cmp::max(param_level, body_level))),
            ))
        },
        Term::FunIntro(_, _) => Err(TypeError::AmbiguousTerm(concrete_term.clone())),
        Term::FunApp(concrete_fun, concrete_args) => {
            let (mut fun, mut fun_ty) = synth_term(context, concrete_fun)?;

            for concrete_arg in concrete_args {
                if let domain::Value::FunType(param_ty, body_ty) = fun_ty.as_ref() {
                    let arg = check_term(context, concrete_arg, param_ty)?;
                    let arg_value = context.eval(&arg)?;

                    fun = core::RcTerm::from(core::Term::FunApp(fun, arg));
                    fun_ty = nbe::do_closure_app(body_ty, arg_value)?;
                } else {
                    let found = fun_ty.clone();
                    return Err(TypeError::ExpectedFunType { found });
                }
            }

            Ok((fun, fun_ty))
        },

        Term::RecordType(concrete_ty_fields) => {
            let mut context = context.clone();
            let mut max_level = UniverseLevel::from(0);

            let ty_fields = concrete_ty_fields
                .iter()
                .map(|concrete_ty_field| {
                    let docs = docs::concat(&concrete_ty_field.docs);
                    let (ty, ty_level) = synth_universe(&context, &concrete_ty_field.ann)?;
                    context.insert_binder(concrete_ty_field.label.clone(), context.eval(&ty)?);
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
        Term::RecordProj(concrete_record, label) => {
            let (record, mut record_ty) = synth_term(context, concrete_record)?;

            while let domain::Value::RecordTypeExtend(current_label, current_ty, rest) =
                record_ty.as_ref()
            {
                let expr = core::RcTerm::from(core::Term::RecordProj(
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
            let level = UniverseLevel::from(level.unwrap_or(0));
            Ok((
                core::RcTerm::from(core::Term::Universe(level)),
                domain::RcValue::from(domain::Value::Universe(level + 1)),
            ))
        },
    }
}
