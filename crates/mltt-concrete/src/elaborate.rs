//! Elaboration of the concrete syntax into the core syntax.
//!
//! Performs the following:
//!
//! - name resolution
//! - desugaring
//! - pattern compilation (TODO)
//! - bidirectional type checking
//! - elaboration of holes (TODO)

use im;
use mltt_core::nbe::{self, NbeError};
use mltt_core::syntax::{core, domain, normal, DbIndex, DbLevel, UniverseLevel};
use std::error::Error;
use std::fmt;

use crate::syntax::{Item, Term};

/// Local elaboration context
#[derive(Debug, Clone, PartialEq)]
pub struct Context<'term> {
    /// Number of local entries
    level: DbLevel,
    /// Values to be used during evaluation
    values: domain::Env,
    /// The user-defined names and type annotations of the binders we have passed over
    binders: im::Vector<(Option<&'term String>, domain::RcType)>,
}

impl<'term> Context<'term> {
    /// Create a new, empty context
    pub fn new() -> Context<'term> {
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

    /// Add a new local entry to the context
    pub fn insert_local(
        &mut self,
        name: impl Into<Option<&'term String>>,
        value: domain::RcValue,
        ty: domain::RcType,
    ) {
        let name = name.into();
        match name {
            Some(name) => log::trace!("insert local: {}", name),
            None => log::trace!("insert fresh local"),
        }
        self.level += 1;
        self.values.push_front(value);
        self.binders.push_front((name, ty));
    }

    /// Add a new binder to the context, returning a value that points to the parameter
    pub fn insert_binder(
        &mut self,
        name: impl Into<Option<&'term String>>,
        ty: domain::RcType,
    ) -> domain::RcValue {
        let param = domain::RcValue::var(self.level());
        self.insert_local(name, param.clone(), ty);
        param
    }

    /// Lookup the de-bruijn index and the type annotation of a binder in the
    /// context using a user-defined name
    pub fn lookup_binder(&self, name: &str) -> Option<(DbIndex, &domain::RcType)> {
        for (i, (n, ty)) in self.binders.iter().enumerate() {
            if Some(name) == n.map(String::as_str) {
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

/// An error produced during type checking
#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    AlreadyDeclared(String),
    AlreadyDefined(String),
    AlreadyDocumented(String),
    ExpectedFunType {
        found: domain::RcType,
    },
    ExpectedPairType {
        found: domain::RcType,
    },
    ExpectedUniverse {
        over: Option<UniverseLevel>,
        found: domain::RcType,
    },
    ExpectedSubtype(domain::RcType, domain::RcType),
    AmbiguousTerm(Term),
    UnboundVariable(String),
    Nbe(NbeError),
}

impl From<NbeError> for TypeError {
    fn from(src: NbeError) -> TypeError {
        TypeError::Nbe(src)
    }
}

impl Error for TypeError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            TypeError::Nbe(error) => Some(error),
            _ => None,
        }
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TypeError::AlreadyDeclared(name) => write!(f, "already declared: `{}`", name),
            TypeError::AlreadyDefined(name) => write!(f, "already defined: `{}`", name),
            TypeError::AlreadyDocumented(name) => write!(f, "already documented: `{}`", name),
            TypeError::ExpectedFunType { .. } => write!(f, "expected function type"),
            TypeError::ExpectedPairType { .. } => write!(f, "expected function type"),
            TypeError::ExpectedUniverse { over, .. } => match over {
                None => write!(f, "expected universe"),
                Some(level) => write!(f, "expected universe over level `{}`", level.0),
            },
            TypeError::ExpectedSubtype(..) => write!(f, "not a subtype"),
            TypeError::AmbiguousTerm(..) => write!(f, "could not infer the type"),
            TypeError::UnboundVariable(name) => write!(f, "unbound variable `{}`", name),
            TypeError::Nbe(err) => err.fmt(f),
        }
    }
}

/// Concatenate a bunch of lines of documentation into a single string, removing
/// comment prefixes if they are found.
fn concat_docs(doc_lines: &[String]) -> String {
    let mut doc = String::new();
    for doc_line in doc_lines {
        // Strip the `||| ` or `|||` prefix left over from tokenization
        // We assume that each line of documentation has a trailing new line
        doc.push_str(match doc_line {
            doc_line if doc_line.starts_with("||| ") => &doc_line["||| ".len()..],
            doc_line if doc_line.starts_with("|||") => &doc_line["|||".len()..],
            doc_line => doc_line,
        });
    }
    doc
}

/// Select the documentation from either the declaration or the definition,
/// returning an error if both are present.
fn merge_docs(name: &str, decl_docs: &[String], defn_docs: &[String]) -> Result<String, TypeError> {
    match (decl_docs, defn_docs) {
        ([], []) => Ok("".to_owned()),
        (docs, []) => Ok(concat_docs(docs)),
        ([], docs) => Ok(concat_docs(docs)),
        (_, _) => Err(TypeError::AlreadyDocumented(name.to_owned())),
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
            Item::Declaration { docs, name, ann } => {
                log::trace!("checking declaration:\t\t{}\t: {}", name, ann);

                match forward_declarations.entry(name) {
                    // No previous declaration for this name was seen, so we can
                    // go-ahead and type check, elaborate, and then add it to
                    // the context
                    Entry::Vacant(entry) => {
                        let ty = check_term_ty(&context, ann)?;
                        // Ensure that we evaluate the forward declaration in
                        // the current context - if we wait until later more
                        // definitions might have come in to scope!
                        //
                        // NOTE: I'm not sure how this reordering affects name
                        // binding - we might need to account for it!
                        let ty = context.eval(&ty)?;
                        entry.insert(Some((docs, ty)));
                    },
                    // There's a declaration for this name already pending - we
                    // can't add a new one!
                    Entry::Occupied(_) => return Err(TypeError::AlreadyDeclared(name.clone())),
                }
            },
            Item::Definition {
                docs,
                name,
                param_names,
                body_ty,
                body,
            } => {
                log::trace!("checking definition:\t\t{}\t= {}", name, body);

                let body_ty = body_ty.as_ref();
                let (doc, term, ty) = match forward_declarations.entry(name) {
                    // No prior declaration was found, so we'll try synthesizing
                    // its type instead
                    Entry::Vacant(entry) => {
                        let docs = concat_docs(docs);
                        let (term, ty) = synth_fun_intro(&context, param_names, body_ty, body)?;
                        entry.insert(None);
                        (docs, term, ty)
                    },
                    // Something has happened with this declaration, let's
                    // 'take' a look!
                    Entry::Occupied(mut entry) => match entry.get_mut().take() {
                        // We found a prior declaration, so we'll use it as a
                        // basis for checking the definition
                        Some((decl_docs, ty)) => {
                            let docs = merge_docs(name, decl_docs, docs)?;
                            let term = check_fun_intro(&context, param_names, body_ty, body, &ty)?;
                            (docs, term, ty)
                        },
                        // This declaration was already given a definition, so
                        // this is an error!
                        //
                        // NOTE: Some languages (eg. Haskell, Agda, Idris, and
                        // Erlang) turn duplicate definitions into case matches.
                        // Languages like Elm don't. What should we do here?
                        None => return Err(TypeError::AlreadyDefined(name.clone())),
                    },
                };
                let value = context.eval(&term)?;
                // NOTE: Not sure how expensive this readback is here! We should
                // definitely investigate fusing the conversion between
                // `value::Value -> normal::Normal -> core::Term` by way of
                // visitors...
                let ann = core::RcTerm::from(&context.read_back(&ty)?);

                log::trace!("elaborated declaration:\t{}\t: {}", name, ann);
                log::trace!("elaborated definition:\t{}\t= {}", name, term);

                context.insert_local(name, value, ty);
                core_items.push(core::Item {
                    doc,
                    name: name.clone(),
                    ann,
                    term,
                });
            },
        }
    }

    Ok(core_items)
}

/// Check that a function introduction conforms to an expected type
fn check_fun_intro<'term>(
    context: &Context<'term>,
    param_names: &'term [String],
    concrete_body_ty: Option<&'term Term>,
    concrete_body: &'term Term,
    expected_ty: &domain::RcType,
) -> Result<core::RcTerm, TypeError> {
    let mut context = context.clone();
    let mut expected_ty = expected_ty.clone();

    for param_name in param_names.iter() {
        if let domain::Value::FunType(param_ty, body_ty) = expected_ty.as_ref() {
            let param = context.insert_binder(param_name, param_ty.clone());
            expected_ty = nbe::do_closure_app(body_ty, param)?;
        } else {
            let found = expected_ty.clone();
            return Err(TypeError::ExpectedFunType { found });
        }
    }

    let body = match concrete_body_ty {
        None => check_term(&context, concrete_body, &expected_ty)?,
        Some(concrete_body_ty) => {
            let body_ty = context.eval(&check_term_ty(&context, concrete_body_ty)?)?;
            let body = check_term(&context, concrete_body, &body_ty)?;
            context.expect_subtype(&body_ty, &expected_ty)?;
            body
        },
    };

    Ok(param_names
        .iter()
        .fold(body, |acc, _| core::RcTerm::from(core::Term::FunIntro(acc))))
}

/// Synthesize the type of a function introduction
fn synth_fun_intro<'term>(
    context: &Context<'term>,
    param_names: &'term [String],
    concrete_body_ty: Option<&'term Term>,
    concrete_body: &'term Term,
) -> Result<(core::RcTerm, domain::RcType), TypeError> {
    if !param_names.is_empty() {
        // TODO: We will be able to type this once we have annotated patterns!
        unimplemented!("type annotations needed");
    }

    let (body, body_ty) = match concrete_body_ty {
        None => synth_term(context, concrete_body)?,
        Some(concrete_body_ty) => {
            let body_ty = context.eval(&check_term_ty(context, concrete_body_ty)?)?;
            let body = check_term(context, concrete_body, &body_ty)?;
            (body, body_ty)
        },
    };

    Ok((
        param_names
            .iter()
            .fold(body, |acc, _| core::RcTerm::from(core::Term::FunIntro(acc))),
        body_ty,
    ))
}

/// Check that a given term conforms to an expected type
pub fn check_term<'term>(
    context: &Context<'term>,
    concrete_term: &'term Term,
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
                context.insert_local(def_name, def_value, def_ty);
                check_term(&context, concrete_body, expected_ty)?
            };

            Ok(core::RcTerm::from(core::Term::Let(def, body)))
        },
        Term::Parens(concrete_term) => check_term(context, concrete_term, expected_ty),

        Term::FunType(concrete_params, concrete_body_ty) => {
            let mut context = context.clone();
            let mut param_tys = Vec::new();

            for (param_names, concrete_param_ty) in concrete_params {
                for param_name in param_names {
                    let param_ty = check_term(&context, concrete_param_ty, expected_ty)?;
                    context.insert_binder(param_name, context.eval(&param_ty)?);
                    param_tys.push(param_ty);
                }
            }

            Ok(param_tys.into_iter().rev().fold(
                check_term(&context, concrete_body_ty, expected_ty)?,
                |acc, param_ty| core::RcTerm::from(core::Term::FunType(param_ty, acc)),
            ))
        },
        Term::FunArrowType(concrete_param_ty, concrete_body_ty) => {
            let param_ty = check_term(context, concrete_param_ty, expected_ty)?;
            let param_ty_value = context.eval(&param_ty)?;
            let body_ty = {
                let mut context = context.clone();
                context.insert_binder(None, param_ty_value);
                check_term(&context, concrete_body_ty, expected_ty)?
            };

            Ok(core::RcTerm::from(core::Term::FunType(param_ty, body_ty)))
        },
        Term::FunIntro(param_names, concrete_body) => {
            check_fun_intro(context, param_names, None, concrete_body, expected_ty)
        },

        Term::PairType(fst_name, concrete_fst_ty, concrete_snd_ty) => {
            let fst_ty = check_term(context, concrete_fst_ty, expected_ty)?;
            let fst_ty_value = context.eval(&fst_ty)?;
            let snd_ty = {
                let mut context = context.clone();
                context.insert_binder(fst_name, fst_ty_value);
                check_term(&context, concrete_snd_ty, expected_ty)?
            };

            Ok(core::RcTerm::from(core::Term::PairType(fst_ty, snd_ty)))
        },
        Term::PairIntro(concrete_fst, concrete_snd) => match expected_ty.as_ref() {
            domain::Value::PairType(fst_ty, snd_ty) => {
                let fst = check_term(context, concrete_fst, fst_ty)?;
                let fst_value = context.eval(&fst)?;
                let snd_ty_value = nbe::do_closure_app(snd_ty, fst_value)?;
                let snd = check_term(context, concrete_snd, &snd_ty_value)?;

                Ok(core::RcTerm::from(core::Term::PairIntro(fst, snd)))
            },
            _ => Err(TypeError::ExpectedPairType {
                found: expected_ty.clone(),
            }),
        },

        Term::Universe(term_level) => {
            let term_level = UniverseLevel::from(term_level.unwrap_or(0));
            match expected_ty.as_ref() {
                domain::Value::Universe(ann_level) if term_level < *ann_level => {
                    Ok(core::RcTerm::from(core::Term::Universe(term_level)))
                },
                _ => Err(TypeError::ExpectedUniverse {
                    over: Some(term_level),
                    found: expected_ty.clone(),
                }),
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
pub fn synth_term<'term>(
    context: &Context<'term>,
    concrete_term: &'term Term,
) -> Result<(core::RcTerm, domain::RcType), TypeError> {
    log::trace!("synthesizing term:\t\t{}", concrete_term);

    match concrete_term {
        Term::Var(name) => match context.lookup_binder(name.as_str()) {
            None => Err(TypeError::UnboundVariable(name.clone())),
            Some((index, ann)) => Ok((core::RcTerm::from(core::Term::Var(index)), ann.clone())),
        },
        Term::Literal(literal) => unimplemented!("literals: {:?}", literal),
        Term::Let(def_name, concrete_def, concrete_body) => {
            let (def, def_ty) = synth_term(context, concrete_def)?;
            let def_value = context.eval(&def)?;
            let (body, body_ty) = {
                let mut context = context.clone();
                context.insert_local(def_name, def_value, def_ty);
                synth_term(&context, concrete_body)?
            };

            Ok((core::RcTerm::from(core::Term::Let(def, body)), body_ty))
        },
        Term::Ann(concrete_term, concrete_term_ty) => {
            let term_ty = context.eval(&check_term_ty(context, concrete_term_ty)?)?;
            let term = check_term(context, concrete_term, &term_ty)?;

            Ok((term, term_ty))
        },
        Term::Parens(concrete_term) => synth_term(context, concrete_term),

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

        Term::PairFst(concrete_pair) => {
            let (pair, pair_ty) = synth_term(context, concrete_pair)?;
            match pair_ty.as_ref() {
                domain::Value::PairType(fst_ty, _) => {
                    let fst = core::RcTerm::from(core::Term::PairFst(pair.clone()));
                    Ok((fst, fst_ty.clone()))
                },
                _ => Err(TypeError::ExpectedPairType {
                    found: pair_ty.clone(),
                }),
            }
        },
        Term::PairSnd(concrete_pair) => {
            let (pair, pair_ty) = synth_term(context, concrete_pair)?;
            match pair_ty.as_ref() {
                domain::Value::PairType(_, snd_ty) => {
                    let fst = core::RcTerm::from(core::Term::PairFst(pair.clone()));
                    let fst_value = context.eval(&fst)?;
                    let snd = core::RcTerm::from(core::Term::PairSnd(pair));

                    Ok((snd, nbe::do_closure_app(snd_ty, fst_value)?))
                },
                _ => Err(TypeError::ExpectedPairType {
                    found: pair_ty.clone(),
                }),
            }
        },

        _ => Err(TypeError::AmbiguousTerm(concrete_term.clone())),
    }
}

/// Check that the given term is a type
pub fn check_term_ty<'term>(
    context: &Context<'term>,
    concrete_term: &'term Term,
) -> Result<core::RcTerm, TypeError> {
    log::trace!("checking term is type:\t{}", concrete_term);

    match concrete_term {
        Term::Let(def_name, concrete_def, concrete_body) => {
            let (def, def_ty) = synth_term(context, concrete_def)?;
            let def_value = context.eval(&def)?;
            let body = {
                let mut context = context.clone();
                context.insert_local(def_name, def_value, def_ty);
                check_term_ty(&context, concrete_body)?
            };

            Ok(core::RcTerm::from(core::Term::Let(def, body)))
        },
        Term::Parens(concrete_term) => check_term_ty(context, concrete_term),

        Term::FunType(concrete_params, concrete_body_ty) => {
            let mut context = context.clone();
            let mut param_tys = Vec::new();

            for (param_names, concrete_param_ty) in concrete_params {
                for param_name in param_names {
                    let param_ty = check_term_ty(&context, concrete_param_ty)?;
                    context.insert_binder(param_name, context.eval(&param_ty)?);
                    param_tys.push(param_ty);
                }
            }

            Ok(param_tys.into_iter().rev().fold(
                check_term_ty(&context, concrete_body_ty)?,
                |acc, param_ty| core::RcTerm::from(core::Term::FunType(param_ty, acc)),
            ))
        },
        Term::FunArrowType(concrete_param_ty, concrete_body_ty) => {
            let param_ty = check_term_ty(context, concrete_param_ty)?;
            let param_ty_value = context.eval(&param_ty)?;
            let body_ty = {
                let mut context = context.clone();
                context.insert_binder(None, param_ty_value);
                check_term_ty(&context, concrete_body_ty)?
            };

            Ok(core::RcTerm::from(core::Term::FunType(param_ty, body_ty)))
        },

        Term::PairType(fst_name, concrete_fst_ty, concrete_snd_ty) => {
            let fst_ty = check_term_ty(context, concrete_fst_ty)?;
            let fst_ty_value = context.eval(&fst_ty)?;
            let snd_ty = {
                let mut snd_ty_context = context.clone();
                snd_ty_context.insert_binder(fst_name, fst_ty_value);
                check_term_ty(&snd_ty_context, concrete_snd_ty)?
            };

            Ok(core::RcTerm::from(core::Term::PairType(fst_ty, snd_ty)))
        },

        Term::Universe(level) => {
            let level = UniverseLevel::from(level.unwrap_or(0));
            Ok(core::RcTerm::from(core::Term::Universe(level)))
        },

        _ => {
            let (term, term_ty) = synth_term(context, concrete_term)?;
            match term_ty.as_ref() {
                domain::Value::Universe(_) => Ok(term),
                _ => Err(TypeError::ExpectedUniverse {
                    over: None,
                    found: term_ty,
                }),
            }
        },
    }
}
