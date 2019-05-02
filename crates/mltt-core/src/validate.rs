//! Bidirectional type checking of the core syntax.
//!
//! This is used to verify that the core syntax is correctly formed, for
//! debugging purposes. We assume that all metavariables have been solved by
//! this stage.

use itertools::Itertools;
use std::error::Error;
use std::fmt;

use super::literal::{LiteralIntro, LiteralType};
use crate::domain::{AppClosure, RcType, RcValue, Value};
use crate::env::Env;
use crate::nbe;
use crate::syntax::{Item, Module, RcTerm, Term};
use crate::{AppMode, Label, MetaEnv, MetaLevel, MetaSolution, UniverseLevel, VarIndex};

/// Local type checking context.
#[derive(Debug, Clone)]
pub struct Context {
    /// Primitive entries.
    prims: nbe::PrimEnv,
    /// Values to be used during evaluation.
    values: Env<RcValue>,
    /// Types of the entries in the context.
    tys: Env<RcType>,
}

impl Context {
    /// Create a new, empty context.
    pub fn new() -> Context {
        Context {
            prims: nbe::PrimEnv::new(),
            values: Env::new(),
            tys: Env::new(),
        }
    }

    /// Primitive entries.
    pub fn prims(&self) -> &nbe::PrimEnv {
        &self.prims
    }

    /// Values to be used during evaluation.
    pub fn values(&self) -> &Env<RcValue> {
        &self.values
    }

    /// Lookup the type of a variable in the context.
    pub fn lookup_ty(&self, var_index: VarIndex) -> Option<&RcType> {
        self.tys.lookup_entry(var_index)
    }

    /// Add a definition to the context.
    pub fn add_defn(&mut self, value: RcValue, ty: RcType) {
        log::trace!("add definition");
        self.values.add_entry(value);
        self.tys.add_entry(ty);
    }

    /// Add a bound variable the context, returning a variable that points to
    /// the correct binder.
    pub fn add_param(&mut self, ty: RcType) -> RcValue {
        log::trace!("add parameter");
        let value = RcValue::var(self.values.size().next_var_level());
        self.values.add_entry(value.clone());
        self.tys.add_entry(ty);
        value
    }

    /// Apply a closure to an argument.
    pub fn app_closure(
        &self,
        metas: &MetaEnv,
        closure: &AppClosure,
        arg: RcValue,
    ) -> Result<RcValue, TypeError> {
        nbe::app_closure(self.prims(), metas, closure, arg).map_err(TypeError::Nbe)
    }

    /// Evaluate a term using the evaluation environment.
    pub fn eval_term(&self, metas: &MetaEnv, term: &RcTerm) -> Result<RcValue, TypeError> {
        nbe::eval_term(self.prims(), metas, self.values(), term).map_err(TypeError::Nbe)
    }

    /// Expect that `ty1` is a subtype of `ty2` in the current context.
    pub fn check_subtype(
        &self,
        metas: &MetaEnv,
        ty1: &RcType,
        ty2: &RcType,
    ) -> Result<(), TypeError> {
        if nbe::check_subtype(self.prims(), metas, self.values().size(), ty1, ty2)
            .map_err(TypeError::Nbe)?
        {
            Ok(())
        } else {
            Err(TypeError::ExpectedSubtype(ty1.clone(), ty2.clone()))
        }
    }
}

impl Default for Context {
    fn default() -> Context {
        let mut context = Context::new();
        let u0 = RcValue::universe(0);
        let bool = RcValue::literal_ty(LiteralType::Bool);

        context.add_defn(RcValue::literal_ty(LiteralType::String), u0.clone());
        context.add_defn(RcValue::literal_ty(LiteralType::Char), u0.clone());
        context.add_defn(bool.clone(), u0.clone());
        context.add_defn(RcValue::literal_intro(true), bool.clone());
        context.add_defn(RcValue::literal_intro(false), bool.clone());
        context.add_defn(RcValue::literal_ty(LiteralType::U8), u0.clone());
        context.add_defn(RcValue::literal_ty(LiteralType::U16), u0.clone());
        context.add_defn(RcValue::literal_ty(LiteralType::U32), u0.clone());
        context.add_defn(RcValue::literal_ty(LiteralType::U64), u0.clone());
        context.add_defn(RcValue::literal_ty(LiteralType::S8), u0.clone());
        context.add_defn(RcValue::literal_ty(LiteralType::S16), u0.clone());
        context.add_defn(RcValue::literal_ty(LiteralType::S32), u0.clone());
        context.add_defn(RcValue::literal_ty(LiteralType::S64), u0.clone());
        context.add_defn(RcValue::literal_ty(LiteralType::F32), u0.clone());
        context.add_defn(RcValue::literal_ty(LiteralType::F64), u0.clone());

        context.prims = nbe::PrimEnv::default();

        context
    }
}

/// An error produced during type checking.
#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    AlreadyDeclared(Label),
    AlreadyDefined(Label),
    ExpectedFunType { found: RcType },
    ExpectedPairType { found: RcType },
    ExpectedUniverse { found: RcType },
    ExpectedSubtype(RcType, RcType),
    AmbiguousTerm(RcTerm),
    UnboundVariable(VarIndex),
    UnboundMeta(MetaLevel),
    UnsolvedMeta(MetaLevel),
    UnknownPrim(String),
    BadLiteralPatterns(Vec<LiteralIntro>),
    NoFieldInType(Label),
    UnexpectedField { found: Label, expected: Label },
    UnexpectedAppMode { found: AppMode, expected: AppMode },
    TooManyFieldsFound,
    NotEnoughFieldsProvided,
    Nbe(String),
}

impl Error for TypeError {}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::AlreadyDeclared(label) => write!(f, "already declared: {}", label),
            TypeError::AlreadyDefined(label) => write!(f, "already defined: {}", label),
            TypeError::ExpectedFunType { .. } => write!(f, "expected function type"),
            TypeError::ExpectedPairType { .. } => write!(f, "expected function type"),
            TypeError::ExpectedUniverse { .. } => write!(f, "expected universe"),
            TypeError::ExpectedSubtype(..) => write!(f, "not a subtype"),
            TypeError::AmbiguousTerm(..) => write!(f, "could not infer the type"),
            TypeError::UnboundVariable(index) => write!(f, "unbound variable: @{}", index.0),
            TypeError::UnboundMeta(level) => write!(f, "unbound metavariable: `?{}`", level.0),
            TypeError::UnsolvedMeta(level) => write!(f, "unsolved metavariable `?{}`", level.0),
            TypeError::UnknownPrim(name) => write!(f, "unbound primitive: {:?}", name),
            TypeError::BadLiteralPatterns(literal_intros) => write!(
                f,
                "literal patterns are not sorted properly: {}",
                literal_intros.iter().format(", "),
            ),
            TypeError::NoFieldInType(label) => write!(f, "no field in type `{}`", label),
            TypeError::UnexpectedField { found, expected } => write!(
                f,
                "unexpected field, found `{}`, but expected `{}`",
                found, expected,
            ),
            TypeError::UnexpectedAppMode { found, expected } => write!(
                f,
                "unexpected application mode, found `{:?}`, but expected `{:?}`",
                found, expected,
            ),
            TypeError::TooManyFieldsFound => write!(f, "too many fields found"),
            TypeError::NotEnoughFieldsProvided => write!(f, "not enough fields provided"),
            TypeError::Nbe(err) => err.fmt(f),
        }
    }
}

/// Check that this is a valid module.
pub fn check_module(context: &Context, metas: &MetaEnv, module: &Module) -> Result<(), TypeError> {
    let mut context = context.clone();
    check_items(&mut context, metas, &module.items)?;
    Ok(())
}

/// Check the given items and add them to the context.
fn check_items(context: &mut Context, metas: &MetaEnv, items: &[Item]) -> Result<(), TypeError> {
    // Declarations that may be waiting to be defined
    let mut forward_declarations = im::HashMap::new();

    for item in items {
        use im::hashmap::Entry;

        match item {
            Item::Declaration(_, label, term_ty) => {
                log::trace!("checking declaration:\t\t{}\t= {}", label, term_ty);

                match forward_declarations.entry(&label.0) {
                    // No previous declaration for this name was seen, so we can
                    // go-ahead and type check, elaborate, and then add it to
                    // the context
                    Entry::Vacant(entry) => {
                        synth_universe(&context, metas, &term_ty)?;
                        // Ensure that we evaluate the forward declaration in
                        // the current context - if we wait until later more
                        // definitions might have come in to scope!
                        let term_ty = context.eval_term(metas, &term_ty)?;
                        entry.insert(Some(term_ty));
                    },
                    // There's a declaration for this name already pending - we
                    // can't add a new one!
                    Entry::Occupied(_) => return Err(TypeError::AlreadyDeclared(label.clone())),
                }

                log::trace!("validated declaration:\t{}", label);
            },
            Item::Definition(_, label, term) => {
                log::trace!("checking definition:\t\t{}\t= {}", label, term);

                let (term, ty) = match forward_declarations.entry(&label.0) {
                    // No prior declaration was found, so we'll try synthesizing
                    // its type instead
                    Entry::Vacant(entry) => {
                        let term_ty = synth_term(&context, metas, term)?;
                        entry.insert(None);
                        (term, term_ty)
                    },
                    // Something has happened with this declaration, let's
                    // 'take' a look!
                    Entry::Occupied(mut entry) => match entry.get_mut().take() {
                        // We found a prior declaration, so we'll use it as a
                        // basis for checking the definition
                        Some(term_ty) => {
                            check_term(&context, metas, term, &term_ty)?;
                            (term, term_ty)
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

                log::trace!("validated definition:\t{}", label);

                let value = context.eval_term(metas, &term)?;
                context.add_defn(value, ty);
            },
        }
    }

    Ok(())
}

/// Check that a literal conforms to a given type.
pub fn check_literal(
    context: &Context,
    metas: &MetaEnv,
    literal_intro: &LiteralIntro,
    expected_ty: &RcType,
) -> Result<(), TypeError> {
    context.check_subtype(metas, &synth_literal(literal_intro), expected_ty)
}

/// Synthesize the type of the literal.
pub fn synth_literal(literal_intro: &LiteralIntro) -> RcType {
    RcValue::literal_ty(match literal_intro {
        LiteralIntro::String(_) => LiteralType::String,
        LiteralIntro::Char(_) => LiteralType::Char,
        LiteralIntro::Bool(_) => LiteralType::Bool,
        LiteralIntro::U8(_) => LiteralType::U8,
        LiteralIntro::U16(_) => LiteralType::U16,
        LiteralIntro::U32(_) => LiteralType::U32,
        LiteralIntro::U64(_) => LiteralType::U64,
        LiteralIntro::S8(_) => LiteralType::S8,
        LiteralIntro::S16(_) => LiteralType::S16,
        LiteralIntro::S32(_) => LiteralType::S32,
        LiteralIntro::S64(_) => LiteralType::S64,
        LiteralIntro::F32(_) => LiteralType::F32,
        LiteralIntro::F64(_) => LiteralType::F64,
    })
}

/// Ensures that the given term is a universe, returning the level of that universe.
pub fn synth_universe(
    context: &Context,
    metas: &MetaEnv,
    term: &RcTerm,
) -> Result<UniverseLevel, TypeError> {
    let ty = synth_term(context, metas, term)?;
    match ty.as_ref() {
        Value::Universe(level) => Ok(*level),
        _ => Err(TypeError::ExpectedUniverse { found: ty.clone() }),
    }
}

/// Check that a term conforms to a given type.
pub fn check_term(
    context: &Context,
    metas: &MetaEnv,
    term: &RcTerm,
    expected_ty: &RcType,
) -> Result<(), TypeError> {
    log::trace!("checking term:\t\t{}", term);

    match term.as_ref() {
        Term::Prim(name) => match context.prims().lookup_entry(name) {
            None => Err(TypeError::UnknownPrim(name.clone())),
            Some(_) => Ok(()),
        },
        Term::Let(items, body) => {
            let mut context = context.clone();
            check_items(&mut context, metas, items)?;
            check_term(&context, metas, body, expected_ty)
        },

        Term::LiteralElim(scrutinee, clauses, default_body) => {
            let scrutinee_ty = synth_term(context, metas, scrutinee)?;

            // Check that the clauses are sorted by patterns and that patterns aren't duplicated
            // TODO: use `Iterator::is_sorted_by` when it is stable
            if clauses
                .iter()
                .tuple_windows()
                // FIXME: Floating point equality?
                .any(|((l1, _), (l2, _))| l1 >= l2)
            {
                return Err(TypeError::BadLiteralPatterns(
                    clauses.iter().map(|(l, _)| l.clone()).collect(),
                ));
            }

            for (literal_intro, body) in clauses.iter() {
                check_literal(context, metas, literal_intro, &scrutinee_ty)?;
                check_term(context, metas, body, &expected_ty)?;
            }

            check_term(context, metas, default_body, expected_ty)
        },

        Term::FunIntro(intro_app_mode, body) => match expected_ty.as_ref() {
            Value::FunType(ty_app_mode, param_ty, body_ty) if intro_app_mode == ty_app_mode => {
                let mut body_context = context.clone();
                let param = body_context.add_param(param_ty.clone());
                let body_ty = context.app_closure(metas, body_ty, param)?;

                check_term(&body_context, metas, body, &body_ty)
            },
            Value::FunType(ty_app_mode, _, _) => Err(TypeError::UnexpectedAppMode {
                found: intro_app_mode.clone(),
                expected: ty_app_mode.clone(),
            }),
            _ => Err(TypeError::ExpectedFunType {
                found: expected_ty.clone(),
            }),
        },

        Term::RecordIntro(intro_fields) => {
            let mut context = context.clone();
            let mut expected_ty = expected_ty.clone();

            for (label, term) in intro_fields {
                if let Value::RecordTypeExtend(_, expected_label, expected_term_ty, rest) =
                    expected_ty.as_ref()
                {
                    if label != expected_label {
                        return Err(TypeError::UnexpectedField {
                            found: label.clone(),
                            expected: expected_label.clone(),
                        });
                    }

                    check_term(&context, metas, term, expected_term_ty)?;
                    let term_value = context.eval_term(metas, term)?;

                    context.add_defn(term_value.clone(), expected_term_ty.clone());
                    expected_ty = context.app_closure(metas, &rest, term_value)?;
                } else {
                    return Err(TypeError::TooManyFieldsFound);
                }
            }

            if let Value::RecordTypeEmpty = expected_ty.as_ref() {
                Ok(())
            } else {
                Err(TypeError::NotEnoughFieldsProvided)
            }
        },

        _ => {
            let synth_ty = synth_term(context, metas, term)?;
            context.check_subtype(metas, &synth_ty, expected_ty)
        },
    }
}

/// Synthesize the type of the term.
pub fn synth_term(context: &Context, metas: &MetaEnv, term: &RcTerm) -> Result<RcType, TypeError> {
    use std::cmp;

    log::trace!("synthesizing term:\t{}", term);

    match term.as_ref() {
        Term::Var(var_index) => match context.lookup_ty(*var_index) {
            None => Err(TypeError::UnboundVariable(*var_index)),
            Some(ann) => Ok(ann.clone()),
        },
        Term::Meta(meta_level) => match metas.lookup_solution(*meta_level) {
            Some((_, MetaSolution::Solved(_value))) => unimplemented!("synth solved metas"), // FIXME: Type?
            Some((_, MetaSolution::Unsolved)) => Err(TypeError::UnsolvedMeta(*meta_level)),
            None => Err(TypeError::UnboundMeta(*meta_level)),
        },
        Term::Prim(name) => match context.prims().lookup_entry(name) {
            None => Err(TypeError::UnknownPrim(name.clone())),
            Some(_) => Err(TypeError::AmbiguousTerm(term.clone())),
        },

        Term::Ann(term, term_ty) => {
            synth_universe(context, metas, term_ty)?;
            let term_ty = context.eval_term(metas, &term_ty)?;
            check_term(context, metas, term, &term_ty)?;
            Ok(term_ty)
        },
        Term::Let(items, body) => {
            let mut context = context.clone();
            check_items(&mut context, metas, items)?;
            synth_term(&context, metas, body)
        },

        Term::LiteralType(_) => Ok(RcValue::universe(0)),
        Term::LiteralIntro(literal_intro) => Ok(synth_literal(literal_intro)),
        Term::LiteralElim(_, _, _) => Err(TypeError::AmbiguousTerm(term.clone())),

        Term::FunType(_app_mode, param_ty, body_ty) => {
            let param_level = synth_universe(context, metas, param_ty)?;
            let param_ty_value = context.eval_term(metas, param_ty)?;

            let mut body_ty_context = context.clone();
            body_ty_context.add_param(param_ty_value);

            let body_level = synth_universe(&body_ty_context, metas, body_ty)?;

            Ok(RcValue::universe(cmp::max(param_level, body_level)))
        },
        Term::FunIntro(_, _) => Err(TypeError::AmbiguousTerm(term.clone())),

        Term::FunElim(fun, arg_app_mode, arg) => {
            let fun_ty = synth_term(context, metas, fun)?;
            match fun_ty.as_ref() {
                Value::FunType(ty_app_mode, arg_ty, body_ty) if arg_app_mode == ty_app_mode => {
                    check_term(context, metas, arg, arg_ty)?;
                    let arg_value = context.eval_term(metas, arg)?;
                    Ok(context.app_closure(metas, body_ty, arg_value)?)
                },
                Value::FunType(ty_app_mode, _, _) => Err(TypeError::UnexpectedAppMode {
                    found: arg_app_mode.clone(),
                    expected: ty_app_mode.clone(),
                }),
                _ => Err(TypeError::ExpectedFunType {
                    found: fun_ty.clone(),
                }),
            }
        },

        Term::RecordType(ty_fields) => {
            let mut context = context.clone();
            let mut max_level = UniverseLevel(0);

            for (_, _, ty) in ty_fields {
                let ty_level = synth_universe(&context, metas, &ty)?;
                context.add_param(context.eval_term(metas, &ty)?);
                max_level = cmp::max(max_level, ty_level);
            }

            Ok(RcValue::universe(max_level))
        },
        Term::RecordIntro(intro_fields) => {
            if intro_fields.is_empty() {
                Ok(RcValue::from(Value::RecordTypeEmpty))
            } else {
                Err(TypeError::AmbiguousTerm(term.clone()))
            }
        },
        Term::RecordElim(record, label) => {
            let mut record_ty = synth_term(context, metas, record)?;

            while let Value::RecordTypeExtend(_, current_label, current_ty, rest) =
                record_ty.as_ref()
            {
                if label == current_label {
                    return Ok(current_ty.clone());
                } else {
                    let label = current_label.clone();
                    let expr = RcTerm::from(Term::RecordElim(record.clone(), label));
                    record_ty =
                        context.app_closure(metas, rest, context.eval_term(metas, &expr)?)?;
                }
            }

            Err(TypeError::NoFieldInType(label.clone()))
        },

        Term::Universe(level) => Ok(RcValue::universe(*level + 1)),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::{VarIndex, VarLevel};

    #[test]
    fn add_params() {
        let mut context = Context::new();

        let ty1 = RcValue::universe(0);
        let ty2 = RcValue::universe(1);
        let ty3 = RcValue::universe(2);

        let param1 = context.add_param(ty1.clone());
        let param2 = context.add_param(ty2.clone());
        let param3 = context.add_param(ty3.clone());

        assert_eq!(param1, RcValue::from(Value::var(VarLevel(0))));
        assert_eq!(param2, RcValue::from(Value::var(VarLevel(1))));
        assert_eq!(param3, RcValue::from(Value::var(VarLevel(2))));

        assert_eq!(context.lookup_ty(VarIndex(2)).unwrap(), &ty1);
        assert_eq!(context.lookup_ty(VarIndex(1)).unwrap(), &ty2);
        assert_eq!(context.lookup_ty(VarIndex(0)).unwrap(), &ty3);
    }
}
