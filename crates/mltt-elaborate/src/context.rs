//! The elaboration context.

use language_reporting::Diagnostic;
use mltt_core::{domain, meta, prim, syntax, validate, var, AppMode};
use mltt_span::FileSpan;
use pretty::{BoxDoc, Doc};

use crate::{nbe, unify};

/// Local elaboration context.
///
/// This stores the information that we need when elaborating terms from the
/// concrete syntax to the core syntax. This includes primitives, values needed
/// for evaluation, and name-to-level substitutions.
///
/// Persistent data structures are used internally, so it shouldn't be too
/// costly to clone this - for example when entering into new scopes.
#[derive(Debug, Clone)]
pub struct Context {
    /// Primitive entries.
    prims: prim::Env,
    /// Values to be used during evaluation.
    values: var::Env<domain::RcValue>,
    /// Types of the entries in the context.
    tys: var::Env<domain::RcType>,
    /// Names of the entries in the context (used for pretty printing).
    names: var::Env<String>,
    /// Substitutions from the user-defined names to the level in which they
    /// were bound.
    ///
    /// We associate levels to the binder names so that we can recover the
    /// correct debruijn index once we reach a variable name in a nested scope.
    /// Not all entries in the context will have a corresponding name - for
    /// example we don't define a name for non-dependent function types.
    names_to_levels: im::HashMap<String, var::Level>,
    /// Local bound levels.
    ///
    /// This is used for making spines for fresh metas.
    bound_levels: im::Vector<var::Level>,
}

impl Context {
    /// Create a new, empty context.
    pub fn empty() -> Context {
        Context {
            prims: prim::Env::new(),
            values: var::Env::new(),
            tys: var::Env::new(),
            names: var::Env::new(),
            names_to_levels: im::HashMap::new(),
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

    /// Convert the context into a validation context.
    pub fn validation_context(&self) -> validate::Context {
        validate::Context::new(self.prims.clone(), self.values.clone(), self.tys.clone())
    }

    /// Convert the context into a pretty printing environment.
    pub fn pretty_env(&self) -> mltt_core::pretty::Env {
        mltt_core::pretty::Env::new(self.names.clone())
    }

    /// Add a name-to-level substitution to the context.
    pub fn add_name(&mut self, name: impl Into<String>, var_level: var::Level) {
        let name = name.into();
        self.names.add_entry(name.clone());
        self.names_to_levels.insert(name, var_level);
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
        self.add_name(name, var_level);
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
        self.add_name(name, var_level);
        let value = domain::RcValue::var(var_level);
        self.values.add_entry(value.clone());
        self.tys.add_entry(ty);
        value
    }

    /// Create a fresh meta and return the meta applied to all of the currently
    /// bound vars.
    pub fn new_meta(
        &self,
        metas: &mut meta::Env,
        span: FileSpan,
        ty: domain::RcType,
    ) -> syntax::RcTerm {
        let args = self.bound_levels.iter().map(|var_level| {
            let var_index = self.values().size().index(*var_level);
            syntax::RcTerm::var(var_index)
        });

        args.fold(
            syntax::RcTerm::from(syntax::Term::Meta(metas.add_unsolved(span, ty))),
            |acc, arg| syntax::RcTerm::from(syntax::Term::FunElim(acc, AppMode::Explicit, arg)),
        )
    }

    /// Lookup the de-bruijn index and the type annotation of a binder in the
    /// context using a user-defined name.
    pub fn lookup_binder(&self, name: &str) -> Option<(var::Index, &domain::RcType)> {
        let var_level = self.names_to_levels.get(name)?;
        let var_index = self.values().size().index(*var_level);
        let ty = self.tys.lookup_entry(var_index)?;
        log::trace!("lookup binder: {} -> {}", name, var_index);
        Some((var_index, ty))
    }

    /// Apply a closure to an argument.
    pub fn app_closure(
        &self,
        metas: &meta::Env,
        closure: &domain::AppClosure,
        arg: domain::RcValue,
    ) -> Result<domain::RcValue, Diagnostic<FileSpan>> {
        nbe::app_closure(self.prims(), metas, closure, arg)
    }

    /// Evaluate a term using the evaluation environment
    pub fn eval_term(
        &self,
        metas: &meta::Env,
        span: impl Into<Option<FileSpan>>,
        term: &syntax::RcTerm,
    ) -> Result<domain::RcValue, Diagnostic<FileSpan>> {
        nbe::eval_term(self.prims(), metas, self.values(), span, term)
    }

    /// Read a value back into the core syntax, normalizing as required.
    pub fn read_back_value(
        &self,
        metas: &meta::Env,
        span: impl Into<Option<FileSpan>>,
        value: &domain::RcValue,
    ) -> Result<syntax::RcTerm, Diagnostic<FileSpan>> {
        nbe::read_back_value(self.prims(), metas, self.values().size(), span, value)
    }

    /// Fully normalize a term by first evaluating it, then reading it back.
    pub fn normalize_term(
        &self,
        metas: &meta::Env,
        span: impl Into<Option<FileSpan>>,
        term: &syntax::RcTerm,
    ) -> Result<syntax::RcTerm, Diagnostic<FileSpan>> {
        nbe::normalize_term(self.prims(), metas, self.values(), span, term)
    }

    /// Evaluate a value further, if it's now possible due to updates made to the
    /// metavariable solutions.
    pub fn force_value(
        &self,
        metas: &meta::Env,
        span: impl Into<Option<FileSpan>>,
        value: &domain::RcValue,
    ) -> Result<domain::RcValue, Diagnostic<FileSpan>> {
        nbe::force_value(self.prims(), metas, span, value)
    }

    /// Expect that `ty1` is a subtype of `ty2` in the current context
    pub fn unify_values(
        &self,
        metas: &mut meta::Env,
        span: FileSpan,
        value1: &domain::RcValue,
        value2: &domain::RcValue,
    ) -> Result<(), Diagnostic<FileSpan>> {
        unify::unify_values(self.prims(), metas, self.values(), span, value1, value2)
    }

    /// Convert a term to a pretty printable document.
    pub fn term_to_doc(&self, term: &syntax::RcTerm) -> Doc<'_, BoxDoc<'_, ()>> {
        term.to_display_doc(&self.pretty_env())
    }

    /// Convert a value to a pretty printable document.
    pub fn value_to_doc(
        &self,
        metas: &meta::Env,
        value: &domain::RcValue,
    ) -> Doc<'_, BoxDoc<'_, ()>> {
        match self.read_back_value(metas, None, value) {
            Ok(term) => term.to_display_doc(&self.pretty_env()),
            Err(_) => Doc::text("<error pretty printing>"),
        }
    }
}

impl Default for Context {
    fn default() -> Context {
        use mltt_core::domain::RcValue;
        use mltt_core::literal::LiteralType as LitType;

        let mut context = Context::empty();
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn add_params() {
        use mltt_core::domain::{RcValue, Value};

        let mut context = Context::empty();

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

        let mut context = Context::empty();

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

        let mut context = Context::empty();

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
