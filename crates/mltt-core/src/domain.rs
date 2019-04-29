//! The semantic domain.

use std::ops;
use std::rc::Rc;

use super::literal::{LiteralIntro, LiteralType};
use crate::env::Env;
use crate::syntax::RcTerm;
use crate::{AppMode, DocString, Label, MetaLevel, UniverseLevel, VarLevel};

/// Reference counted value.
#[derive(Debug, Clone, PartialEq)]
pub struct RcValue {
    /// The inner value.
    pub inner: Rc<Value>,
}

impl RcValue {
    /// Construct a variable.
    pub fn var(level: impl Into<VarLevel>) -> RcValue {
        RcValue::from(Value::var(level))
    }

    /// Construct a metavariable.
    pub fn meta(level: impl Into<MetaLevel>) -> RcValue {
        RcValue::from(Value::meta(level))
    }

    /// Construct a primitive.
    pub fn prim(name: String) -> RcValue {
        RcValue::from(Value::prim(name))
    }

    /// Construct a literal type.
    pub fn literal_ty(ty: LiteralType) -> RcValue {
        RcValue::from(Value::literal_ty(ty))
    }

    /// Construct a literal introduction.
    pub fn literal_intro(value: impl Into<LiteralIntro>) -> RcValue {
        RcValue::from(Value::literal_intro(value))
    }

    /// Construct a universe.
    pub fn universe(level: impl Into<UniverseLevel>) -> RcValue {
        RcValue::from(Value::universe(level))
    }
}

impl From<Value> for RcValue {
    fn from(src: Value) -> RcValue {
        RcValue {
            inner: Rc::new(src),
        }
    }
}

impl AsRef<Value> for RcValue {
    fn as_ref(&self) -> &Value {
        self.inner.as_ref()
    }
}

impl ops::Deref for RcValue {
    type Target = Value;

    fn deref(&self) -> &Value {
        self.as_ref()
    }
}

/// Terms that are in _weak head normal form_.
///
/// These can either be _neutral values_ (values that are stuck on a variable),
/// or _canonical values_.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// Neutral values
    ///
    /// Terms for which computation has stopped because of an attempt to
    /// evaluate a variable.
    ///
    /// These are known as _neutral values_ or _accumulators_.
    Neutral(Head, Spine),

    /// Literal types
    LiteralType(LiteralType),
    /// Literal introductions
    LiteralIntro(LiteralIntro),

    /// Dependent function types
    FunType(AppMode, RcType, AppClosure),
    /// Introduce a function
    FunIntro(AppMode, AppClosure),

    /// Dependent record type extension
    RecordTypeExtend(DocString, Label, RcType, AppClosure),
    /// Empty record type
    RecordTypeEmpty,
    /// Introduce a record
    RecordIntro(Vec<(Label, RcValue)>),

    /// Universe of types
    Universe(UniverseLevel),
}

impl Value {
    /// Construct a variable.
    pub fn var(level: impl Into<VarLevel>) -> Value {
        Value::Neutral(Head::Var(level.into()), Vec::new())
    }

    /// Construct a metavariable.
    pub fn meta(level: impl Into<MetaLevel>) -> Value {
        Value::Neutral(Head::Meta(level.into()), Vec::new())
    }

    /// Construct a primitive.
    pub fn prim(name: String) -> Value {
        Value::Neutral(Head::Prim(name), Vec::new())
    }

    /// Construct a literal type.
    pub fn literal_ty(ty: LiteralType) -> Value {
        Value::LiteralType(ty)
    }

    /// Construct a literal introduction.
    pub fn literal_intro(value: impl Into<LiteralIntro>) -> Value {
        Value::LiteralIntro(value.into())
    }

    /// Construct a universe.
    pub fn universe(level: impl Into<UniverseLevel>) -> Value {
        Value::Universe(level.into())
    }
}

/// Alias for types - we are using describing a dependently typed language
/// types, so this is just an alias.
pub type Type = Value;

/// Alias for reference counted types - we are using describing a dependently
/// typed language types, so this is just an alias.
pub type RcType = RcValue;

/// The head of a neutral term.
#[derive(Debug, Clone, PartialEq)]
pub enum Head {
    /// Variables
    Var(VarLevel),
    /// Metavariables
    Meta(MetaLevel),
    /// Primitives
    Prim(String),
}

/// A spine of eliminators.
pub type Spine = Vec<Elim>;

/// An eliminator.
#[derive(Debug, Clone, PartialEq)]
pub enum Elim {
    /// Literal elimination (case split).
    Literal(LiteralClosure),
    /// Function elimination (application).
    Fun(AppMode, RcValue),
    /// Record elimination (projection).
    Record(Label),
}

/// A closure that binds a single variable.
///
/// We can think of these closures as a limited form of [_explicit substitutions_].
/// They allow us to avoid eagerly substituting under binders when evaluating
/// terms.
///
/// [_explicit substitutions_]: https://en.wikipedia.org/wiki/Explicit_substitution
#[derive(Debug, Clone, PartialEq)]
pub struct AppClosure {
    /// The term that the argument will be applied to.
    pub term: RcTerm,
    /// The environment in which we'll run the term in.
    ///
    /// At the moment this captures the _entire_ environment - would it be
    /// better to only capture what the `term` needs?
    pub env: Env<RcValue>,
}

impl AppClosure {
    pub fn new(term: RcTerm, env: Env<RcValue>) -> AppClosure {
        AppClosure { term, env }
    }
}

/// A closure that stores a list of clauses.
#[derive(Debug, Clone, PartialEq)]
pub struct LiteralClosure {
    /// The clauses.
    pub clauses: Rc<[(LiteralIntro, RcTerm)]>,
    /// The default term.
    pub default: RcTerm,
    /// The environment in which we'll run the clauses in.
    ///
    /// At the moment this captures the _entire_ environment - would it be
    /// better to only capture what the `term` needs?
    pub env: Env<RcValue>,
}

impl LiteralClosure {
    pub fn new(
        clauses: Rc<[(LiteralIntro, RcTerm)]>,
        default: RcTerm,
        env: Env<RcValue>,
    ) -> LiteralClosure {
        LiteralClosure {
            clauses,
            default,
            env,
        }
    }
}
