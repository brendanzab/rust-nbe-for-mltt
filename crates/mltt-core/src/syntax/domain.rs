//! The semantic domain

use std::rc::Rc;

use crate::syntax::core::RcTerm;
use crate::syntax::{AppMode, DbLevel, Label, Literal, UniverseLevel};

/// An environment of values
pub type Env = im::Vector<RcValue>;

/// A closure that binds a variable
#[derive(Debug, Clone, PartialEq)]
pub struct Closure {
    /// The term that the argument will be applied to.
    pub term: RcTerm,
    /// The environment in which we'll run the term in.
    ///
    /// At the moment this captures the _entire_ environment - would it be
    /// better to only capture what the `term` needs?
    pub env: Env,
}

impl Closure {
    pub fn new(term: RcTerm, env: Env) -> Closure {
        Closure { term, env }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RcValue {
    pub inner: Rc<Value>,
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

impl RcValue {
    /// Construct a variable
    pub fn var(level: impl Into<DbLevel>) -> RcValue {
        RcValue::from(Value::var(level))
    }
}

/// Terms that are in _weak head normal form_
///
/// These can either be _neutral values_ (values that are stuck on a variable),
/// or _canonical values_.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// Neutral values
    Neutral(RcNeutral),

    /// Literals
    Literal(Literal),

    /// Dependent function types
    FunType(AppMode, RcType, Closure),
    /// Introduce a function
    FunIntro(AppMode, Closure),

    /// Dependent record type extension
    RecordTypeExtend(Label, RcType, Closure),
    /// Empty record type
    RecordTypeEmpty,
    /// Introduce a record
    RecordIntro(Vec<(Label, RcValue)>),

    /// Universe of types
    Universe(UniverseLevel),
}

impl Value {
    /// Construct a variable
    pub fn var(level: impl Into<DbLevel>) -> Value {
        Value::Neutral(RcNeutral::from(Neutral::Var(level.into())))
    }
}

/// Alias for types - we are using describing a dependently typed language
/// types, so this is just an alias
pub type Type = Value;

/// Alias for reference counted types - we are using describing a dependently
/// typed language types, so this is just an alias
pub type RcType = RcValue;

#[derive(Debug, Clone, PartialEq)]
pub struct RcNeutral {
    pub inner: Rc<Neutral>,
}

impl From<Neutral> for RcNeutral {
    fn from(src: Neutral) -> RcNeutral {
        RcNeutral {
            inner: Rc::new(src),
        }
    }
}

impl AsRef<Neutral> for RcNeutral {
    fn as_ref(&self) -> &Neutral {
        self.inner.as_ref()
    }
}

/// Terms for which computation has stopped because of an attempt to evaluate a
/// variable
///
/// These are known as _neutral values_ or _accumulators_.
#[derive(Debug, Clone, PartialEq)]
pub enum Neutral {
    /// Variables
    Var(DbLevel),

    /// Apply a function to an argument
    FunApp(RcNeutral, AppMode, RcValue),

    /// Project on a record
    RecordProj(RcNeutral, Label),
}
