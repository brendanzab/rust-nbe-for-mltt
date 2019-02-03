//! The semantic domain

use im;
use std::rc::Rc;

use crate::syntax::core::RcTerm;
use crate::syntax::{DbLevel, Literal, UniverseLevel};

pub type Env = im::Vector<RcValue>;

/// A closure that binds a variable
#[derive(Debug, Clone, PartialEq)]
pub struct Closure {
    pub term: RcTerm,
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
    FunType(RcType, Closure),
    /// Introduce a function
    FunIntro(Closure),

    /// Dependent pair types
    PairType(RcType, Closure),
    /// Introduce a pair
    PairIntro(RcValue, RcValue),

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
    FunApp(RcNeutral, RcValue),

    /// Project the first element of a pair
    PairFst(RcNeutral),
    /// Project the second element of a pair
    PairSnd(RcNeutral),
}
