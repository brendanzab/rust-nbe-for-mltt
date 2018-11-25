//! The semantic domain

use im;
use std::rc::Rc;

use syntax::core::RcTerm;
use syntax::{DbLevel, IdentHint, UniverseLevel};

pub type Env = im::Vector<RcValue>;

/// A closure that binds a variable
#[derive(Debug, Clone, PartialEq)]
pub struct Closure {
    pub term: RcTerm,
    pub env: Env,
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

impl RcValue {
    /// Construct a variable
    pub fn var(
        ident: impl Into<IdentHint>,
        level: impl Into<DbLevel>,
        ann: impl Into<RcValue>,
    ) -> RcValue {
        RcValue::from(Value::var(ident, level, ann))
    }
}

/// Terms that are in _weak head normal form_
///
/// These can either be _neutral values_ (values that are stuck on a variable),
/// or _canonical values_.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// Neutral values, annotated with a type
    Neutral(RcNeutral, RcType),

    /// Dependent function types
    FunType(IdentHint, RcType, Closure),
    /// Introduce a function
    FunIntro(IdentHint, Closure),

    /// Dependent pair types
    PairType(IdentHint, RcType, Closure),
    /// Introduce a pair
    PairIntro(RcValue, RcValue),

    /// Universe of types
    Universe(UniverseLevel),
}

impl Value {
    /// Construct a variable
    pub fn var(
        ident: impl Into<IdentHint>,
        level: impl Into<DbLevel>,
        ann: impl Into<RcValue>,
    ) -> Value {
        Value::Neutral(
            RcNeutral::from(Neutral::Var(ident.into(), level.into())),
            ann.into(),
        )
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

/// Terms for which computation has stopped because of an attempt to evaluate a
/// variable
///
/// These are known as _neutral values_ or _accumulators_.
#[derive(Debug, Clone, PartialEq)]
pub enum Neutral {
    /// Variables
    Var(IdentHint, DbLevel),

    /// Apply a function to an argument
    FunApp(RcNeutral, Nf),

    /// Project the first element of a pair
    PairFst(RcNeutral),
    /// Project the second element of a pair
    PairSnd(RcNeutral),
}

/// Associates a type with a value so that later during quotation we can eta
/// expand it appropriately
#[derive(Debug, Clone, PartialEq)]
pub struct Nf {
    pub term: RcValue,
    pub ann: RcType,
}

impl Nf {
    pub fn new(term: impl Into<RcValue>, ann: impl Into<RcType>) -> Nf {
        Nf {
            term: term.into(),
            ann: ann.into(),
        }
    }
}
