//! The semantic domain

use im;
use std::rc::Rc;

use syntax::core::RcTerm;
use syntax::{DbLevel, UniverseLevel};

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
    pub fn var(level: impl Into<DbLevel>, ann: impl Into<RcValue>) -> RcValue {
        RcValue::from(Value::var(level, ann))
    }
}

/// Values are terms that have evaluated to a constructor that does not need to
/// be reduced further
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// Neutral values
    Neutral { ann: RcType, term: RcNeutral },

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
    pub fn var(level: impl Into<DbLevel>, ann: impl Into<RcValue>) -> Value {
        Value::Neutral {
            ann: ann.into(),
            term: RcNeutral::from(Neutral::Var(level.into())),
        }
    }
}

pub type Type = Value;

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

/// Terms that want to reduce further, but cannot because they blocked on
/// something
#[derive(Debug, Clone, PartialEq)]
pub enum Neutral {
    /// Variables
    Var(DbLevel),

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
    pub ann: RcType,
    pub term: RcValue,
}
