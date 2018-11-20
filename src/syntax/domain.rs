//! The semantic domain

use im;
use std::rc::Rc;

use syntax::core::RcTerm;
use syntax::{DbLevel, UniverseLevel};

pub type Env = im::Vector<RcValue>;

/// A Closure that binds one variable
#[derive(Debug, Clone, PartialEq)]
pub enum Closure {
    Closure { term: RcTerm, env: Env },
    Const(RcValue),
}

/// A closure that bninds two variables
#[derive(Debug, Clone, PartialEq)]
pub struct Closure2 {
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
    Neutral { ann: RcValue, term: RcNeutral },

    /// Type of natural numbers
    NatType,
    /// The natural number zero
    NatZero,
    /// The successor of a natural number
    NatSucc(RcValue),

    /// Dependent function types
    FunType(RcValue, Closure),
    /// Introduce a function
    FunIntro(Closure),

    /// Dependent pair types
    PairType(RcValue, Closure),
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

    /// Recursively eliminate a natural number
    NatRec(Closure, RcValue, Closure2, RcNeutral),
}

/// Associates a type with a value so that later during quotation we can eta
/// expand it appropriately
#[derive(Debug, Clone, PartialEq)]
pub struct Nf {
    pub ann: RcValue,
    pub term: RcValue,
}
