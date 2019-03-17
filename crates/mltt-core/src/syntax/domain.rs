//! The semantic domain

use std::ops;
use std::rc::Rc;

use crate::syntax::core::{RcTerm, Term};
use crate::syntax::{
    AppMode, Env, Label, LiteralIntro, LiteralType, UniverseLevel, UniverseShift, VarLevel,
};

/// A closure that binds a single variable.
///
/// We can think of these closures as a limited form of [_explicit substitutions_].
/// They allow us to avoid eagerly substituting under binders when evaluating
/// terms.
///
/// [_explicit substitutions_]: https://en.wikipedia.org/wiki/Explicit_substitution
#[derive(Debug, Clone, PartialEq)]
pub struct Closure {
    /// The term that the argument will be applied to.
    pub term: RcTerm,
    /// The environment in which we'll run the term in.
    ///
    /// At the moment this captures the _entire_ environment - would it be
    /// better to only capture what the `term` needs?
    pub env: Env<RcValue>,
}

impl Closure {
    pub fn new(term: RcTerm, env: Env<RcValue>) -> Closure {
        Closure { term, env }
    }

    pub fn lift(&mut self, shift: UniverseShift) {
        self.term = RcTerm::from(Term::Lift(self.term.clone(), shift));
        self.env.lift(shift);
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

impl ops::Deref for RcValue {
    type Target = Value;

    fn deref(&self) -> &Value {
        self.as_ref()
    }
}

impl RcValue {
    /// Construct a variable
    pub fn var(level: VarLevel, shift: Option<UniverseShift>) -> RcValue {
        RcValue::from(Value::var(level, shift))
    }

    pub fn lift(&mut self, shift: UniverseShift) {
        Rc::make_mut(&mut self.inner).lift(shift);
    }
}

/// Terms that are in _weak head normal form_
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
    Neutral(Head, Option<UniverseShift>, Spine),

    /// Literal types
    LiteralType(LiteralType),
    /// Literal introductions
    LiteralIntro(LiteralIntro),

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
    pub fn var(level: VarLevel, shift: Option<UniverseShift>) -> Value {
        Value::Neutral(Head::Var(level.into()), shift, Vec::new())
    }

    pub fn lift(&mut self, shift: UniverseShift) {
        match self {
            Value::Neutral(_, head_shift, spine) => {
                if let Some(ref mut head_shift) = head_shift {
                    *head_shift += shift;
                }
                for elim in spine {
                    elim.lift(shift);
                }
            },
            Value::LiteralIntro(_) => {},
            Value::LiteralType(_) => {},
            Value::FunType(_, param_ty, body_ty) => {
                param_ty.lift(shift);
                body_ty.lift(shift);
            },
            Value::FunIntro(_, body) => body.lift(shift),
            Value::RecordTypeExtend(_, ty, rest) => {
                ty.lift(shift);
                rest.lift(shift);
            },
            Value::RecordTypeEmpty => {},
            Value::RecordIntro(fields) => {
                for (_, term) in fields {
                    term.lift(shift);
                }
            },
            Value::Universe(ref mut level) => *level += shift,
        }
    }
}

/// Alias for types - we are using describing a dependently typed language
/// types, so this is just an alias
pub type Type = Value;

/// Alias for reference counted types - we are using describing a dependently
/// typed language types, so this is just an alias
pub type RcType = RcValue;

/// The head of a neutral term
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Head {
    /// Variables
    Var(VarLevel),
}

/// A spine of eliminators
pub type Spine = Vec<Elim>;

/// An eliminator
#[derive(Debug, Clone, PartialEq)]
pub enum Elim {
    /// Function elimination (application)
    Fun(AppMode, RcValue),
    /// Record elimination (projection)
    Record(Label),
}

impl Elim {
    pub fn lift(&mut self, shift: UniverseShift) {
        match self {
            Elim::Fun(_, arg) => arg.lift(shift),
            Elim::Record(_) => {},
        }
    }
}
