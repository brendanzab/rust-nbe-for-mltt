//! The semantic domain.

use std::ops;
use std::rc::Rc;

use crate::syntax::core::RcTerm;
use crate::syntax::{AppMode, Env, Label, LiteralIntro, LiteralType, UniverseLevel, VarLevel};

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
pub struct ClauseClosure {
    /// The clauses
    pub clauses: Rc<[(LiteralIntro, RcTerm)]>,
    /// The environment in which we'll run the clauses in.
    ///
    /// At the moment this captures the _entire_ environment - would it be
    /// better to only capture what the `term` needs?
    pub env: Env<RcValue>,
}

impl ClauseClosure {
    pub fn new(clauses: Rc<[(LiteralIntro, RcTerm)]>, env: Env<RcValue>) -> ClauseClosure {
        ClauseClosure { clauses, env }
    }

    pub fn match_literal(&self, literal_intro: &LiteralIntro) -> Option<&RcTerm> {
        use std::cmp::Ordering;

        let index = self.clauses.binary_search_by(|(l, _)| {
            l.partial_cmp(literal_intro).unwrap_or(Ordering::Greater) // NaN?
        });

        match index {
            Ok(index) => self.clauses.get(index).map(|(_, body)| body),
            Err(_) => None,
        }
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
    pub fn var(level: impl Into<VarLevel>) -> RcValue {
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
    RecordTypeExtend(Label, RcType, AppClosure),
    /// Empty record type
    RecordTypeEmpty,
    /// Introduce a record
    RecordIntro(Vec<(Label, RcValue)>),

    /// Universe of types
    Universe(UniverseLevel),
}

impl Value {
    /// Construct a variable
    pub fn var(level: impl Into<VarLevel>) -> Value {
        Value::Neutral(Head::Var(level.into()), Vec::new())
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
    /// Literal elimination (case split)
    Literal(ClauseClosure, AppClosure),
    /// Function elimination (application)
    Fun(AppMode, RcValue),
    /// Record elimination (projection)
    Record(Label),
}
