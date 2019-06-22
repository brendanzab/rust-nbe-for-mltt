//! The semantic domain.

use std::rc::Rc;

use crate::literal::{LiteralIntro, LiteralType};
use crate::syntax::Term;
use crate::{global, meta, prim, var, AppMode, DocString, Label, UniverseLevel};

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
    FunType(AppMode, Option<String>, Rc<Type>, AppClosure),
    /// Introduce a function
    FunIntro(AppMode, Option<String>, AppClosure),

    /// Dependent record type extension
    RecordTypeExtend(DocString, Label, Option<String>, Rc<Type>, AppClosure),
    /// Empty record type
    RecordTypeEmpty,
    /// Introduce a record
    RecordIntro(Vec<(Label, Rc<Value>)>),

    /// Universe of types
    Universe(UniverseLevel),
}

impl Value {
    /// Construct a variable.
    pub fn var(level: impl Into<var::Level>) -> Value {
        Value::Neutral(Head::Var(level.into()), Vec::new())
    }

    /// Construct a metavariable.
    pub fn meta(index: impl Into<meta::Index>) -> Value {
        Value::Neutral(Head::Meta(index.into()), Vec::new())
    }

    /// Construct a global.
    pub fn global(name: impl Into<global::Name>) -> Value {
        Value::Neutral(Head::Global(name.into()), Vec::new())
    }

    /// Construct a primitive.
    pub fn prim(name: impl Into<prim::Name>) -> Value {
        Value::Neutral(Head::Prim(name.into()), Vec::new())
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

/// The head of a neutral term.
#[derive(Debug, Clone, PartialEq)]
pub enum Head {
    /// Variables
    Var(var::Level),
    /// Metavariables
    Meta(meta::Index),
    /// Globals
    Global(global::Name),
    /// Primitives
    Prim(prim::Name),
}

/// A spine of eliminators.
pub type Spine = Vec<Elim>;

/// An eliminator.
#[derive(Debug, Clone, PartialEq)]
pub enum Elim {
    /// Literal elimination (case split).
    Literal(LiteralClosure),
    /// Function elimination (application).
    Fun(AppMode, Rc<Value>),
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
    pub term: Rc<Term>,
    /// The environment in which we'll run the term in.
    ///
    /// At the moment this captures the _entire_ environment - would it be
    /// better to only capture what the `term` needs?
    pub values: var::Env<Rc<Value>>,
}

impl AppClosure {
    pub fn new(term: Rc<Term>, values: var::Env<Rc<Value>>) -> AppClosure {
        AppClosure { term, values }
    }
}

/// A closure that stores a list of clauses.
#[derive(Debug, Clone, PartialEq)]
pub struct LiteralClosure {
    /// The clauses.
    pub clauses: Rc<[(LiteralIntro, Rc<Term>)]>,
    /// The default term.
    pub default: Rc<Term>,
    /// The environment in which we'll run the clauses in.
    ///
    /// At the moment this captures the _entire_ environment - would it be
    /// better to only capture what the `term` needs?
    pub values: var::Env<Rc<Value>>,
}

impl LiteralClosure {
    pub fn new(
        clauses: Rc<[(LiteralIntro, Rc<Term>)]>,
        default: Rc<Term>,
        values: var::Env<Rc<Value>>,
    ) -> LiteralClosure {
        LiteralClosure {
            clauses,
            default,
            values,
        }
    }
}
