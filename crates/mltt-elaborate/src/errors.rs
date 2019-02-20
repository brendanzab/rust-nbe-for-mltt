use mltt_concrete::Term;
use mltt_core::nbe::NbeError;
use mltt_core::syntax::{domain, AppMode};
use std::error::Error;
use std::fmt;

/// An error produced during type checking
#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    AlreadyDeclared(String),
    AlreadyDefined(String),
    AlreadyDocumented(String),
    ExpectedFunType { found: domain::RcType },
    ExpectedPairType { found: domain::RcType },
    ExpectedUniverse { found: domain::RcType },
    ExpectedSubtype(domain::RcType, domain::RcType),
    AmbiguousTerm(Term),
    UnboundVariable(String),
    NoFieldInType(String),
    UnexpectedField { found: String, expected: String },
    UnexpectedAppMode { found: AppMode, expected: AppMode },
    TooManyFieldsFound,
    NotEnoughFieldsProvided,
    Nbe(NbeError),
}

impl From<NbeError> for TypeError {
    fn from(src: NbeError) -> TypeError {
        TypeError::Nbe(src)
    }
}

impl Error for TypeError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            TypeError::Nbe(error) => Some(error),
            _ => None,
        }
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::AlreadyDeclared(name) => write!(f, "already declared: `{}`", name),
            TypeError::AlreadyDefined(name) => write!(f, "already defined: `{}`", name),
            TypeError::AlreadyDocumented(name) => write!(f, "already documented: `{}`", name),
            TypeError::ExpectedFunType { .. } => write!(f, "expected function type"),
            TypeError::ExpectedPairType { .. } => write!(f, "expected function type"),
            TypeError::ExpectedUniverse { .. } => write!(f, "expected universe"),
            TypeError::ExpectedSubtype(..) => write!(f, "not a subtype"),
            TypeError::AmbiguousTerm(..) => write!(f, "could not infer the type"),
            TypeError::UnboundVariable(name) => write!(f, "unbound variable `{}`", name),
            TypeError::NoFieldInType(label) => write!(f, "no field in type `{}`", label),
            TypeError::UnexpectedField { found, expected } => write!(
                f,
                "unexpected field, found `{}`, but expected `{}`",
                found, expected,
            ),
            TypeError::UnexpectedAppMode { found, expected } => write!(
                f,
                "unexpected application mode, found `{:?}`, but expected `{:?}`",
                found, expected,
            ),
            TypeError::TooManyFieldsFound => write!(f, "too many fields found"),
            TypeError::NotEnoughFieldsProvided => write!(f, "not enough fields provided"),
            TypeError::Nbe(err) => err.fmt(f),
        }
    }
}
