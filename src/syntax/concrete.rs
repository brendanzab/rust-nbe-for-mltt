//! The concrete syntax

use syntax::UniverseLevel;

pub type Ident = String;

pub type Signature = Vec<Decl>;

#[derive(Debug, Clone, PartialEq)]
pub enum Decl {
    Def { name: Ident, def: Term, ann: Term },
    NormalizeDef(Ident),
    NormalizeTerm { term: Term, ann: Term },
    Quit,
}

/// A body that binds one variable
#[derive(Debug, Clone, PartialEq)]
pub struct Binder {
    pub name: Ident,
    pub body: Box<Term>,
}

/// A body that binds two variables
#[derive(Debug, Clone, PartialEq)]
pub struct Binder2 {
    pub name1: Ident,
    pub name2: Ident,
    pub body: Box<Term>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// Variables
    Var(Ident),
    /// Let bindings
    Let(Box<Term>, Binder),
    /// A term that is explicitly annotated with a type
    Check { term: Box<Term>, tp: Box<Term> },

    /// Type of natural numbers
    NatType,
    /// Construct the successor of a natural number
    NatSucc(Box<Term>),
    /// Construct a natural number from a literal integer
    NatLit(u32),
    /// Recursively eliminate a natural number
    NatRec {
        motive: Binder,
        zero: Box<Term>,
        suc: Binder2,
        nat: Box<Term>,
    },

    /// Dependent function type
    FunType(Box<Term>, Binder),
    /// Introduce a function
    FunIntro(Binder),
    /// Apply a function to an argument
    FunApp(Box<Term>, Vec<Term>),

    /// Dependent pair type
    PairType(Box<Term>, Binder),
    /// Introduce a pair
    PairIntro(Box<Term>, Box<Term>),
    /// Project the first element of a pair
    PairFst(Box<Term>),
    /// Project the second element of a pair
    PairSnd(Box<Term>),

    /// Universe of types
    Universe(UniverseLevel),
}
