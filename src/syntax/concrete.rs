//! The concrete syntax

use syntax::UniverseLevel;

pub type Ident = String;

pub type Signature = Vec<Item>;

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    Definition { name: Ident, def: Term, ann: Term },
    NormalizeDefinition(Ident),
    NormalizeTerm { term: Term, ann: Term },
    Quit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// Variables
    Var(Ident),
    /// Let bindings
    Let(Ident, Box<Term>, Box<Term>),
    /// A term that is explicitly annotated with a type
    Check(Box<Term>, Box<Term>),

    /// Type of natural numbers
    NatType,
    /// Construct the successor of a natural number
    NatSucc(Box<Term>),
    /// Construct a natural number from a literal integer
    NatLit(u32),
    /// Recursively eliminate a natural number
    NatRec {
        motive: (Ident, Box<Term>),
        zero: Box<Term>,
        succ: (Ident, Ident, Box<Term>),
        nat: Box<Term>,
    },

    /// Dependent function type
    FunType(Ident, Box<Term>, Box<Term>),
    /// Introduce a function
    FunIntro(Ident, Box<Term>),
    /// Apply a function to an argument
    FunApp(Box<Term>, Vec<Term>),

    /// Dependent pair type
    PairType(Ident, Box<Term>, Box<Term>),
    /// Introduce a pair
    PairIntro(Box<Term>, Box<Term>),
    /// Project the first element of a pair
    PairFst(Box<Term>),
    /// Project the second element of a pair
    PairSnd(Box<Term>),

    /// Universe of types
    Universe(UniverseLevel),
}
