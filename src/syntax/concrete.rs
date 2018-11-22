//! The concrete syntax

use pretty::{BoxDoc, Doc};

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

impl Term {
    // FIXME: Precedences
    pub fn to_doc(&self) -> Doc<BoxDoc<()>> {
        match *self {
            Term::Var(ref ident) => Doc::as_string(ident),
            Term::Let(ref ident, ref def, ref body) => Doc::nil()
                .append("let")
                .append(Doc::as_string(ident))
                .append(Doc::space())
                .append("=")
                .append(Doc::space())
                .append(def.to_doc())
                .append(Doc::space())
                .append("in")
                .append(Doc::space())
                .append(body.to_doc()),
            Term::Check(ref term, ref ann) => Doc::nil()
                .append(term.to_doc())
                .append(Doc::space())
                .append(":")
                .append(Doc::space())
                .append(ann.to_doc()),
            Term::NatType => Doc::text("Nat"),
            Term::NatSucc(ref nat) => Doc::nil()
                .append("succ")
                .append(Doc::space())
                .append(nat.to_doc()),
            Term::NatLit(nat) => Doc::as_string(nat),
            Term::NatRec { .. } => unimplemented!("to_doc: Term::NatRec"),
            Term::FunType(ref ident, ref src_ty, ref dst_ty) => Doc::nil()
                .append(Doc::group(
                    Doc::nil()
                        .append("(")
                        .append(Doc::as_string(ident))
                        .append(Doc::space())
                        .append(":")
                        .append(Doc::space())
                        .append(src_ty.to_doc())
                        .append(")"),
                ))
                .append(Doc::space())
                .append("->")
                .append(Doc::space())
                .append(dst_ty.to_doc()),
            Term::FunIntro(ref ident, ref body) => Doc::nil()
                .append("\\")
                .append(Doc::as_string(ident))
                .append(Doc::space())
                .append("=>")
                .append(Doc::space())
                .append(body.to_doc()),
            Term::FunApp(ref fun, ref args) => Doc::nil()
                .append(fun.to_doc())
                .append(Doc::space())
                .append(Doc::intersperse(
                    args.iter().map(Term::to_doc),
                    Doc::space(),
                )),
            Term::PairType(ref ident, ref fst_ty, ref snd_ty) => Doc::nil()
                .append(Doc::group(
                    Doc::nil()
                        .append("(")
                        .append(Doc::as_string(ident))
                        .append(Doc::space())
                        .append(":")
                        .append(Doc::space())
                        .append(fst_ty.to_doc())
                        .append(")"),
                ))
                .append(Doc::space())
                .append("*")
                .append(Doc::space())
                .append(snd_ty.to_doc()),
            Term::PairIntro(ref fst, ref snd) => Doc::nil()
                .append("<")
                .append(fst.to_doc())
                .append(",")
                .append(Doc::space())
                .append(snd.to_doc())
                .append(">"),
            Term::PairFst(ref pair) => pair.to_doc().append(".1"),
            Term::PairSnd(ref pair) => pair.to_doc().append(".2"),
            Term::Universe(UniverseLevel(level)) => Doc::text("Type").append(Doc::as_string(level)),
        }
    }
}
