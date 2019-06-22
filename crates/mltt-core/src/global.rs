use std::fmt;
use std::rc::Rc;

use crate::domain::{Type, Value};

/// The name of a global.
#[derive(Debug, Clone, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub struct Name(pub String);

impl<'a> From<&'a str> for Name {
    fn from(src: &'a str) -> Name {
        Name(src.to_owned())
    }
}

impl From<String> for Name {
    fn from(src: String) -> Name {
        Name(src)
    }
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// An environment of primitives to use during normalization.
#[derive(Debug, Clone)]
pub struct Env {
    entries: im::HashMap<Name, (Rc<Value>, Rc<Type>)>,
}

impl Env {
    /// Construct a new, empty environment.
    pub fn new() -> Env {
        Env {
            entries: im::HashMap::new(),
        }
    }

    /// Lookup an entry in the environment.
    pub fn lookup_entry(&self, name: &Name) -> Option<&(Rc<Value>, Rc<Type>)> {
        self.entries.get(name)
    }

    /// Add a new entry to the environment.
    pub fn add_entry(&mut self, name: impl Into<Name>, term: Rc<Value>, term_ty: Rc<Type>) {
        self.entries.insert(name.into(), (term, term_ty));
    }
}

impl Default for Env {
    fn default() -> Env {
        use crate::literal::LiteralType;

        let mut env = Env::new();
        let u0 = Rc::from(Value::universe(0));
        let lit_ty = |ty| Rc::from(Value::literal_ty(ty));
        let bool = lit_ty(LiteralType::Bool);

        env.add_entry("String", lit_ty(LiteralType::String), u0.clone());
        env.add_entry("Char", lit_ty(LiteralType::Char), u0.clone());
        env.add_entry("Bool", bool.clone(), u0.clone());
        env.add_entry("true", Rc::from(Value::literal_intro(true)), bool.clone());
        env.add_entry("false", Rc::from(Value::literal_intro(false)), bool.clone());
        env.add_entry("U8", lit_ty(LiteralType::U8), u0.clone());
        env.add_entry("U16", lit_ty(LiteralType::U16), u0.clone());
        env.add_entry("U32", lit_ty(LiteralType::U32), u0.clone());
        env.add_entry("U64", lit_ty(LiteralType::U64), u0.clone());
        env.add_entry("S8", lit_ty(LiteralType::S8), u0.clone());
        env.add_entry("S16", lit_ty(LiteralType::S16), u0.clone());
        env.add_entry("S32", lit_ty(LiteralType::S32), u0.clone());
        env.add_entry("S64", lit_ty(LiteralType::S64), u0.clone());
        env.add_entry("F32", lit_ty(LiteralType::F32), u0.clone());
        env.add_entry("F64", lit_ty(LiteralType::F64), u0.clone());

        env
    }
}
