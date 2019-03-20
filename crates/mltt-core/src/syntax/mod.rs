//! The various syntaxes of the language.
//!
//! The core, domain, and normal syntaxes are mainly based off Mini-TT

use pretty::{BoxDoc, Doc};
use std::fmt;
use std::ops;
use std::rc::Rc;

pub mod core;
pub mod domain;

/// Reference counted documentation string
pub type DocString = Rc<str>;

/// De Bruijn level
///
/// This counts the total number of binders that we encounter when running down
/// the syntax tree from the root.
///
/// De Bruijn levels are useful because unlike de Bruijn indices, they don't
/// need to be shifted while moving around terms under a specific scope. This
/// makes them ideal for representing values. We'll convert these back into
/// indices during read-back.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct VarLevel(pub u32);

impl From<u32> for VarLevel {
    fn from(src: u32) -> VarLevel {
        VarLevel(src)
    }
}

impl ops::AddAssign<u32> for VarLevel {
    fn add_assign(&mut self, other: u32) {
        self.0 += other;
    }
}

impl ops::Add<u32> for VarLevel {
    type Output = VarLevel;

    fn add(mut self, other: u32) -> VarLevel {
        self += other;
        self
    }
}

/// De Bruijn index
///
/// This counts the number of binders we encounter when running up the syntax
/// tree to get to the binder that bound this variable. De Bruijn indices are
/// useful for being able to quickly looking up entries in an `Env` when deep in
/// a nested scope. They also provide easy access to alpha equality.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct VarIndex(pub u32);

impl VarIndex {
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::as_string(format!("@{}", self.0))
    }
}

impl From<u32> for VarIndex {
    fn from(src: u32) -> VarIndex {
        VarIndex(src)
    }
}

impl ops::AddAssign<u32> for VarIndex {
    fn add_assign(&mut self, other: u32) {
        self.0 += other;
    }
}

impl ops::Add<u32> for VarIndex {
    type Output = VarIndex;

    fn add(mut self, other: u32) -> VarIndex {
        self += other;
        self
    }
}

/// An environment of entries that can be looked up based on a debruijn index.
///
/// It is backed by an `im::Vector` to allow for efficient sharing between
/// multiple closures.
#[derive(Debug, Clone, PartialEq)]
pub struct Env<Entry: Clone> {
    /// The entries in the environment
    entries: im::Vector<Entry>,
}

impl<Entry: Clone> Env<Entry> {
    /// Create a new, empty environment.
    pub fn new() -> Env<Entry> {
        Env {
            entries: im::Vector::new(),
        }
    }

    /// Lookup an entry in the environment.
    pub fn lookup_entry(&self, index: VarIndex) -> Option<&Entry> {
        self.entries.get(index.0 as usize)
    }

    /// Add a new entry to the environment.
    pub fn add_entry(&mut self, entry: Entry) {
        self.entries.push_front(entry)
    }
}

/// The level of a universe
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct UniverseLevel(pub u32);

impl UniverseLevel {
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::as_string(&self.0)
    }
}

impl From<u32> for UniverseLevel {
    fn from(src: u32) -> UniverseLevel {
        UniverseLevel(src)
    }
}

impl ops::AddAssign<u32> for UniverseLevel {
    fn add_assign(&mut self, other: u32) {
        self.0 += other;
    }
}

impl ops::Add<u32> for UniverseLevel {
    type Output = UniverseLevel;

    fn add(mut self, other: u32) -> UniverseLevel {
        self += other;
        self
    }
}

/// Literal types
#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum LiteralType {
    String,
    Char,
    Bool,
    U8,
    U16,
    U32,
    U64,
    S8,
    S16,
    S32,
    S64,
    F32,
    F64,
}

impl LiteralType {
    pub fn alpha_eq(&self, other: &LiteralType) -> bool {
        self == other
    }

    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            LiteralType::String => Doc::text("String"),
            LiteralType::Char => Doc::text("Char"),
            LiteralType::Bool => Doc::text("Bool"),
            LiteralType::U8 => Doc::text("U8"),
            LiteralType::U16 => Doc::text("U16"),
            LiteralType::U32 => Doc::text("U32"),
            LiteralType::U64 => Doc::text("U64"),
            LiteralType::S8 => Doc::text("S8"),
            LiteralType::S16 => Doc::text("S16"),
            LiteralType::S32 => Doc::text("S32"),
            LiteralType::S64 => Doc::text("S64"),
            LiteralType::F32 => Doc::text("F32"),
            LiteralType::F64 => Doc::text("F64"),
        }
    }
}

/// Literal introductions
#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum LiteralIntro {
    String(String),
    Char(char),
    Bool(bool),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    S8(i8),
    S16(i16),
    S32(i32),
    S64(i64),
    F32(f32),
    F64(f64),
}

impl LiteralIntro {
    pub fn alpha_eq(&self, other: &LiteralIntro) -> bool {
        match (self, other) {
            (LiteralIntro::String(v1), LiteralIntro::String(v2)) => v1 == v2,
            (LiteralIntro::Char(v1), LiteralIntro::Char(v2)) => v1 == v2,
            (LiteralIntro::Bool(v1), LiteralIntro::Bool(v2)) => v1 == v2,
            (LiteralIntro::U8(v1), LiteralIntro::U8(v2)) => v1 == v2,
            (LiteralIntro::U16(v1), LiteralIntro::U16(v2)) => v1 == v2,
            (LiteralIntro::U32(v1), LiteralIntro::U32(v2)) => v1 == v2,
            (LiteralIntro::U64(v1), LiteralIntro::U64(v2)) => v1 == v2,
            (LiteralIntro::S8(v1), LiteralIntro::S8(v2)) => v1 == v2,
            (LiteralIntro::S16(v1), LiteralIntro::S16(v2)) => v1 == v2,
            (LiteralIntro::S32(v1), LiteralIntro::S32(v2)) => v1 == v2,
            (LiteralIntro::S64(v1), LiteralIntro::S64(v2)) => v1 == v2,
            // Use bitwise equality, combined with a NaN check to provide a
            // logically consistent equality comparison of floating point
            // numbers. This means that the following weirdness (from an
            // IEEE-754 perspective) happens at the type level:
            //
            // - 0.0 != -0.0
            // - NaN == NaN
            // - NaN == -NaN
            //
            // # References
            //
            // - https://github.com/idris-lang/Idris-dev/issues/2609
            // - https://github.com/dhall-lang/dhall-lang/issues/425
            // - https://github.com/agda/agda/issues/2169
            // - https://agda.readthedocs.io/en/v2.5.4.2/language/built-ins.html#floats
            (LiteralIntro::F32(v1), LiteralIntro::F32(v2)) => {
                v1.to_bits() == v2.to_bits() || v1.is_nan() && v2.is_nan()
            },
            (LiteralIntro::F64(v1), LiteralIntro::F64(v2)) => {
                v1.to_bits() == v2.to_bits() || v1.is_nan() && v2.is_nan()
            },
            (_, _) => false,
        }
    }

    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            LiteralIntro::String(value) => Doc::text(format!("{:?}", value)),
            LiteralIntro::Char(value) => Doc::text(format!("{:?}", value)),
            LiteralIntro::Bool(true) => Doc::text("true"),
            LiteralIntro::Bool(false) => Doc::text("false"),
            LiteralIntro::U8(value) => Doc::as_string(&value),
            LiteralIntro::U16(value) => Doc::as_string(&value),
            LiteralIntro::U32(value) => Doc::as_string(&value),
            LiteralIntro::U64(value) => Doc::as_string(&value),
            LiteralIntro::S8(value) => Doc::as_string(&value),
            LiteralIntro::S16(value) => Doc::as_string(&value),
            LiteralIntro::S32(value) => Doc::as_string(&value),
            LiteralIntro::S64(value) => Doc::as_string(&value),
            LiteralIntro::F32(value) => Doc::as_string(&value),
            LiteralIntro::F64(value) => Doc::as_string(&value),
        }
    }
}

/// A label
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Label(pub String);

impl Label {
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::text(&self.0)
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// The application mode of a function
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AppMode {
    /// Explicit application mode
    Explicit,
    /// Implicit application mode
    Implicit(Label),
    /// Instance application mode
    Instance(Label),
}

impl fmt::Display for AppMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AppMode::Explicit => write!(f, "_"),
            AppMode::Implicit(label) => write!(f, "{{{}}}", label),
            AppMode::Instance(label) => write!(f, "{{{{{}}}}}", label),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{f32, f64};

    use super::*;

    use self::LiteralIntro::{F32, F64};

    #[test]
    fn alpha_eq_f32_nan_nan() {
        assert!(LiteralIntro::alpha_eq(&F32(f32::NAN), &F32(f32::NAN)));
    }

    #[test]
    fn alpha_eq_f32_neg_nan_nan() {
        assert!(LiteralIntro::alpha_eq(&F32(-f32::NAN), &F32(f32::NAN)));
    }

    #[test]
    fn alpha_eq_f32_nan_neg_nan() {
        assert!(LiteralIntro::alpha_eq(&F32(f32::NAN), &F32(-f32::NAN)));
    }

    #[test]
    fn alpha_eq_f32_neg_nan_neg_nan() {
        assert!(LiteralIntro::alpha_eq(&F32(-f32::NAN), &F32(-f32::NAN)));
    }

    #[test]
    fn alpha_eq_f32_zero_zero() {
        assert!(LiteralIntro::alpha_eq(&F32(0.0), &F32(0.0)));
    }

    #[test]
    fn alpha_eq_f32_neg_zero_zero() {
        assert!(!LiteralIntro::alpha_eq(&F32(-0.0), &F32(0.0)));
    }

    #[test]
    fn alpha_eq_f32_zero_neg_zero() {
        assert!(!LiteralIntro::alpha_eq(&F32(0.0), &F32(-0.0)));
    }

    #[test]
    fn alpha_eq_f32_neg_zero_neg_zero() {
        assert!(LiteralIntro::alpha_eq(&F32(-0.0), &F32(-0.0)));
    }

    #[test]
    fn alpha_eq_f64_nan_nan() {
        assert!(LiteralIntro::alpha_eq(&F64(f64::NAN), &F64(f64::NAN)));
    }

    #[test]
    fn alpha_eq_f64_neg_nan_nan() {
        assert!(LiteralIntro::alpha_eq(&F64(-f64::NAN), &F64(f64::NAN)));
    }

    #[test]
    fn alpha_eq_f64_nan_neg_nan() {
        assert!(LiteralIntro::alpha_eq(&F64(f64::NAN), &F64(-f64::NAN)));
    }

    #[test]
    fn alpha_eq_f64_neg_nan_neg_nan() {
        assert!(LiteralIntro::alpha_eq(&F64(-f64::NAN), &F64(-f64::NAN)));
    }

    #[test]
    fn alpha_eq_f64_zero_zero() {
        assert!(LiteralIntro::alpha_eq(&F64(0.0), &F64(0.0)));
    }

    #[test]
    fn alpha_eq_f64_neg_zero_zero() {
        assert!(!LiteralIntro::alpha_eq(&F64(-0.0), &F64(0.0)));
    }

    #[test]
    fn alpha_eq_f64_zero_neg_zero() {
        assert!(!LiteralIntro::alpha_eq(&F64(0.0), &F64(-0.0)));
    }

    #[test]
    fn alpha_eq_f64_neg_zero_neg_zero() {
        assert!(LiteralIntro::alpha_eq(&F64(-0.0), &F64(-0.0)));
    }
}
