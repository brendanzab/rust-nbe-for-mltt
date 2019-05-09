//! Core literals.

use std::fmt;
use std::rc::Rc;

/// Literal types.
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
}

impl fmt::Display for LiteralType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LiteralType::String => write!(f, "String"),
            LiteralType::Char => write!(f, "Char"),
            LiteralType::Bool => write!(f, "Bool"),
            LiteralType::U8 => write!(f, "U8"),
            LiteralType::U16 => write!(f, "U16"),
            LiteralType::U32 => write!(f, "U32"),
            LiteralType::U64 => write!(f, "U64"),
            LiteralType::S8 => write!(f, "S8"),
            LiteralType::S16 => write!(f, "S16"),
            LiteralType::S32 => write!(f, "S32"),
            LiteralType::S64 => write!(f, "S64"),
            LiteralType::F32 => write!(f, "F32"),
            LiteralType::F64 => write!(f, "F64"),
        }
    }
}

/// Literal introductions.
#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum LiteralIntro {
    String(Rc<str>),
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
}

impl fmt::Display for LiteralIntro {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LiteralIntro::String(value) => write!(f, "{:?}", value),
            LiteralIntro::Char(value) => write!(f, "{:?}", value),
            LiteralIntro::Bool(true) => write!(f, "true"),
            LiteralIntro::Bool(false) => write!(f, "false"),
            LiteralIntro::U8(value) => write!(f, "{}", value),
            LiteralIntro::U16(value) => write!(f, "{}", value),
            LiteralIntro::U32(value) => write!(f, "{}", value),
            LiteralIntro::U64(value) => write!(f, "{}", value),
            LiteralIntro::S8(value) => write!(f, "{}", value),
            LiteralIntro::S16(value) => write!(f, "{}", value),
            LiteralIntro::S32(value) => write!(f, "{}", value),
            LiteralIntro::S64(value) => write!(f, "{}", value),
            LiteralIntro::F32(value) => write!(f, "{}", value),
            LiteralIntro::F64(value) => write!(f, "{}", value),
        }
    }
}

macro_rules! impl_from_to_literal_intro {
    ($T:ty, $Literal:ident) => {
        impl From<$T> for LiteralIntro {
            fn from(src: $T) -> LiteralIntro {
                LiteralIntro::$Literal(src)
            }
        }
    };
}

impl_from_to_literal_intro!(Rc<str>, String);
impl_from_to_literal_intro!(char, Char);
impl_from_to_literal_intro!(bool, Bool);
impl_from_to_literal_intro!(u8, U8);
impl_from_to_literal_intro!(u16, U16);
impl_from_to_literal_intro!(u32, U32);
impl_from_to_literal_intro!(u64, U64);
impl_from_to_literal_intro!(i8, S8);
impl_from_to_literal_intro!(i16, S16);
impl_from_to_literal_intro!(i32, S32);
impl_from_to_literal_intro!(i64, S64);
impl_from_to_literal_intro!(f32, F32);
impl_from_to_literal_intro!(f64, F64);

impl<'a> From<&'a str> for LiteralIntro {
    fn from(src: &'a str) -> LiteralIntro {
        LiteralIntro::String(Rc::from(src))
    }
}

impl From<String> for LiteralIntro {
    fn from(src: String) -> LiteralIntro {
        LiteralIntro::String(Rc::from(src))
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
