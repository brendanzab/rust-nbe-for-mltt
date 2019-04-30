//! Elaboration of literals from unicode strings into their respective core
//! syntax representations.
//!
//! We need to defer the final parsing of literals until elaboration time
//! because it is only now that we know how large our target types are. This
//! saves us from having to use big integers or floats in our concrete syntax.
//!
//! Ultimately it would be pretty cool if you could register your own parse
//! functions that would be able to convert (at elaboration time) a UTF-8 string
//! into a data type of your choice, or return a custom error diagnostic.

use language_reporting::{Diagnostic, Label as DiagnosticLabel};
use mltt_concrete::{LiteralKind, SpannedString};
use mltt_core::literal::LiteralIntro;
use mltt_core::{domain, meta};
use mltt_span::FileSpan;
use std::rc::Rc;

use super::Context;

/// Check the type of a literal in a context.
pub fn check(
    context: &Context,
    metas: &meta::Env<domain::RcValue>,
    kind: LiteralKind,
    src: &SpannedString<'_>,
    expected_ty: &domain::RcType,
) -> Result<LiteralIntro, Diagnostic<FileSpan>> {
    use mltt_concrete::LiteralKind as LitKind;
    use mltt_core::domain::Value::LiteralType;
    use mltt_core::literal::{LiteralIntro as LitIntro, LiteralType as LitType};

    match (kind, expected_ty.as_ref()) {
        (LitKind::String, LiteralType(LitType::String)) => {
            parse_string(src).map(Rc::from).map(LitIntro::String)
        },
        (LitKind::Char, LiteralType(LitType::Char)) => parse_char(src).map(LitIntro::Char),
        (LitKind::Int, LiteralType(LitType::U8)) => parse_int::<u8>(src).map(LitIntro::U8),
        (LitKind::Int, LiteralType(LitType::U16)) => parse_int::<u16>(src).map(LitIntro::U16),
        (LitKind::Int, LiteralType(LitType::U32)) => parse_int::<u32>(src).map(LitIntro::U32),
        (LitKind::Int, LiteralType(LitType::U64)) => parse_int::<u64>(src).map(LitIntro::U64),
        (LitKind::Int, LiteralType(LitType::S8)) => parse_int::<i8>(src).map(LitIntro::S8),
        (LitKind::Int, LiteralType(LitType::S16)) => parse_int::<i16>(src).map(LitIntro::S16),
        (LitKind::Int, LiteralType(LitType::S32)) => parse_int::<i32>(src).map(LitIntro::S32),
        (LitKind::Int, LiteralType(LitType::S64)) => parse_int::<i64>(src).map(LitIntro::S64),
        (LitKind::Float, LiteralType(LitType::F32)) => parse_float::<f32>(src).map(LitIntro::F32),
        (LitKind::Float, LiteralType(LitType::F64)) => parse_float::<f64>(src).map(LitIntro::F64),
        (_, _) => Err(Diagnostic::new_error("mismatched literal").with_label(
            DiagnosticLabel::new_primary(src.span()).with_message(format!(
                "expected: {}",
                context.read_back_value(metas, None, expected_ty)?,
            )),
        )),
    }
}

/// Synthesize the type of a literal.
pub fn synth(
    kind: LiteralKind,
    src: &SpannedString<'_>,
) -> Result<(LiteralIntro, domain::RcType), Diagnostic<FileSpan>> {
    use mltt_concrete::LiteralKind as LitKind;
    use mltt_core::literal::{LiteralIntro as LitIntro, LiteralType as LitType};

    match kind {
        LitKind::String => Ok((
            LitIntro::String(Rc::from(parse_string(src)?)),
            domain::RcValue::literal_ty(LitType::String),
        )),
        LitKind::Char => Ok((
            LitIntro::Char(parse_char(src)?),
            domain::RcValue::literal_ty(LitType::Char),
        )),
        LitKind::Int | LitKind::Float => Err(Diagnostic::new_error("ambiguous literal")
            .with_label(DiagnosticLabel::new_primary(src.span()))),
    }
}

fn literal_bug<T>(span: FileSpan, message: impl Into<String>) -> Result<T, Diagnostic<FileSpan>> {
    // FIXME: improve precision of error span
    Err(Diagnostic::new_bug(message).with_label(DiagnosticLabel::new_primary(span)))
}

fn expect_char(
    span: FileSpan,
    chars: &mut impl Iterator<Item = char>,
) -> Result<char, Diagnostic<FileSpan>> {
    match chars.next() {
        Some(ch) => Ok(ch),
        None => literal_bug(span, "unexpected EOF"),
    }
}

pub fn parse_string(src: &SpannedString<'_>) -> Result<String, Diagnostic<FileSpan>> {
    let mut chars = src.slice.chars();
    let mut string = String::new();

    assert_eq!(chars.next(), Some('"'));

    loop {
        match expect_char(src.span(), &mut chars)? {
            '"' => break,
            '\\' => string.push(parse_escape(src.span(), &mut chars)?),
            ch => string.push(ch),
        }
    }

    assert_eq!(chars.next(), None);

    Ok(string)
}

pub fn parse_char(src: &SpannedString<'_>) -> Result<char, Diagnostic<FileSpan>> {
    let mut chars = src.slice.chars();

    assert_eq!(chars.next(), Some('\''));

    let ch = match expect_char(src.span(), &mut chars)? {
        '\'' => literal_bug(src.span(), "unexpected end of character"),
        '\\' => parse_escape(src.span(), &mut chars),
        ch => Ok(ch),
    }?;

    assert_eq!(chars.next(), Some('\''));
    assert_eq!(chars.next(), None);

    Ok(ch)
}

fn parse_escape(
    span: FileSpan,
    chars: &mut impl Iterator<Item = char>,
) -> Result<char, Diagnostic<FileSpan>> {
    match expect_char(span, chars)? {
        '\'' => Ok('\''),
        '\"' => Ok('\"'),
        '\\' => Ok('\\'),
        'n' => Ok('\n'),
        'r' => Ok('\r'),
        't' => Ok('\t'),
        '0' => Ok('\0'),
        'x' => {
            let mut code = 0;

            match expect_char(span, chars)? {
                ch @ '0'..='7' => code = code * 16 + (ch as u32 - '0' as u32),
                _ => literal_bug(span, "invalid ascii escape")?,
            };

            match expect_char(span, chars)? {
                ch @ '0'..='9' => code = code * 16 + (ch as u32 - '0' as u32),
                ch @ 'a'..='f' => code = code * 16 + (ch as u32 - 'a' as u32 + 10),
                ch @ 'A'..='F' => code = code * 16 + (ch as u32 - 'A' as u32 + 10),
                _ => literal_bug(span, "invalid ascii escape")?,
            };

            match std::char::from_u32(code) {
                Some(ch) => Ok(ch),
                None => literal_bug(span, "invalid ascii escape"),
            }
        },
        'u' => {
            let mut code = 0;

            assert_eq!(chars.next(), Some('{'));
            loop {
                match expect_char(span, chars)? {
                    ch @ '0'..='9' => code = code * 16 + (ch as u32 - '0' as u32),
                    ch @ 'a'..='f' => code = code * 16 + (ch as u32 - 'a' as u32 + 10),
                    ch @ 'A'..='F' => code = code * 16 + (ch as u32 - 'A' as u32 + 10),
                    '_' => continue,
                    '}' => break,
                    _ => literal_bug(span, "invalid unicode escape")?,
                }
            }

            match std::char::from_u32(code) {
                Some(ch) => Ok(ch),
                None => literal_bug(span, "invalid unicode escape"),
            }
        },
        _ => literal_bug(span, "unknown escape code"),
    }
}

/// Helper trait for defining `parse_int`.
pub trait ParseIntLiteral: Sized {
    fn from_u8(num: u8) -> Self;
    fn checked_neg(self) -> Option<Self>;
    fn checked_add(self, other: Self) -> Option<Self>;
    fn checked_mul(self, other: Self) -> Option<Self>;
}

macro_rules! impl_parse_int_literal {
    ($T:ident) => {
        impl ParseIntLiteral for $T {
            fn from_u8(num: u8) -> $T {
                num as $T
            }

            fn checked_neg(self) -> Option<$T> {
                $T::checked_neg(self)
            }

            fn checked_add(self, other: $T) -> Option<$T> {
                $T::checked_add(self, other)
            }

            fn checked_mul(self, other: $T) -> Option<$T> {
                $T::checked_mul(self, other)
            }
        }
    };
}

impl_parse_int_literal!(u8);
impl_parse_int_literal!(u16);
impl_parse_int_literal!(u32);
impl_parse_int_literal!(u64);
impl_parse_int_literal!(i8);
impl_parse_int_literal!(i16);
impl_parse_int_literal!(i32);
impl_parse_int_literal!(i64);

pub fn parse_int<T: ParseIntLiteral>(src: &SpannedString<'_>) -> Result<T, Diagnostic<FileSpan>> {
    let span = src.span();
    let mut chars = src.slice.chars();

    fn expect_base(
        span: FileSpan,
        is_neg: bool,
        chars: &mut impl Iterator<Item = char>,
    ) -> Result<(bool, u8, Option<char>), Diagnostic<FileSpan>> {
        match chars.next() {
            None => Ok((is_neg, 10, None)),
            Some('b') => Ok((is_neg, 2, None)),
            Some('o') => Ok((is_neg, 8, None)),
            Some('x') => Ok((is_neg, 16, None)),
            Some('_') => Ok((is_neg, 10, None)),
            Some(ch @ '0'..='9') => Ok((is_neg, 10, Some(ch))),
            Some(_) => literal_bug(span, "unexpected character")?,
        }
    }

    let (is_neg, base, mut first_digit) = match expect_char(span, &mut chars)? {
        '-' => match expect_char(span, &mut chars)? {
            '0' => expect_base(span, true, &mut chars)?,
            ch @ '0'..='9' => (true, 10, Some(ch)),
            _ => literal_bug(span, "unexpected character")?,
        },
        '0' => expect_base(span, false, &mut chars)?,
        ch @ '0'..='9' => (false, 10, Some(ch)),
        _ => literal_bug(span, "unexpected character")?,
    };

    let from_char = |ch: char, ch_diff: char, off: u8| {
        let number = T::from_u8(ch as u8 - ch_diff as u8 + off);

        if is_neg {
            number.checked_neg().ok_or_else(|| {
                Diagnostic::new_error("overflowing literal")
                    .with_label(DiagnosticLabel::new_primary(span))
            })
        } else {
            Ok(number)
        }
    };

    let acc = |prev: T, base: u8, inc: T| {
        if is_neg {
            prev.checked_mul(T::from_u8(base))
                .and_then(|prev| prev.checked_add(inc))
                .ok_or_else(|| {
                    Diagnostic::new_error("underflowing literal")
                        .with_label(DiagnosticLabel::new_primary(span))
                })
        } else {
            prev.checked_mul(T::from_u8(base))
                .and_then(|prev| prev.checked_add(inc))
                .ok_or_else(|| {
                    Diagnostic::new_error("overflowing literal")
                        .with_label(DiagnosticLabel::new_primary(span))
                })
        }
    };

    let mut number = T::from_u8(0);

    while let Some(ch) = first_digit.take().or_else(|| chars.next()) {
        number = match (base, ch) {
            (2, ch @ '0'..='1') => acc(number, base, from_char(ch, '0', 0)?)?,
            (8, ch @ '0'..='7') => acc(number, base, from_char(ch, '0', 0)?)?,
            (10, ch @ '0'..='9') => acc(number, base, from_char(ch, '0', 0)?)?,
            (16, ch @ '0'..='9') => acc(number, base, from_char(ch, '0', 0)?)?,
            (16, ch @ 'a'..='f') => acc(number, base, from_char(ch, 'a', 10)?)?,
            (16, ch @ 'A'..='F') => acc(number, base, from_char(ch, 'A', 10)?)?,
            (_, '_') => continue,
            (_, _) => literal_bug(span, "unexpected character")?,
        };
    }

    Ok(number)
}

/// Helper trait for defining `parse_float`.
pub trait ParseFloatLiteral: Sized {}

macro_rules! impl_parse_float_literal {
    ($T:ident) => {
        impl ParseFloatLiteral for $T {}
    };
}

impl_parse_float_literal!(f32);
impl_parse_float_literal!(f64);

pub fn parse_float<T: ParseFloatLiteral>(
    src: &SpannedString<'_>,
) -> Result<T, Diagnostic<FileSpan>> {
    literal_bug(
        src.span(),
        "literal elaboration not yet implemented for floats",
    )
}
