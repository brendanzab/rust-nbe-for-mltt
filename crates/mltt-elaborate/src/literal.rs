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

use mltt_concrete::{Literal, LiteralKind};
use mltt_core::syntax::{core, domain, LiteralIntro, LiteralType};

use crate::TypeError;

pub fn check(
    concrete_literal: &Literal,
    expected_ty: &domain::RcType,
) -> Result<core::RcTerm, TypeError> {
    use mltt_core::syntax::domain::Value;

    let Literal { kind, value } = concrete_literal;

    let literal_intro = match (kind, expected_ty.as_ref()) {
        (LiteralKind::String, Value::LiteralType(LiteralType::String)) => parse_string(value),
        (LiteralKind::Char, Value::LiteralType(LiteralType::Char)) => parse_char(value),
        (LiteralKind::Int, Value::LiteralType(LiteralType::U8)) => parse_u8(value),
        (LiteralKind::Int, Value::LiteralType(LiteralType::U16)) => parse_u16(value),
        (LiteralKind::Int, Value::LiteralType(LiteralType::U32)) => parse_u32(value),
        (LiteralKind::Int, Value::LiteralType(LiteralType::U64)) => parse_u64(value),
        (LiteralKind::Int, Value::LiteralType(LiteralType::S8)) => parse_s8(value),
        (LiteralKind::Int, Value::LiteralType(LiteralType::S16)) => parse_s16(value),
        (LiteralKind::Int, Value::LiteralType(LiteralType::S32)) => parse_s32(value),
        (LiteralKind::Int, Value::LiteralType(LiteralType::S64)) => parse_s64(value),
        (LiteralKind::Int, Value::LiteralType(LiteralType::F32)) => parse_f32(value),
        (LiteralKind::Int, Value::LiteralType(LiteralType::F64)) => parse_f64(value),
        (LiteralKind::Float, Value::LiteralType(LiteralType::F32)) => parse_f32(value),
        (LiteralKind::Float, Value::LiteralType(LiteralType::F64)) => parse_f64(value),
        (_, _) => Err(TypeError::MismatchedLiteral(*kind, expected_ty.clone())),
    }?;

    Ok(core::RcTerm::from(core::Term::LiteralIntro(literal_intro)))
}

pub fn synth(concrete_literal: &Literal) -> Result<(core::RcTerm, domain::RcType), TypeError> {
    let Literal { kind, value } = concrete_literal;

    let (literal_intro, literal_ty) = match kind {
        LiteralKind::String => (parse_string(value)?, LiteralType::String),
        LiteralKind::Char => (parse_char(value)?, LiteralType::Char),
        LiteralKind::Int => return Err(TypeError::AmbiguousLiteral(LiteralKind::Int)),
        LiteralKind::Float => return Err(TypeError::AmbiguousLiteral(LiteralKind::Float)),
    };

    Ok((
        core::RcTerm::from(core::Term::LiteralIntro(literal_intro)),
        domain::RcValue::from(domain::Value::LiteralType(literal_ty)),
    ))
}

// FIXME: convert panics into internal compiler errors

fn parse_string(src: &str) -> Result<LiteralIntro, TypeError> {
    let mut chars = src.chars();
    let mut string = String::new();

    assert_eq!(chars.next(), Some('"'));

    loop {
        match chars.next().expect("unexpected EOF") {
            '"' => break,
            '\\' => string.push(parse_escape(&mut chars)),
            ch => string.push(ch),
        }
    }

    assert_eq!(chars.next(), None);

    Ok(LiteralIntro::String(string))
}

fn parse_char(src: &str) -> Result<LiteralIntro, TypeError> {
    let mut chars = src.chars();

    assert_eq!(chars.next(), Some('\''));

    let ch = match chars.next().expect("unexpected EOF") {
        '\'' => panic!("unexpected end of character"),
        '\\' => parse_escape(&mut chars),
        ch => ch,
    };

    assert_eq!(chars.next(), Some('\''));
    assert_eq!(chars.next(), None);

    Ok(LiteralIntro::Char(ch))
}

fn parse_escape(chars: &mut std::str::Chars<'_>) -> char {
    match chars.next().expect("unexpected EOF") {
        '\'' => '\'',
        '\"' => '\"',
        '\\' => '\\',
        'n' => '\n',
        'r' => '\r',
        't' => '\t',
        '0' => '\0',
        'x' => {
            let mut code = 0;

            match chars.next().expect("unexpected EOF") {
                ch @ '0'..='7' => code = code * 16 + (ch as u32 - '0' as u32),
                _ => panic!("invalid ascii escape"),
            };

            match chars.next().expect("unexpected EOF") {
                ch @ '0'..='9' => code = code * 16 + (ch as u32 - '0' as u32),
                ch @ 'a'..='f' => code = code * 16 + (ch as u32 - 'a' as u32 + 10),
                ch @ 'A'..='F' => code = code * 16 + (ch as u32 - 'A' as u32 + 10),
                _ => panic!("invalid ascii escape"),
            };

            std::char::from_u32(code).expect("invalid ascii escape")
        },
        'u' => {
            let mut code = 0;

            assert_eq!(chars.next(), Some('{'));
            loop {
                match chars.next().expect("unexpected EOF") {
                    ch @ '0'..='9' => code = code * 16 + (ch as u32 - '0' as u32),
                    ch @ 'a'..='f' => code = code * 16 + (ch as u32 - 'a' as u32 + 10),
                    ch @ 'A'..='F' => code = code * 16 + (ch as u32 - 'A' as u32 + 10),
                    '_' => continue,
                    '}' => break,
                    _ => panic!("invalid unicode escape"),
                }
            }

            std::char::from_u32(code).expect("invalid unicode escape")
        },
        _ => panic!("unknown escape code"),
    }
}

// FIXME: convert to a polymorphic function?
macro_rules! parse_int {
    ($T:ty, $Lit:ident, $src:ident) => {{
        let mut chars = $src.chars();

        let (base, mut number) = match chars.next().expect("unexpected EOF") {
            '0' => match chars.next() {
                None => (10, 0),
                Some('b') => (2, 0),
                Some('o') => (8, 0),
                Some('x') => (16, 0),
                Some('_') => (10, 0),
                Some(ch @ '0'..='9') => (10, ch as $T - '0' as $T),
                Some(_) => panic!("unexpected character"),
            },
            ch @ '0'..='9' => (10, ch as $T - '0' as $T),
            _ => panic!("unexpected character"),
        };

        let acc = |prev: $T, base: $T, inc: $T| {
            prev.checked_mul(base)
                .and_then(|prev| prev.checked_add(inc))
                .ok_or_else(|| TypeError::OverflowingLiteral($src.to_owned()))
        };

        while let Some(ch) = chars.next() {
            match (base, ch) {
                (2, ch @ '0'..='1') => number = acc(number, base, ch as $T - '0' as $T)?,
                (8, ch @ '0'..='7') => number = acc(number, base, ch as $T - '0' as $T)?,
                (10, ch @ '0'..='9') => number = acc(number, base, ch as $T - '0' as $T)?,
                (16, ch @ '0'..='9') => number = acc(number, base, ch as $T - '0' as $T)?,
                (16, ch @ 'a'..='f') => number = acc(number, base, ch as $T - 'a' as $T + 10)?,
                (16, ch @ 'A'..='F') => number = acc(number, base, ch as $T - 'A' as $T + 10)?,
                (_, '_') => continue,
                (_, _) => panic!("unexpected character"),
            }
        }

        Ok(LiteralIntro::$Lit(number))
    }};
}

fn parse_u8(src: &str) -> Result<LiteralIntro, TypeError> {
    parse_int!(u8, U8, src)
}

fn parse_u16(src: &str) -> Result<LiteralIntro, TypeError> {
    parse_int!(u16, U16, src)
}

fn parse_u32(src: &str) -> Result<LiteralIntro, TypeError> {
    parse_int!(u32, U32, src)
}

fn parse_u64(src: &str) -> Result<LiteralIntro, TypeError> {
    parse_int!(u64, U64, src)
}

fn parse_s8(src: &str) -> Result<LiteralIntro, TypeError> {
    parse_int!(i8, S8, src)
}

fn parse_s16(src: &str) -> Result<LiteralIntro, TypeError> {
    parse_int!(i16, S16, src)
}

fn parse_s32(src: &str) -> Result<LiteralIntro, TypeError> {
    parse_int!(i32, S32, src)
}

fn parse_s64(src: &str) -> Result<LiteralIntro, TypeError> {
    parse_int!(i64, S64, src)
}

fn parse_f32(src: &str) -> Result<LiteralIntro, TypeError> {
    unimplemented!("f32 literals: {:?}", src)
}

fn parse_f64(src: &str) -> Result<LiteralIntro, TypeError> {
    unimplemented!("f64 literals: {:?}", src)
}
