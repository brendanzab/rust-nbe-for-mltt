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
use mltt_concrete::{Literal, LiteralKind};
use mltt_core::syntax::{core, domain, LiteralIntro, LiteralType};
use mltt_span::FileSpan;

pub fn check(
    concrete_literal: &Literal,
    expected_ty: &domain::RcType,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    use mltt_core::syntax::domain::Value;
    use mltt_core::syntax::LiteralType as LitType;

    let Literal { span, kind, value } = concrete_literal;

    let literal_intro = match (kind, expected_ty.as_ref()) {
        (LiteralKind::String, Value::LiteralType(LitType::String)) => parse_string(*span, value),
        (LiteralKind::Char, Value::LiteralType(LitType::Char)) => parse_char(*span, value),
        (LiteralKind::Int, Value::LiteralType(LitType::U8)) => parse_u8(*span, value),
        (LiteralKind::Int, Value::LiteralType(LitType::U16)) => parse_u16(*span, value),
        (LiteralKind::Int, Value::LiteralType(LitType::U32)) => parse_u32(*span, value),
        (LiteralKind::Int, Value::LiteralType(LitType::U64)) => parse_u64(*span, value),
        (LiteralKind::Int, Value::LiteralType(LitType::S8)) => parse_s8(*span, value),
        (LiteralKind::Int, Value::LiteralType(LitType::S16)) => parse_s16(*span, value),
        (LiteralKind::Int, Value::LiteralType(LitType::S32)) => parse_s32(*span, value),
        (LiteralKind::Int, Value::LiteralType(LitType::S64)) => parse_s64(*span, value),
        (LiteralKind::Int, Value::LiteralType(LitType::F32)) => parse_f32(*span, value),
        (LiteralKind::Int, Value::LiteralType(LitType::F64)) => parse_f64(*span, value),
        (LiteralKind::Float, Value::LiteralType(LitType::F32)) => parse_f32(*span, value),
        (LiteralKind::Float, Value::LiteralType(LitType::F64)) => parse_f64(*span, value),
        (_, _) => Err(Diagnostic::new_error("mismatched literal")
            .with_label(DiagnosticLabel::new_primary(*span))),
    }?;

    Ok(core::RcTerm::from(core::Term::LiteralIntro(literal_intro)))
}

pub fn synth(
    concrete_literal: &Literal,
) -> Result<(core::RcTerm, domain::RcType), Diagnostic<FileSpan>> {
    let Literal { span, kind, value } = concrete_literal;

    let (literal_intro, literal_ty) = match kind {
        LiteralKind::String => (parse_string(*span, value)?, LiteralType::String),
        LiteralKind::Char => (parse_char(*span, value)?, LiteralType::Char),
        LiteralKind::Int | LiteralKind::Float => {
            return Err(Diagnostic::new_error("ambiguous literal")
                .with_label(DiagnosticLabel::new_primary(*span)));
        },
    };

    Ok((
        core::RcTerm::from(core::Term::LiteralIntro(literal_intro)),
        domain::RcValue::from(domain::Value::LiteralType(literal_ty)),
    ))
}

// FIXME: convert panics into internal compiler errors

fn parse_string(_span: FileSpan, src: &str) -> Result<LiteralIntro, Diagnostic<FileSpan>> {
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

fn parse_char(_span: FileSpan, src: &str) -> Result<LiteralIntro, Diagnostic<FileSpan>> {
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
    ($span:expr, $T:ty, $Lit:ident, $src:ident) => {{
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
                .ok_or_else(|| {
                    Diagnostic::new_error("overflowing literal")
                        .with_label(DiagnosticLabel::new_primary($span))
                })
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

fn parse_u8(span: FileSpan, src: &str) -> Result<LiteralIntro, Diagnostic<FileSpan>> {
    parse_int!(span, u8, U8, src)
}

fn parse_u16(span: FileSpan, src: &str) -> Result<LiteralIntro, Diagnostic<FileSpan>> {
    parse_int!(span, u16, U16, src)
}

fn parse_u32(span: FileSpan, src: &str) -> Result<LiteralIntro, Diagnostic<FileSpan>> {
    parse_int!(span, u32, U32, src)
}

fn parse_u64(span: FileSpan, src: &str) -> Result<LiteralIntro, Diagnostic<FileSpan>> {
    parse_int!(span, u64, U64, src)
}

fn parse_s8(span: FileSpan, src: &str) -> Result<LiteralIntro, Diagnostic<FileSpan>> {
    parse_int!(span, i8, S8, src)
}

fn parse_s16(span: FileSpan, src: &str) -> Result<LiteralIntro, Diagnostic<FileSpan>> {
    parse_int!(span, i16, S16, src)
}

fn parse_s32(span: FileSpan, src: &str) -> Result<LiteralIntro, Diagnostic<FileSpan>> {
    parse_int!(span, i32, S32, src)
}

fn parse_s64(span: FileSpan, src: &str) -> Result<LiteralIntro, Diagnostic<FileSpan>> {
    parse_int!(span, i64, S64, src)
}

fn parse_f32(_span: FileSpan, src: &str) -> Result<LiteralIntro, Diagnostic<FileSpan>> {
    unimplemented!("f32 literals: {:?}", src)
}

fn parse_f64(_span: FileSpan, src: &str) -> Result<LiteralIntro, Diagnostic<FileSpan>> {
    unimplemented!("f64 literals: {:?}", src)
}
