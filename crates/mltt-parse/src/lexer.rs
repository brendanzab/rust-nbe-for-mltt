use language_reporting::{Diagnostic, Label};
use mltt_span::{ByteIndex, ByteSize, File, FileSpan};
use std::fmt;
use std::str::{CharIndices, FromStr};

fn is_symbol(ch: char) -> bool {
    match ch {
        '&' | '!' | ':' | ',' | '.' | '=' | '/' | '>' | '<' | '-' | '|' | '+' | ';' | '*' | '^'
        | '?' => true,
        _ => false,
    }
}

fn is_name_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_' || ch == '-'
}

fn is_name_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_' || ch == '-'
}

fn is_bin_digit(ch: char) -> bool {
    ch.is_digit(2)
}

fn is_oct_digit(ch: char) -> bool {
    ch.is_digit(8)
}

fn is_dec_digit(ch: char) -> bool {
    ch.is_digit(10)
}

fn is_hex_digit(ch: char) -> bool {
    ch.is_digit(16)
}

pub type SpannedToken<'file> = (ByteIndex, Token<&'file str>, ByteIndex);

/// A token in the source file, to be emitted by the `Lexer`
#[derive(Clone, Debug, PartialEq)]
pub enum Token<S> {
    // Data
    Name(S),
    LineComment(S),
    LineDoc(S),
    StringLiteral(String),
    CharLiteral(char),
    BinIntLiteral(u64),
    OctIntLiteral(u64),
    DecIntLiteral(u64),
    HexIntLiteral(u64),
    DecFloatLiteral(f64),

    // Keywords
    As,         // as
    Case,       // case
    Else,       // else
    If,         // if
    Import,     // import
    In,         // in
    Let,        // let
    Record,     // record
    RecordType, // Record
    Then,       // then
    Type,       // Type
    Where,      // where

    // Symbols
    BSlash,    // \
    Caret,     // ^
    Colon,     // :
    Comma,     // ,
    Dot,       // .
    DotDot,    // ..
    Equal,     // =
    LArrow,    // ->
    LFatArrow, // =>
    Question,  // ?
    Semi,      // ;

    // Delimiters
    LParen,   // (
    RParen,   // )
    LBrace,   // {
    RBrace,   // }
    LBracket, // [
    RBracket, // ]
}

impl<S: fmt::Display> fmt::Display for Token<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Token::Name(ref name) => write!(f, "{}", name),
            Token::LineComment(ref value) => write!(f, "-- {}", value),
            Token::LineDoc(ref value) => write!(f, "||| {}", value),
            Token::StringLiteral(ref value) => write!(f, "{:?}", value),
            Token::CharLiteral(ref value) => write!(f, "'{:?}'", value),
            Token::BinIntLiteral(ref value) => write!(f, "{:b}", value),
            Token::OctIntLiteral(ref value) => write!(f, "{:o}", value),
            Token::DecIntLiteral(ref value) => write!(f, "{}", value),
            Token::HexIntLiteral(ref value) => write!(f, "{:x}", value),
            Token::DecFloatLiteral(ref value) => write!(f, "{}", value),
            Token::As => write!(f, "as"),
            Token::Case => write!(f, "case"),
            Token::Else => write!(f, "else"),
            Token::If => write!(f, "if"),
            Token::Import => write!(f, "import"),
            Token::In => write!(f, "in"),
            Token::Let => write!(f, "let"),
            Token::Record => write!(f, "record"),
            Token::RecordType => write!(f, "Record"),
            Token::Then => write!(f, "then"),
            Token::Type => write!(f, "Type"),
            Token::Where => write!(f, "where"),
            Token::BSlash => write!(f, "\\"),
            Token::Caret => write!(f, "^"),
            Token::Colon => write!(f, ":"),
            Token::Comma => write!(f, ","),
            Token::Dot => write!(f, "."),
            Token::DotDot => write!(f, ".."),
            Token::Equal => write!(f, "="),
            Token::LFatArrow => write!(f, "=>"),
            Token::LArrow => write!(f, "->"),
            Token::Question => write!(f, "?"),
            Token::Semi => write!(f, ";"),
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::LBrace => write!(f, "{{"),
            Token::RBrace => write!(f, "}}"),
            Token::LBracket => write!(f, "["),
            Token::RBracket => write!(f, "]"),
        }
    }
}

impl<'file> From<Token<&'file str>> for Token<String> {
    fn from(src: Token<&'file str>) -> Token<String> {
        match src {
            Token::Name(name) => Token::Name(name.to_owned()),
            Token::LineComment(value) => Token::LineComment(value.to_owned()),
            Token::LineDoc(value) => Token::LineDoc(value.to_owned()),
            Token::StringLiteral(value) => Token::StringLiteral(value),
            Token::CharLiteral(value) => Token::CharLiteral(value),
            Token::BinIntLiteral(value) => Token::BinIntLiteral(value),
            Token::OctIntLiteral(value) => Token::OctIntLiteral(value),
            Token::DecIntLiteral(value) => Token::DecIntLiteral(value),
            Token::HexIntLiteral(value) => Token::HexIntLiteral(value),
            Token::DecFloatLiteral(value) => Token::DecFloatLiteral(value),
            Token::As => Token::As,
            Token::Case => Token::Case,
            Token::Else => Token::Else,
            Token::If => Token::If,
            Token::Import => Token::Import,
            Token::In => Token::In,
            Token::Let => Token::Let,
            Token::Record => Token::Record,
            Token::RecordType => Token::RecordType,
            Token::Then => Token::Then,
            Token::Type => Token::Type,
            Token::Where => Token::Where,
            Token::BSlash => Token::BSlash,
            Token::Caret => Token::Caret,
            Token::Colon => Token::Colon,
            Token::Comma => Token::Comma,
            Token::Dot => Token::Dot,
            Token::DotDot => Token::DotDot,
            Token::Equal => Token::Equal,
            Token::LFatArrow => Token::LFatArrow,
            Token::LArrow => Token::LArrow,
            Token::Question => Token::Question,
            Token::Semi => Token::Semi,
            Token::LParen => Token::LParen,
            Token::RParen => Token::RParen,
            Token::LBrace => Token::LBrace,
            Token::RBrace => Token::RBrace,
            Token::LBracket => Token::LBracket,
            Token::RBracket => Token::RBracket,
        }
    }
}

/// An iterator over a source string that yields `Token`s for subsequent use by
/// the parser
pub struct Lexer<'file> {
    file: &'file File,
    chars: CharIndices<'file>,
    lookahead: Option<(usize, char)>,
}

impl<'file> Iterator for Lexer<'file> {
    type Item = Result<SpannedToken<'file>, Diagnostic<FileSpan>>;

    fn next(&mut self) -> Option<Result<SpannedToken<'file>, Diagnostic<FileSpan>>> {
        while let Some((start, ch)) = self.bump() {
            let end = start + ByteSize::from_char_len_utf8(ch);

            return Some(match ch {
                ch if is_symbol(ch) => self.continue_symbol(start),
                '\\' => Ok((start, Token::BSlash, end)),
                '(' => Ok((start, Token::LParen, end)),
                ')' => Ok((start, Token::RParen, end)),
                '{' => Ok((start, Token::LBrace, end)),
                '}' => Ok((start, Token::RBrace, end)),
                '[' => Ok((start, Token::LBracket, end)),
                ']' => Ok((start, Token::RBracket, end)),
                '"' => self.continue_string_literal(start),
                '\'' => self.continue_char_literal(start),
                '0' => self.continue_zero_number(start),
                ch if is_dec_digit(ch) => self.continue_dec_literal(start),
                ch if is_name_start(ch) => Ok(self.continue_name(start)),
                ch if ch.is_whitespace() => continue,
                _ => Err({
                    let end = start + ByteSize::from_char_len_utf8(ch);
                    Diagnostic::new_error(format!("unexpected character `{}`", ch))
                        .with_label(Label::new_primary(self.span(start, end)))
                }),
            });
        }

        None
    }
}

impl<'file> Lexer<'file> {
    /// Create a new lexer from the source string
    pub fn new(file: &'file File) -> Self {
        let mut chars = file.contents().char_indices();

        Lexer {
            file,
            lookahead: chars.next(),
            chars,
        }
    }

    /// Returns a span in the source file
    fn span(&self, start: ByteIndex, end: ByteIndex) -> FileSpan {
        FileSpan::new(self.file.id(), start, end)
    }

    /// Returns the index of the end of the file
    fn eof(&self) -> ByteIndex {
        self.file.span().end()
    }

    fn error_integer_literal_overflow(
        &self,
        start: ByteIndex,
        end: ByteIndex,
        value: &str,
    ) -> Diagnostic<FileSpan> {
        Diagnostic::new_error(format!("integer literal overflow with value `{}`", value))
            .with_label(
                Label::new_primary(self.span(start, end)).with_message("overflowing literal"),
            )
    }

    /// Return the next character in the source string
    fn lookahead(&self) -> Option<(ByteIndex, char)> {
        self.lookahead.map(|(i, ch)| (ByteIndex::from(i), ch))
    }

    /// Bump the current position in the source string by one character,
    /// returning the current character and byte position.
    fn bump(&mut self) -> Option<(ByteIndex, char)> {
        let current = self.lookahead();
        self.lookahead = self.chars.next();
        current
    }

    /// Bump the current position in the source string by one character,
    /// returning the current character and byte position, or returning an
    /// unexpected end of file error.
    fn expect_bump(&mut self) -> Result<(ByteIndex, char), Diagnostic<FileSpan>> {
        self.bump().ok_or_else(|| {
            let eof = self.eof();
            Diagnostic::new_error("unexpected end of file")
                .with_label(Label::new_primary(self.span(eof, eof)))
        })
    }

    /// Return a slice of the source string
    fn slice(&self, start: ByteIndex, end: ByteIndex) -> &'file str {
        &self.file.contents()[start.to_usize()..end.to_usize()]
    }

    /// Consume characters while the predicate matches for the current
    /// character, then return the consumed slice and the end byte
    /// position.
    fn take_while<F>(&mut self, start: ByteIndex, mut keep_going: F) -> (ByteIndex, &'file str)
    where
        F: FnMut(char) -> bool,
    {
        self.take_until(start, |ch| !keep_going(ch))
    }

    /// Consume characters until the predicate matches for the next character
    /// in the lookahead, then return the consumed slice and the end byte
    /// position.
    fn take_until<F>(&mut self, start: ByteIndex, mut terminate: F) -> (ByteIndex, &'file str)
    where
        F: FnMut(char) -> bool,
    {
        while let Some((end, ch)) = self.lookahead() {
            if terminate(ch) {
                return (end, self.slice(start, end));
            } else {
                self.bump();
            }
        }

        let eof = self.eof();
        (eof, self.slice(start, eof))
    }

    /// Consume a line comment
    fn continue_line_comment(&mut self, start: ByteIndex) -> SpannedToken<'file> {
        let (end, mut comment) =
            self.take_until(start + ByteSize::from_str_len_utf8("--"), |ch| ch == '\n');

        // Skip preceding space
        if comment.starts_with(' ') {
            comment = &comment[1..];
        }

        (start, Token::LineComment(comment), end)
    }

    /// Consume a doc comment
    fn continue_line_doc(&mut self, start: ByteIndex) -> SpannedToken<'file> {
        let (end, mut comment) =
            self.take_until(start + ByteSize::from_str_len_utf8("|||"), |ch| ch == '\n');

        // Skip preceding space
        if comment.starts_with(' ') {
            comment = &comment[1..];
        }

        (start, Token::LineDoc(comment), end)
    }

    /// Consume a symbol
    fn continue_symbol(
        &mut self,
        start: ByteIndex,
    ) -> Result<SpannedToken<'file>, Diagnostic<FileSpan>> {
        let (end, symbol) = self.take_while(start, is_symbol);

        match symbol {
            ":" => Ok((start, Token::Colon, end)),
            "^" => Ok((start, Token::Caret, end)),
            "," => Ok((start, Token::Comma, end)),
            "." => Ok((start, Token::Dot, end)),
            ".." => Ok((start, Token::DotDot, end)),
            "=" => Ok((start, Token::Equal, end)),
            "->" => Ok((start, Token::LArrow, end)),
            "=>" => Ok((start, Token::LFatArrow, end)),
            "?" => Ok((start, Token::Question, end)),
            ";" => Ok((start, Token::Semi, end)),
            symbol if symbol.starts_with("|||") => Ok(self.continue_line_doc(start)),
            symbol if symbol.starts_with("--") => Ok(self.continue_line_comment(start)),
            _ => Err(
                Diagnostic::new_error(format!("unexpected symbol `{}`", symbol))
                    .with_label(Label::new_primary(self.span(start, end))),
            ),
        }
    }

    /// Consume a name
    fn continue_name(&mut self, start: ByteIndex) -> SpannedToken<'file> {
        let (end, name) = self.take_while(start, is_name_continue);

        let token = match name {
            "as" => Token::As,
            "case" => Token::Case,
            "else" => Token::Else,
            "if" => Token::If,
            "import" => Token::Import,
            "in" => Token::In,
            "let" => Token::Let,
            "record" => Token::Record,
            "Record" => Token::RecordType,
            "then" => Token::Then,
            "Type" => Token::Type,
            "where" => Token::Where,
            name => Token::Name(name),
        };

        (start, token, end)
    }

    /// Consume an escape code
    fn start_escape(&mut self) -> Result<char, Diagnostic<FileSpan>> {
        match self.expect_bump()? {
            (_, '\'') => Ok('\''),
            (_, '"') => Ok('"'),
            (_, '\\') => Ok('\\'),
            (_, '/') => Ok('/'),
            (_, 'n') => Ok('\n'),
            (_, 'r') => Ok('\r'),
            (_, 't') => Ok('\t'),
            // TODO: Unicode escape codes
            (start, ch) => Err({
                let end = start + ByteSize::from_char_len_utf8(ch);
                Diagnostic::new_error(format!("unknown escape code `\\{}`", ch))
                    .with_label(Label::new_primary(self.span(start, end)))
            }),
        }
    }

    /// Consume a string literal
    fn continue_string_literal(
        &mut self,
        start: ByteIndex,
    ) -> Result<SpannedToken<'file>, Diagnostic<FileSpan>> {
        let mut string = String::new();
        let mut end = start;

        while let Some((next, ch)) = self.bump() {
            end = next + ByteSize::from_char_len_utf8(ch);
            match ch {
                '\\' => string.push(self.start_escape()?),
                '"' => return Ok((start, Token::StringLiteral(string), end)),
                ch => string.push(ch),
            }
        }

        Err(Diagnostic::new_error("unterminated string literal")
            .with_label(Label::new_primary(self.span(start, end))))
    }

    /// Consume a character literal
    fn continue_char_literal(
        &mut self,
        start: ByteIndex,
    ) -> Result<SpannedToken<'file>, Diagnostic<FileSpan>> {
        let ch = match self.expect_bump()? {
            (_, '\\') => self.start_escape()?,
            (next, '\'') => {
                let end = next + ByteSize::from_char_len_utf8('\'');
                return Err(Diagnostic::new_error("empty character literal")
                    .with_label(Label::new_primary(self.span(start, end))));
            },
            (_, ch) => ch,
        };

        match self.expect_bump()? {
            (end, '\'') => Ok((
                start,
                Token::CharLiteral(ch),
                end + ByteSize::from_char_len_utf8('\''),
            )),
            (next, ch) => Err({
                let end = next + ByteSize::from_char_len_utf8(ch);
                Diagnostic::new_error("unterminated character literal")
                    .with_label(Label::new_primary(self.span(start, end)))
            }),
        }
    }

    /// Consume a number starting with zero
    fn continue_zero_number(
        &mut self,
        start: ByteIndex,
    ) -> Result<(ByteIndex, Token<&'file str>, ByteIndex), Diagnostic<FileSpan>> {
        match self.lookahead() {
            Some((_, 'b')) => self.continue_bin_literal(start),
            Some((_, 'o')) => self.continue_oct_literal(start),
            Some((_, 'x')) => self.continue_hex_literal(start),
            _ => self.continue_dec_literal(start),
        }
    }

    /// Consume a binary literal token
    fn continue_bin_literal(
        &mut self,
        start: ByteIndex,
    ) -> Result<(ByteIndex, Token<&'file str>, ByteIndex), Diagnostic<FileSpan>> {
        self.bump(); // skip 'b'
        let (end, src) = self.take_while(start + ByteSize::from_str_len_utf8("0b"), is_bin_digit);
        if src.is_empty() {
            Err(Diagnostic::new_error("unterminated binary literal")
                .with_label(Label::new_primary(self.span(start, end))))
        } else {
            match u64::from_str_radix(src, 2) {
                Ok(value) => Ok((start, Token::BinIntLiteral(value), end)),
                Err(_) => Err(self.error_integer_literal_overflow(start, end, src)),
            }
        }
    }

    /// Consume a octal literal token
    fn continue_oct_literal(
        &mut self,
        start: ByteIndex,
    ) -> Result<(ByteIndex, Token<&'file str>, ByteIndex), Diagnostic<FileSpan>> {
        self.bump(); // skip 'o'
        let (end, src) = self.take_while(start + ByteSize::from_str_len_utf8("0o"), is_oct_digit);
        if src.is_empty() {
            Err(Diagnostic::new_error("unterminated octal literal")
                .with_label(Label::new_primary(self.span(start, end))))
        } else {
            match u64::from_str_radix(src, 8) {
                Ok(value) => Ok((start, Token::OctIntLiteral(value), end)),
                Err(_) => Err(self.error_integer_literal_overflow(start, end, src)),
            }
        }
    }

    /// Consume a decimal literal
    fn continue_dec_literal(
        &mut self,
        start: ByteIndex,
    ) -> Result<SpannedToken<'file>, Diagnostic<FileSpan>> {
        let (end, src) = self.take_while(start, is_dec_digit);

        if let Some((_, '.')) = self.lookahead() {
            self.bump(); // skip '.'
            let (end, src) = self.take_while(start, is_dec_digit);

            match f64::from_str(src) {
                Ok(value) => Ok((start, Token::DecFloatLiteral(value), end)),
                Err(_) => unimplemented!(),
            }
        } else {
            match u64::from_str_radix(src, 10) {
                Ok(value) => Ok((start, Token::DecIntLiteral(value), end)),
                Err(_) => Err(self.error_integer_literal_overflow(start, end, src)),
            }
        }
    }

    /// Consume a hexadecimal literal token
    fn continue_hex_literal(
        &mut self,
        start: ByteIndex,
    ) -> Result<(ByteIndex, Token<&'file str>, ByteIndex), Diagnostic<FileSpan>> {
        self.bump(); // skip 'x'
        let (end, src) = self.take_while(start + ByteSize::from_str_len_utf8("0x"), is_hex_digit);
        if src.is_empty() {
            Err(Diagnostic::new_error("unterminated hexadecimal literal")
                .with_label(Label::new_primary(self.span(start, end))))
        } else {
            match u64::from_str_radix(src, 16) {
                Ok(value) => Ok((start, Token::HexIntLiteral(value), end)),
                Err(_) => Err(self.error_integer_literal_overflow(start, end, src)),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use mltt_span::Files;

    use super::*;

    /// A handy macro to give us a nice syntax for declaring test cases
    ///
    /// This was inspired by the tests in the LALRPOP lexer
    macro_rules! test {
        ($src:expr, $($span:expr => $token:expr,)*) => {{
            let mut files = Files::new();
            let file_id = files.add("test", $src);
            let lexed_tokens: Vec<_> = Lexer::new(&files[file_id])
                .map(|result| result.map_err(|err| format!("{:?}", err)))
                .collect();
            let expected_tokens = vec![$({
                let start = ByteIndex::from($span.find("~").unwrap());
                let end = ByteIndex::from($span.rfind("~").unwrap()) + ByteSize::from(1);
                Ok((start, $token, end))
            }),*];

            assert_eq!(lexed_tokens, expected_tokens);
        }};
    }

    #[test]
    fn data() {
        test! {
            "  hello-hahaha8ABC  ",
            "  ~~~~~~~~~~~~~~~~  " => Token::Name("hello-hahaha8ABC"),
        };
    }

    #[test]
    fn comment() {
        test! {
            "       -- hello this is dog\n  ",
            "       ~~~~~~~~~~~~~~~~~~~~    " => Token::LineComment("hello this is dog"),
        };
    }

    #[test]
    fn line_doc() {
        test! {
            "       ||| hello this is dog",
            "       ~~~~~~~~~~~~~~~~~~~~~" => Token::LineDoc("hello this is dog"),
        };
    }

    #[test]
    fn string_literal() {
        test! {
            r#"  "a" "\t"  "#,
            r#"  ~~~       "# => Token::StringLiteral("a".to_owned()),
            r#"      ~~~~  "# => Token::StringLiteral("\t".to_owned()),
        };
    }

    #[test]
    fn char_literal() {
        test! {
            r"  'a' '\t'  ",
            r"  ~~~       " => Token::CharLiteral('a'),
            r"      ~~~~  " => Token::CharLiteral('\t'),
        };
    }

    #[test]
    fn bin_literal() {
        test! {
            "  0b010110  ",
            "  ~~~~~~~~  " => Token::BinIntLiteral(0b010110),
        };
    }

    #[test]
    fn oct_literal() {
        test! {
            "  0o12371  ",
            "  ~~~~~~~  " => Token::OctIntLiteral(0o12371),
        };
    }

    #[test]
    fn dec_literal() {
        test! {
            "  123 0  ",
            "  ~~~    " => Token::DecIntLiteral(123),
            "      ~  " => Token::DecIntLiteral(0),
        };
    }

    #[test]
    fn hex_literal() {
        test! {
            "  0x123AF  ",
            "  ~~~~~~~  " => Token::HexIntLiteral(0x123AF),
        };
    }

    #[test]
    fn float_literal() {
        test! {
            "  122.345  ",
            "  ~~~~~~~  " => Token::DecFloatLiteral(122.345),
        };
    }

    #[test]
    fn keywords() {
        test! {
            "  as case else if import in let record Record then Type where  ",
            "  ~~                                                              " => Token::As,
            "     ~~~~                                                         " => Token::Case,
            "          ~~~~                                                    " => Token::Else,
            "               ~~                                                 " => Token::If,
            "                  ~~~~~~                                          " => Token::Import,
            "                         ~~                                       " => Token::In,
            "                            ~~~                                   " => Token::Let,
            "                                ~~~~~~                            " => Token::Record,
            "                                       ~~~~~~                     " => Token::RecordType,
            "                                              ~~~~                " => Token::Then,
            "                                                   ~~~~           " => Token::Type,
            "                                                        ~~~~~     " => Token::Where,
        };
    }

    #[test]
    fn symbols() {
        test! {
            r" \ ^ : , .. = -> => ? ; ",
            r" ~                      " => Token::BSlash,
            r"   ~                    " => Token::Caret,
            r"     ~                  " => Token::Colon,
            r"       ~                " => Token::Comma,
            r"         ~~             " => Token::DotDot,
            r"            ~           " => Token::Equal,
            r"              ~~        " => Token::LArrow,
            r"                 ~~     " => Token::LFatArrow,
            r"                    ~   " => Token::Question,
            r"                      ~ " => Token::Semi,
        }
    }

    #[test]
    fn delimiters() {
        test! {
            " ( ) { } [ ] ",
            " ~           " => Token::LParen,
            "   ~         " => Token::RParen,
            "     ~       " => Token::LBrace,
            "       ~     " => Token::RBrace,
            "         ~   " => Token::LBracket,
            "           ~ " => Token::RBracket,
        }
    }
}
