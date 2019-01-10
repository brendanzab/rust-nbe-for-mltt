use std::fmt;
use std::str::{CharIndices, FromStr};

fn is_symbol(ch: char) -> bool {
    match ch {
        '&' | '!' | ':' | ',' | '.' | '=' | '/' | '>' | '<' | '-' | '|' | '+' | ';' | '*' | '^'
        | '?' => true,
        _ => false,
    }
}

fn is_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_' || ch == '-'
}

fn is_ident_continue(ch: char) -> bool {
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

/// An error that occurred while lexing the source file
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LexerError {
    UnexpectedCharacter { start: usize, found: char },
    UnexpectedEof { end: usize },
    UnterminatedStringLiteral { span: (usize, usize) },
    UnterminatedCharLiteral { span: (usize, usize) },
    UnterminatedBinLiteral { span: (usize, usize) },
    UnterminatedOctLiteral { span: (usize, usize) },
    UnterminatedHexLiteral { span: (usize, usize) },
    EmptyCharLiteral { span: (usize, usize) },
    UnknownEscapeCode { start: usize, found: char },
    IntegerLiteralOverflow { span: (usize, usize), value: String },
}

impl fmt::Display for LexerError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            LexerError::UnexpectedCharacter { found, .. } => {
                write!(f, "An unexpected character {:?} was found.", found)
            },
            LexerError::UnexpectedEof { .. } => write!(f, "Unexpected end of file."),
            LexerError::UnterminatedStringLiteral { .. } => {
                write!(f, "Unterminated string literal.")
            },
            LexerError::UnterminatedCharLiteral { .. } => {
                write!(f, "Unterminated character literal.")
            },
            LexerError::UnterminatedBinLiteral { .. } => {
                write!(f, "Unterminated a binary literal.")
            },
            LexerError::UnterminatedOctLiteral { .. } => write!(f, "Unterminated a octal literal."),
            LexerError::UnterminatedHexLiteral { .. } => {
                write!(f, "Unterminated a hexidecimal literal.")
            },
            LexerError::EmptyCharLiteral { .. } => write!(f, "Empty character literal."),
            LexerError::UnknownEscapeCode { found, .. } => {
                write!(f, "An unknown escape code \\{} was found.", found)
            },
            LexerError::IntegerLiteralOverflow { ref value, .. } => write!(
                f,
                "An integer literal {} was too large for the target type.",
                value
            ),
        }
    }
}

/// A token in the source file, to be emitted by the `Lexer`
#[derive(Clone, Debug, PartialEq)]
pub enum Token<S> {
    // Data
    Ident(S),
    DocComment(S),
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
            Token::Ident(ref name) => write!(f, "{}", name),
            Token::DocComment(ref comment) => write!(f, "||| {}", comment),
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

impl<'input> From<Token<&'input str>> for Token<String> {
    fn from(src: Token<&'input str>) -> Token<String> {
        match src {
            Token::Ident(name) => Token::Ident(name.to_owned()),
            Token::DocComment(comment) => Token::DocComment(comment.to_owned()),
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
pub struct Lexer<'input> {
    src: &'input str,
    chars: CharIndices<'input>,
    lookahead: Option<(usize, char)>,
}

impl<'input> Lexer<'input> {
    /// Create a new lexer from the source string
    pub fn new(src: &'input str) -> Self {
        let mut chars = src.char_indices();

        Lexer {
            src,
            lookahead: chars.next(),
            chars,
        }
    }

    /// Returns the index of the end of the file
    fn eof(&self) -> usize {
        self.src.len()
    }

    /// Return the next character in the source string
    fn lookahead(&self) -> Option<(usize, char)> {
        self.lookahead
    }

    /// Bump the current position in the source string by one character,
    /// returning the current character and byte position.
    fn bump(&mut self) -> Option<(usize, char)> {
        let current = self.lookahead();
        self.lookahead = self.chars.next();
        current
    }

    /// Return a slice of the source string
    fn slice(&self, start: usize, end: usize) -> &'input str {
        &self.src[start..end]
    }

    /// Test a predicate against the next character in the source
    fn test_lookahead<F>(&self, mut pred: F) -> bool
    where
        F: FnMut(char) -> bool,
    {
        self.lookahead.map_or(false, |(_, ch)| pred(ch))
    }

    /// Consume characters while the predicate matches for the current
    /// character, then return the consumed slice and the end byte
    /// position.
    fn take_while<F>(&mut self, start: usize, mut keep_going: F) -> (usize, &'input str)
    where
        F: FnMut(char) -> bool,
    {
        self.take_until(start, |ch| !keep_going(ch))
    }

    /// Consume characters until the predicate matches for the next character
    /// in the lookahead, then return the consumed slice and the end byte
    /// position.
    fn take_until<F>(&mut self, start: usize, mut terminate: F) -> (usize, &'input str)
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

    /// Consume a doc comment
    fn doc_comment(&mut self, start: usize) -> SpannedToken<'input> {
        let (end, mut comment) = self.take_until(start + "|||".len(), |ch| ch == '\n');

        // Skip preceding space
        if comment.starts_with(' ') {
            comment = &comment[1..];
        }

        (start, Token::DocComment(comment), end)
    }

    /// Consume an identifier
    fn ident(&mut self, start: usize) -> SpannedToken<'input> {
        let (end, ident) = self.take_while(start, is_ident_continue);

        let token = match ident {
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
            ident => Token::Ident(ident),
        };

        (start, token, end)
    }

    /// Consume an escape code
    fn escape_code(&mut self, start: usize) -> Result<char, LexerError> {
        match self.bump() {
            Some((_, '\'')) => Ok('\''),
            Some((_, '"')) => Ok('"'),
            Some((_, '\\')) => Ok('\\'),
            Some((_, '/')) => Ok('/'),
            Some((_, 'n')) => Ok('\n'),
            Some((_, 'r')) => Ok('\r'),
            Some((_, 't')) => Ok('\t'),
            // TODO: Unicode escape codes
            Some((start, ch)) => Err(LexerError::UnknownEscapeCode { start, found: ch }),
            None => Err(LexerError::UnexpectedEof { end: start }),
        }
    }

    /// Consume a string literal
    fn string_literal(&mut self, start: usize) -> Result<SpannedToken<'input>, LexerError> {
        let mut string = String::new();
        let mut end = start;

        while let Some((next, ch)) = self.bump() {
            end = next + ch.len_utf8();
            match ch {
                '\\' => string.push(self.escape_code(next)?),
                '"' => return Ok((start, Token::StringLiteral(string), end)),
                ch => string.push(ch),
            }
        }

        Err(LexerError::UnterminatedStringLiteral { span: (start, end) })
    }

    /// Consume a character literal
    fn char_literal(&mut self, start: usize) -> Result<SpannedToken<'input>, LexerError> {
        let ch = match self.bump() {
            Some((next, '\\')) => self.escape_code(next)?,
            Some((next, '\'')) => {
                return Err(LexerError::EmptyCharLiteral {
                    span: (start, next + '\''.len_utf8()),
                });
            },
            Some((_, ch)) => ch,
            None => return Err(LexerError::UnexpectedEof { end: start }),
        };

        match self.bump() {
            Some((end, '\'')) => Ok((start, Token::CharLiteral(ch), end + '\''.len_utf8())),
            Some((next, ch)) => Err(LexerError::UnterminatedCharLiteral {
                span: (start, next + ch.len_utf8()),
            }),
            None => Err(LexerError::UnexpectedEof { end: start }),
        }
    }

    /// Consume a binary literal token
    fn bin_literal(
        &mut self,
        start: usize,
    ) -> Result<(usize, Token<&'input str>, usize), LexerError> {
        self.bump(); // skip 'b'
        let (end, src) = self.take_while(start + 2, is_bin_digit);
        if src.is_empty() {
            Err(LexerError::UnterminatedBinLiteral { span: (start, end) })
        } else {
            let int = u64::from_str_radix(src, 2).unwrap();
            Ok((start, Token::BinIntLiteral(int), end))
        }
    }

    /// Consume a octal literal token
    fn oct_literal(
        &mut self,
        start: usize,
    ) -> Result<(usize, Token<&'input str>, usize), LexerError> {
        self.bump(); // skip 'o'
        let (end, src) = self.take_while(start + 2, is_oct_digit);
        if src.is_empty() {
            Err(LexerError::UnterminatedOctLiteral { span: (start, end) })
        } else {
            let int = u64::from_str_radix(src, 8).unwrap();
            Ok((start, Token::OctIntLiteral(int), end))
        }
    }

    /// Consume a decimal literal
    fn dec_literal(&mut self, start: usize) -> Result<SpannedToken<'input>, LexerError> {
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
                Err(_) => Err(LexerError::IntegerLiteralOverflow {
                    span: (start, end),
                    value: src.to_string(),
                }),
            }
        }
    }

    /// Consume a hexadecimal literal token
    fn hex_literal(
        &mut self,
        start: usize,
    ) -> Result<(usize, Token<&'input str>, usize), LexerError> {
        self.bump(); // skip 'x'
        let (end, src) = self.take_while(start + 2, is_hex_digit);
        if src.is_empty() {
            Err(LexerError::UnterminatedHexLiteral { span: (start, end) })
        } else {
            let int = u64::from_str_radix(src, 16).unwrap();
            Ok((start, Token::HexIntLiteral(int), end))
        }
    }
}

pub type SpannedToken<'input> = (usize, Token<&'input str>, usize);

impl<'input> Iterator for Lexer<'input> {
    type Item = Result<(usize, Token<&'input str>, usize), LexerError>;

    fn next(&mut self) -> Option<Result<SpannedToken<'input>, LexerError>> {
        while let Some((start, ch)) = self.bump() {
            let end = start + ch.len_utf8();

            return Some(match ch {
                ch if is_symbol(ch) => {
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
                        symbol if symbol.starts_with("|||") => Ok(self.doc_comment(start)),
                        symbol if symbol.starts_with("--") => {
                            self.take_until(start, |ch| ch == '\n');
                            continue;
                        },
                        _ => Err(LexerError::UnexpectedCharacter { start, found: ch }),
                    }
                },
                '\\' => Ok((start, Token::BSlash, end)),
                '(' => Ok((start, Token::LParen, end)),
                ')' => Ok((start, Token::RParen, end)),
                '{' => Ok((start, Token::LBrace, end)),
                '}' => Ok((start, Token::RBrace, end)),
                '[' => Ok((start, Token::LBracket, end)),
                ']' => Ok((start, Token::RBracket, end)),
                '"' => self.string_literal(start),
                '\'' => self.char_literal(start),
                '0' if self.test_lookahead(|x| x == 'b') => self.bin_literal(start),
                '0' if self.test_lookahead(|x| x == 'o') => self.oct_literal(start),
                '0' if self.test_lookahead(|x| x == 'x') => self.hex_literal(start),
                ch if is_ident_start(ch) => Ok(self.ident(start)),
                ch if is_dec_digit(ch) => self.dec_literal(start),
                ch if ch.is_whitespace() => continue,
                _ => Err(LexerError::UnexpectedCharacter { start, found: ch }),
            });
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A handy macro to give us a nice syntax for declaring test cases
    ///
    /// This was inspired by the tests in the LALRPOP lexer
    macro_rules! test {
        ($src:expr, $($span:expr => $token:expr,)*) => {{
            let lexed_tokens: Vec<_> = Lexer::new(&$src).collect();
            let expected_tokens = vec![$({
                let start = $span.find("~").unwrap();
                let end = $span.rfind("~").unwrap() + 1;
                Ok((start, $token, end))
            }),*];

            assert_eq!(lexed_tokens, expected_tokens);
        }};
    }

    #[test]
    fn data() {
        test! {
            "  hello-hahaha8ABC  ",
            "  ~~~~~~~~~~~~~~~~  " => Token::Ident("hello-hahaha8ABC"),
        };
    }

    #[test]
    fn comment() {
        test! {
            "       -- hello this is dog\n  ",
        };
    }

    #[test]
    fn doc_comment() {
        test! {
            "       ||| hello this is dog",
            "       ~~~~~~~~~~~~~~~~~~~~~" => Token::DocComment("hello this is dog"),
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
            "  123  ",
            "  ~~~  " => Token::DecIntLiteral(123),
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
