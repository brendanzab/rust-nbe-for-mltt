use language_reporting::{Diagnostic, Label};
use mltt_span::{ByteIndex, ByteSize, File, FileSpan};
use std::iter::Peekable;
use std::str::Chars;

use crate::token::{Token, TokenKind};

/// The keywords used in the language
pub const KEYWORDS: [&str; 3] = ["in", "let", "Type"];

fn is_whitespace(ch: char) -> bool {
    match ch {
        | '\u{0009}' // horizontal tab, '\t'
        | '\u{000A}' // line feed, '\n'
        | '\u{000B}' // vertical tab
        | '\u{000C}' // form feed
        | '\u{000D}' // carriage return, '\r'
        | '\u{0020}' // space, ' '
        | '\u{0085}' // next line
        | '\u{200E}' // left-to-right mark
        | '\u{200F}' // right-to-left mark
        | '\u{2028}' // line separator
        | '\u{2029}' // paragraph separator
        => true,
        _ => false,
    }
}

fn is_symbol(ch: char) -> bool {
    match ch {
        '&' | '!' | ':' | '.' | '=' | '\\' | '/' | '>' | '<' | '-' | '|' | '+' | '*' | '^'
        | '?' => true,
        _ => false,
    }
}

fn is_identifier_start(ch: char) -> bool {
    match ch {
        'a'..='z' | 'A'..='Z' | '_' | '-' => true,
        _ => false,
    }
}

fn is_identifier_continue(ch: char) -> bool {
    match ch {
        '0'..='9' | 'a'..='z' | 'A'..='Z' | '_' | '-' => true,
        _ => false,
    }
}

fn is_bin_digit(ch: char) -> bool {
    match ch {
        '0'..='1' => true,
        _ => false,
    }
}

fn is_oct_digit(ch: char) -> bool {
    match ch {
        '0'..='7' => true,
        _ => false,
    }
}

fn is_dec_digit(ch: char) -> bool {
    match ch {
        '0'..='9' => true,
        _ => false,
    }
}

fn is_hex_digit(ch: char) -> bool {
    match ch {
        '0'..='9' | 'a'..='f' | 'A'..='F' => true,
        _ => false,
    }
}

/// An iterator over a source string that yields `Token`s for subsequent use by
/// the parser
pub struct Lexer<'file> {
    /// The file we are lexing
    file: &'file File,
    /// An iterator of unicode characters to consume
    chars: Peekable<Chars<'file>>,
    /// The start of the next token to be emitted
    token_start: ByteIndex,
    /// The end of the next token to be emitted
    token_end: ByteIndex,
}

impl<'file> Lexer<'file> {
    /// Create a new lexer from the source file
    pub fn new(file: &'file File) -> Lexer<'file> {
        Lexer {
            file,
            chars: file.contents().chars().peekable(),
            token_start: ByteIndex::from(0),
            token_end: ByteIndex::from(0),
        }
    }

    /// Returns a span in the source file
    fn span(&self, start: ByteIndex, end: ByteIndex) -> FileSpan {
        FileSpan::new(self.file.id(), start, end)
    }

    /// Returns the span of the current token in the source file
    fn token_span(&self) -> FileSpan {
        self.span(self.token_start, self.token_end)
    }

    /// Returns the string slice of the current token
    fn token_slice(&self) -> &'file str {
        &self.file.contents()[self.token_start.to_usize()..self.token_end.to_usize()]
    }

    /// Returns the span of the end of the file
    fn eof(&self) -> FileSpan {
        let end = self.file.span().end();
        self.span(end, end)
    }

    /// Create a new error diagnostic at the current token
    fn token_error(&self, message: impl Into<String>) -> Diagnostic<FileSpan> {
        Diagnostic::new_error(message).with_label(Label::new_primary(self.token_span()))
    }

    /// Create a new error diagnostic at the end of file
    fn eof_error(&self, message: impl Into<String>) -> Diagnostic<FileSpan> {
        Diagnostic::new_error(message).with_label(Label::new_primary(self.eof()))
    }

    /// Emit a token and reset the start position, ready for the next token
    fn emit(&mut self, kind: TokenKind) -> Token<'file> {
        let slice = self.token_slice();
        let span = self.token_span();
        self.token_start = self.token_end;
        Token { kind, slice, span }
    }

    /// Return the next character in the source string
    fn peek(&mut self) -> Option<char> {
        self.chars.peek().map(char::clone)
    }

    /// Bump the current position in the source string by one character,
    /// returning the current character and byte position.
    fn advance(&mut self) -> Option<char> {
        let current = self.chars.next();
        self.token_end += match current {
            Some(ch) => ByteSize::from_char_len_utf8(ch),
            None => ByteSize::from(0),
        };
        current
    }

    /// Bump the current position in the source string by one character,
    /// returning the current character or an unexpected end of file error.
    fn expect_advance(&mut self) -> Result<char, Diagnostic<FileSpan>> {
        self.advance()
            .ok_or_else(|| self.eof_error("unexpected end of file"))
    }

    /// Skip characters while the predicate matches the lookahead character.
    fn skip_while(&mut self, mut keep_going: impl FnMut(char) -> bool) {
        while self.peek().map_or(false, |ch| keep_going(ch)) {
            self.advance();
        }
    }

    /// Skip by one character if the predicate matches the lookahead
    fn skip_if(&mut self, predicate: impl Fn(char) -> bool) -> bool {
        match self.peek() {
            Some(ch) if predicate(ch) => {
                self.advance();
                true
            },
            Some(_) | None => false,
        }
    }

    /// Consume a token, returning its tag or none on end of file
    fn consume_token(&mut self) -> Option<Result<TokenKind, Diagnostic<FileSpan>>> {
        self.advance().map(|ch| match ch {
            ',' => Ok(TokenKind::Comma),
            ';' => Ok(TokenKind::Semicolon),
            '(' => Ok(TokenKind::LParen),
            ')' => Ok(TokenKind::RParen),
            '{' => Ok(TokenKind::LBrace),
            '}' => Ok(TokenKind::RBrace),
            '[' => Ok(TokenKind::LBracket),
            ']' => Ok(TokenKind::RBracket),
            '"' => self.consume_string_literal(),
            '\'' => self.consume_char_literal(),
            '0' => self.consume_zero_number(),
            ch if is_dec_digit(ch) => self.consume_dec_literal(),
            ch if is_whitespace(ch) => Ok(self.consume_whitespace()),
            ch if is_symbol(ch) => Ok(self.consume_symbol()),
            ch if is_identifier_start(ch) => Ok(self.consume_identifier()),
            ch => Err(self.token_error(format!("unexpected character `{}`", ch))),
        })
    }

    /// Consume a line comment
    fn consume_line_comment(&mut self) -> TokenKind {
        self.skip_while(|ch| ch != '\n');
        TokenKind::LineComment
    }

    /// Consume a doc comment
    fn consume_line_doc(&mut self) -> TokenKind {
        self.skip_while(|ch| ch != '\n');
        TokenKind::LineDoc
    }

    /// Consume some whitespace
    fn consume_whitespace(&mut self) -> TokenKind {
        self.skip_while(is_whitespace);
        TokenKind::Whitespace
    }

    /// Consume a symbol
    fn consume_symbol(&mut self) -> TokenKind {
        self.skip_while(is_symbol);
        match self.token_slice() {
            "\\" => TokenKind::BSlash,
            "^" => TokenKind::Caret,
            ":" => TokenKind::Colon,
            "," => TokenKind::Comma,
            "." => TokenKind::Dot,
            "=" => TokenKind::Equals,
            "->" => TokenKind::RArrow,
            "=>" => TokenKind::RFatArrow,
            slice if slice.starts_with("|||") => self.consume_line_doc(),
            slice if slice.starts_with("--") => self.consume_line_comment(),
            _ => TokenKind::Symbol,
        }
    }

    /// Consume a identifier
    fn consume_identifier(&mut self) -> TokenKind {
        self.skip_while(is_identifier_continue);
        if KEYWORDS.contains(&self.token_slice()) {
            TokenKind::Keyword
        } else {
            TokenKind::Identifier
        }
    }

    /// Skip an ASCII character code
    fn skip_ascii_char_code(&mut self) -> Result<(), Diagnostic<FileSpan>> {
        if !is_oct_digit(self.expect_advance()?) {
            Err(self.token_error("invalid ASCII character code"))
        } else if !is_hex_digit(self.expect_advance()?) {
            Err(self.token_error("invalid ASCII character code"))
        } else {
            Ok(())
        }
    }

    /// Skip an escape
    fn skip_escape(&mut self) -> Result<(), Diagnostic<FileSpan>> {
        match self.expect_advance()? {
            '\'' | '\"' | '\\' | '/' | 'n' | 'r' | 't' => Ok(()),
            'x' => self.skip_ascii_char_code(),
            'u' => unimplemented!("Unicode escapes"),
            ch => Err(self.token_error(format!("unknown escape code `\\{}`", ch))),
        }
    }

    /// Consume a string literal
    fn consume_string_literal(&mut self) -> Result<TokenKind, Diagnostic<FileSpan>> {
        while let Some(ch) = self.advance() {
            match ch {
                '\\' => self.skip_escape()?,
                '"' => return Ok(TokenKind::StringLiteral),
                _ => {},
            }
        }

        Err(self.token_error("unterminated string literal"))
    }

    /// Consume a character literal
    fn consume_char_literal(&mut self) -> Result<TokenKind, Diagnostic<FileSpan>> {
        match self.expect_advance()? {
            '\\' => self.skip_escape()?,
            '\'' => return Err(self.token_error("empty character literal")),
            _ => {},
        };

        match self.expect_advance()? {
            '\'' => Ok(TokenKind::CharLiteral),
            _ => Err(self.token_error("unterminated character literal")),
        }
    }

    /// Skip some digits, separated by `_`, returning the number of digits consumed
    fn skip_separated_digits(&mut self, is_digit: impl Fn(char) -> bool) -> usize {
        let mut digits = 0;
        loop {
            if self.skip_if(&is_digit) {
                digits += 1;
            } else if !self.skip_if(|ch| ch == '_') {
                break;
            }
        }
        digits
    }

    /// Consume a number starting with zero
    fn consume_zero_number(&mut self) -> Result<TokenKind, Diagnostic<FileSpan>> {
        if self.skip_if(|ch| ch == 'b') {
            self.consume_radix_literal("binary", is_bin_digit)
        } else if self.skip_if(|ch| ch == 'o') {
            self.consume_radix_literal("octal", is_oct_digit)
        } else if self.skip_if(|ch| ch == 'x') {
            self.consume_radix_literal("hexadecimal", is_hex_digit)
        } else {
            self.consume_dec_literal()
        }
    }

    /// Consume an integer literal that uses a specific radix
    fn consume_radix_literal(
        &mut self,
        radix_name: &str,
        is_digit: impl Fn(char) -> bool,
    ) -> Result<TokenKind, Diagnostic<FileSpan>> {
        if self.skip_separated_digits(is_digit) == 0 {
            Err(self.token_error(format!("no valid digits found in {} literal", radix_name)))
        } else {
            Ok(TokenKind::IntLiteral)
        }
    }

    /// Consume float exponents, returning `true` if an exponent was found
    fn skip_float_exponent(&mut self) -> Result<bool, Diagnostic<FileSpan>> {
        if self.skip_if(|ch| ch == 'e' || ch == 'E') {
            unimplemented!("float exponent");
        } else {
            Ok(false)
        }
    }

    /// Consume a decimal literal
    fn consume_dec_literal(&mut self) -> Result<TokenKind, Diagnostic<FileSpan>> {
        // No need to check the number of digits here - we should have already
        // consumed at least one when advancing the lexer at the beginning of
        // the first token.
        self.skip_separated_digits(is_dec_digit);

        if self.skip_if(|ch| ch == '.') {
            // We should see at least one decimal digit at the beginning of
            // the fractional part of the floating point number. This rules
            // out numbers like `0._1`.
            if self.skip_if(is_dec_digit) {
                self.skip_separated_digits(is_dec_digit);
                self.skip_float_exponent()?;
                Ok(TokenKind::FloatLiteral)
            } else if self.skip_float_exponent()? {
                Ok(TokenKind::FloatLiteral)
            } else {
                Err(self.token_error("expected a digit or exponent after the decimal place"))
            }
        } else if self.skip_float_exponent()? {
            Ok(TokenKind::FloatLiteral)
        } else {
            Ok(TokenKind::IntLiteral)
        }
    }
}

impl<'file> Iterator for Lexer<'file> {
    type Item = Result<Token<'file>, Diagnostic<FileSpan>>;

    fn next(&mut self) -> Option<Result<Token<'file>, Diagnostic<FileSpan>>> {
        self.consume_token().map(|tag| Ok(self.emit(tag?)))
    }
}

#[cfg(test)]
mod tests {
    use mltt_span::Files;
    use pretty_assertions::assert_eq;

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
                let (kind, slice) = $token;
                let start = ByteIndex::from($span.find("~").unwrap());
                let end = ByteIndex::from($span.rfind("~").unwrap()) + ByteSize::from(1);
                let span = FileSpan::new(file_id, start, end);
                Ok(Token { kind, slice, span })
            }),*];

            assert_eq!(lexed_tokens, expected_tokens);
        }};
    }

    #[test]
    fn data() {
        test! {
            "  hello-hahaha8ABC  ",
            "~~                  " => (TokenKind::Whitespace, "  "),
            "  ~~~~~~~~~~~~~~~~  " => (TokenKind::Identifier, "hello-hahaha8ABC"),
            "                  ~~" => (TokenKind::Whitespace, "  "),
        };
    }

    #[test]
    fn comment() {
        test! {
            "       -- hello this is dog\n  ",
            "~~~~~~~                        " => (TokenKind::Whitespace, "       "),
            "       ~~~~~~~~~~~~~~~~~~~~    " => (TokenKind::LineComment, "-- hello this is dog"),
            "                           ~~~ " => (TokenKind::Whitespace, "\n  "),
        };
    }

    #[test]
    fn line_doc() {
        test! {
            "       ||| hello this is dog",
            "~~~~~~~                     " => (TokenKind::Whitespace, "       "),
            "       ~~~~~~~~~~~~~~~~~~~~~" => (TokenKind::LineDoc, "||| hello this is dog"),
        };
    }

    #[test]
    fn string_literal() {
        test! {
            r#"  "a" "\t" "hello \x3f \x7F"  "#,
            r#"~~                            "# => (TokenKind::Whitespace, "  "),
            r#"  ~~~                         "# => (TokenKind::StringLiteral, r#""a""#),
            r#"     ~                        "# => (TokenKind::Whitespace, " "),
            r#"      ~~~~                    "# => (TokenKind::StringLiteral, r#""\t""#),
            r#"          ~                   "# => (TokenKind::Whitespace, " "),
            r#"           ~~~~~~~~~~~~~~~~~  "# => (TokenKind::StringLiteral, r#""hello \x3f \x7F""#),
            r#"                            ~~"# => (TokenKind::Whitespace, "  "),
        };
    }

    #[test]
    fn char_literal() {
        test! {
            r"  'a' '\t'  ",
            r"~~          " => (TokenKind::Whitespace, "  "),
            r"  ~~~       " => (TokenKind::CharLiteral, "'a'"),
            r"     ~      " => (TokenKind::Whitespace, " "),
            r"      ~~~~  " => (TokenKind::CharLiteral, r"'\t'"),
            r"          ~~" => (TokenKind::Whitespace, "  "),
        };
    }

    #[test]
    fn bin_literal() {
        test! {
            "  0b010110  ",
            "~~          " => (TokenKind::Whitespace, "  "),
            "  ~~~~~~~~  " => (TokenKind::IntLiteral, "0b010110"),
            "          ~~" => (TokenKind::Whitespace, "  "),
        };
    }

    #[test]
    fn oct_literal() {
        test! {
            "  0o12371  ",
            "~~         " => (TokenKind::Whitespace, "  "),
            "  ~~~~~~~  " => (TokenKind::IntLiteral, "0o12371"),
            "         ~~" => (TokenKind::Whitespace, "  "),
        };
    }

    #[test]
    fn dec_literal() {
        test! {
            "  123 0 1 2345_65_32  ",
            "~~                    " => (TokenKind::Whitespace, "  "),
            "  ~~~                 " => (TokenKind::IntLiteral, "123"),
            "     ~                " => (TokenKind::Whitespace, " "),
            "      ~               " => (TokenKind::IntLiteral, "0"),
            "       ~              " => (TokenKind::Whitespace, " "),
            "        ~             " => (TokenKind::IntLiteral, "1"),
            "         ~            " => (TokenKind::Whitespace, " "),
            "          ~~~~~~~~~~  " => (TokenKind::IntLiteral, "2345_65_32"),
            "                    ~~" => (TokenKind::Whitespace, "  "),
        };
    }

    #[test]
    fn hex_literal() {
        test! {
            "  0x123AF  ",
            "~~         " => (TokenKind::Whitespace, "  "),
            "  ~~~~~~~  " => (TokenKind::IntLiteral, "0x123AF"),
            "         ~~" => (TokenKind::Whitespace, "  "),
        };
    }

    #[test]
    fn float_literal() {
        test! {
            "  122.345 1.0  ",
            "~~             " => (TokenKind::Whitespace, "  "),
            "  ~~~~~~~      " => (TokenKind::FloatLiteral, "122.345"),
            "         ~     " => (TokenKind::Whitespace, " "),
            "          ~~~  " => (TokenKind::FloatLiteral, "1.0"),
            "             ~~" => (TokenKind::Whitespace, "  "),
        };
    }

    #[test]
    fn keywords() {
        test! {
            "  as case else if import in let record Record then Type where  ",
            "~~                                                             " => (TokenKind::Whitespace, "  "),
            "  ~~                                                           " => (TokenKind::Identifier, "as"),
            "    ~                                                          " => (TokenKind::Whitespace, " "),
            "     ~~~~                                                      " => (TokenKind::Identifier, "case"),
            "         ~                                                     " => (TokenKind::Whitespace, " "),
            "          ~~~~                                                 " => (TokenKind::Identifier, "else"),
            "              ~                                                " => (TokenKind::Whitespace, " "),
            "               ~~                                              " => (TokenKind::Identifier, "if"),
            "                 ~                                             " => (TokenKind::Whitespace, " "),
            "                  ~~~~~~                                       " => (TokenKind::Identifier, "import"),
            "                        ~                                      " => (TokenKind::Whitespace, " "),
            "                         ~~                                    " => (TokenKind::Keyword, "in"),
            "                           ~                                   " => (TokenKind::Whitespace, " "),
            "                            ~~~                                " => (TokenKind::Keyword, "let"),
            "                               ~                               " => (TokenKind::Whitespace, " "),
            "                                ~~~~~~                         " => (TokenKind::Identifier, "record"),
            "                                      ~                        " => (TokenKind::Whitespace, " "),
            "                                       ~~~~~~                  " => (TokenKind::Identifier, "Record"),
            "                                             ~                 " => (TokenKind::Whitespace, " "),
            "                                              ~~~~             " => (TokenKind::Identifier, "then"),
            "                                                  ~            " => (TokenKind::Whitespace, " "),
            "                                                   ~~~~        " => (TokenKind::Keyword, "Type"),
            "                                                       ~       " => (TokenKind::Whitespace, " "),
            "                                                        ~~~~~  " => (TokenKind::Identifier, "where"),
            "                                                             ~~" => (TokenKind::Whitespace, "  "),
        };
    }

    #[test]
    fn symbols() {
        test! {
            r" \ ^ : , .. = -> => ? ; ",
            r"~                       " => (TokenKind::Whitespace, " "),
            r" ~                      " => (TokenKind::BSlash, r"\"),
            r"  ~                     " => (TokenKind::Whitespace, " "),
            r"   ~                    " => (TokenKind::Caret, "^"),
            r"    ~                   " => (TokenKind::Whitespace, " "),
            r"     ~                  " => (TokenKind::Colon, ":"),
            r"      ~                 " => (TokenKind::Whitespace, " "),
            r"       ~                " => (TokenKind::Comma, ","),
            r"        ~               " => (TokenKind::Whitespace, " "),
            r"         ~~             " => (TokenKind::Symbol, ".."),
            r"           ~            " => (TokenKind::Whitespace, " "),
            r"            ~           " => (TokenKind::Equals, "="),
            r"             ~          " => (TokenKind::Whitespace, " "),
            r"              ~~        " => (TokenKind::RArrow, "->"),
            r"                ~       " => (TokenKind::Whitespace, " "),
            r"                 ~~     " => (TokenKind::RFatArrow, "=>"),
            r"                   ~    " => (TokenKind::Whitespace, " "),
            r"                    ~   " => (TokenKind::Symbol, "?"),
            r"                     ~  " => (TokenKind::Whitespace, " "),
            r"                      ~ " => (TokenKind::Semicolon, ";"),
            r"                       ~" => (TokenKind::Whitespace, " "),
        }
    }

    #[test]
    fn delimiters() {
        test! {
            " ( ) { } [ ] ",
            "~            " => (TokenKind::Whitespace, " "),
            " ~           " => (TokenKind::LParen, "("),
            "  ~          " => (TokenKind::Whitespace, " "),
            "   ~         " => (TokenKind::RParen, ")"),
            "    ~        " => (TokenKind::Whitespace, " "),
            "     ~       " => (TokenKind::LBrace, "{"),
            "      ~      " => (TokenKind::Whitespace, " "),
            "       ~     " => (TokenKind::RBrace, "}"),
            "        ~    " => (TokenKind::Whitespace, " "),
            "         ~   " => (TokenKind::LBracket, "["),
            "          ~  " => (TokenKind::Whitespace, " "),
            "           ~ " => (TokenKind::RBracket, "]"),
            "            ~" => (TokenKind::Whitespace, " "),
        }
    }
}
