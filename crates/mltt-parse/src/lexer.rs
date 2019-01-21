use language_reporting::{Diagnostic, Label};
use mltt_span::{ByteIndex, ByteSize, File, FileSpan};
use std::str::Chars;

use crate::token::{Token, TokenTag};

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
        '&' | '!' | ':' | ',' | '.' | '=' | '\\' | '/' | '>' | '<' | '-' | '|' | '+' | ';'
        | '*' | '^' | '?' => true,
        _ => false,
    }
}

fn is_delimiter(ch: char) -> bool {
    match ch {
        '(' | ')' | '{' | '}' | '[' | ']' => true,
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
    chars: Chars<'file>,
    /// The start of the next token to be emitted
    token_start: ByteIndex,
    /// The end of the next token to be emitted
    token_end: ByteIndex,
    /// The current character that we are looking at
    current: Option<char>,
}

impl<'file> Lexer<'file> {
    /// Create a new lexer from the source string
    pub fn new(file: &'file File) -> Lexer<'file> {
        Lexer {
            file,
            chars: file.contents().chars(),
            token_start: ByteIndex::from(0),
            token_end: ByteIndex::from(0),
            current: None,
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
    fn emit(&mut self, tag: TokenTag) -> Token<'file> {
        let slice = &self.file.contents()[self.token_start.to_usize()..self.token_end.to_usize()];
        let span = self.token_span();
        self.token_start = self.token_end;
        Token { tag, slice, span }
    }

    /// Return the next character in the source string
    fn peek(&self) -> Option<char> {
        self.chars.clone().next()
    }

    /// Bump the current position in the source string by one character,
    /// returning the current character and byte position.
    fn advance(&mut self) -> Option<char> {
        self.current = self.chars.next();
        self.token_end += match self.current {
            Some(ch) => ByteSize::from_char_len_utf8(ch),
            None => ByteSize::from(0),
        };

        self.current
    }

    /// Advances the lexer by one token if the predicate matches
    fn peek_advance(&mut self, advance_if: impl Fn(char) -> bool) -> bool {
        match self.peek() {
            Some(ch) if advance_if(ch) => {
                self.advance();
                true
            },
            Some(_) | None => false,
        }
    }

    /// Bump the current position in the source string by one character,
    /// returning the current character and byte position, or returning an
    /// unexpected end of file error.
    fn expect_advance(&mut self) -> Result<char, Diagnostic<FileSpan>> {
        self.advance()
            .ok_or_else(|| self.eof_error("unexpected end of file"))
    }

    /// Consume characters while the predicate matches for the current
    /// character, then return the consumed slice and the end byte
    /// position.
    fn take_while(&mut self, mut keep_going: impl FnMut(char) -> bool) {
        while self.peek().map_or(false, |ch| keep_going(ch)) {
            self.advance();
        }
    }

    /// Consume a token
    fn consume_token(&mut self) -> Option<Result<TokenTag, Diagnostic<FileSpan>>> {
        self.advance().map(|ch| match ch {
            '"' => self.consume_string_literal(),
            '\'' => self.consume_char_literal(),
            '0' => self.consume_zero_number(),
            ch if is_dec_digit(ch) => self.consume_dec_literal(),
            ch if is_whitespace(ch) => Ok(self.consume_whitespace()),
            ch if is_symbol(ch) => Ok(self.consume_symbol()),
            ch if is_delimiter(ch) => Ok(TokenTag::Delimiter),
            ch if is_identifier_start(ch) => Ok(self.consume_identifier()),
            ch => Err(self.token_error(format!("unexpected character `{}`", ch))),
        })
    }

    /// Consume a line comment
    fn consume_line_comment(&mut self) -> TokenTag {
        self.take_while(|ch| ch != '\n');
        TokenTag::LineComment
    }

    /// Consume a doc comment
    fn consume_line_doc(&mut self) -> TokenTag {
        self.take_while(|ch| ch != '\n');
        TokenTag::LineDoc
    }

    /// Consume some whitespace
    fn consume_whitespace(&mut self) -> TokenTag {
        self.take_while(is_whitespace);
        TokenTag::Whitespace
    }

    /// Consume a symbol
    fn consume_symbol(&mut self) -> TokenTag {
        match &self.file.contents()[self.token_start.to_usize()..] {
            symbol if symbol.starts_with("|||") => self.consume_line_doc(),
            symbol if symbol.starts_with("--") => self.consume_line_comment(),
            _ => {
                self.take_while(is_symbol);
                TokenTag::Symbol
            },
        }
    }

    /// Consume a identifier
    fn consume_identifier(&mut self) -> TokenTag {
        self.take_while(is_identifier_continue);
        TokenTag::Identifier
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
    fn consume_string_literal(&mut self) -> Result<TokenTag, Diagnostic<FileSpan>> {
        while let Some(ch) = self.advance() {
            match ch {
                '\\' => self.skip_escape()?,
                '"' => return Ok(TokenTag::StringLiteral),
                _ => {},
            }
        }

        Err(self.token_error("unterminated string literal"))
    }

    /// Consume a character literal
    fn consume_char_literal(&mut self) -> Result<TokenTag, Diagnostic<FileSpan>> {
        match self.expect_advance()? {
            '\\' => self.skip_escape()?,
            '\'' => return Err(self.token_error("empty character literal")),
            _ => {},
        };

        match self.expect_advance()? {
            '\'' => Ok(TokenTag::CharLiteral),
            _ => Err(self.token_error("unterminated character literal")),
        }
    }

    /// Skip some digits, separated by `_`, returning the number of digits consumed
    fn skip_separated_digits(&mut self, is_digit: impl Fn(char) -> bool) -> usize {
        let mut digits = 0;
        self.take_while(|ch| {
            if is_digit(ch) {
                digits += 1;
                true
            } else {
                ch == '_'
            }
        });
        digits
    }

    /// Consume a number starting with zero
    fn consume_zero_number(&mut self) -> Result<TokenTag, Diagnostic<FileSpan>> {
        if self.peek_advance(|ch| ch == 'b') {
            self.consume_bin_literal()
        } else if self.peek_advance(|ch| ch == 'o') {
            self.consume_oct_literal()
        } else if self.peek_advance(|ch| ch == 'x') {
            self.consume_hex_literal()
        } else {
            self.consume_dec_literal()
        }
    }

    /// Consume a binary literal token
    fn consume_bin_literal(&mut self) -> Result<TokenTag, Diagnostic<FileSpan>> {
        if self.skip_separated_digits(is_bin_digit) == 0 {
            Err(self.token_error("no valid digits found in binary literal"))
        } else {
            Ok(TokenTag::IntLiteral)
        }
    }

    /// Consume a octal literal token
    fn consume_oct_literal(&mut self) -> Result<TokenTag, Diagnostic<FileSpan>> {
        if self.skip_separated_digits(is_oct_digit) == 0 {
            Err(self.token_error("no valid digits found in octal literal"))
        } else {
            Ok(TokenTag::IntLiteral)
        }
    }

    /// Consume a hexadecimal literal token
    fn consume_hex_literal(&mut self) -> Result<TokenTag, Diagnostic<FileSpan>> {
        if self.skip_separated_digits(is_hex_digit) == 0 {
            Err(self.token_error("no valid digits found in hexadecimal literal"))
        } else {
            Ok(TokenTag::IntLiteral)
        }
    }

    /// Consume float exponents, returning `true` if an exponent was found
    fn skip_float_exponent(&mut self) -> Result<bool, Diagnostic<FileSpan>> {
        if self.peek_advance(|ch| ch == 'e' || ch == 'E') {
            unimplemented!("float exponent");
        } else {
            Ok(false)
        }
    }

    /// Consume a decimal literal
    fn consume_dec_literal(&mut self) -> Result<TokenTag, Diagnostic<FileSpan>> {
        // No need to check the number of digits here - we should have already
        // consumed at least one when advancing the lexer at the beginning of
        // the first token.
        self.skip_separated_digits(is_dec_digit);

        if self.peek_advance(|ch| ch == '.') {
            // We should see at least one decimal digit at the beginning of
            // the fractional part of the floating point number. This rules
            // out numbers like `0._1`.
            if self.peek_advance(is_dec_digit) {
                self.skip_separated_digits(is_dec_digit);
                self.skip_float_exponent()?;
                Ok(TokenTag::FloatLiteral)
            } else if self.skip_float_exponent()? {
                Ok(TokenTag::FloatLiteral)
            } else {
                Err(self.token_error("expected a digit or exponent after the decimal place"))
            }
        } else if self.skip_float_exponent()? {
            Ok(TokenTag::FloatLiteral)
        } else {
            Ok(TokenTag::IntLiteral)
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
                let (tag, slice) = $token;
                let start = ByteIndex::from($span.find("~").unwrap());
                let end = ByteIndex::from($span.rfind("~").unwrap()) + ByteSize::from(1);
                let span = FileSpan::new(file_id, start, end);
                Ok(Token { tag, slice, span })
            }),*];

            assert_eq!(lexed_tokens, expected_tokens);
        }};
    }

    #[test]
    fn data() {
        test! {
            "  hello-hahaha8ABC  ",
            "~~                  " => (TokenTag::Whitespace, "  "),
            "  ~~~~~~~~~~~~~~~~  " => (TokenTag::Identifier, "hello-hahaha8ABC"),
            "                  ~~" => (TokenTag::Whitespace, "  "),
        };
    }

    #[test]
    fn comment() {
        test! {
            "       -- hello this is dog\n  ",
            "~~~~~~~                        " => (TokenTag::Whitespace, "       "),
            "       ~~~~~~~~~~~~~~~~~~~~    " => (TokenTag::LineComment, "-- hello this is dog"),
            "                           ~~~ " => (TokenTag::Whitespace, "\n  "),
        };
    }

    #[test]
    fn line_doc() {
        test! {
            "       ||| hello this is dog",
            "~~~~~~~                     " => (TokenTag::Whitespace, "       "),
            "       ~~~~~~~~~~~~~~~~~~~~~" => (TokenTag::LineDoc, "||| hello this is dog"),
        };
    }

    #[test]
    fn string_literal() {
        test! {
            r#"  "a" "\t" "hello \x3f \x7F"  "#,
            r#"~~                            "# => (TokenTag::Whitespace, "  "),
            r#"  ~~~                         "# => (TokenTag::StringLiteral, r#""a""#),
            r#"     ~                        "# => (TokenTag::Whitespace, " "),
            r#"      ~~~~                    "# => (TokenTag::StringLiteral, r#""\t""#),
            r#"          ~                   "# => (TokenTag::Whitespace, " "),
            r#"           ~~~~~~~~~~~~~~~~~  "# => (TokenTag::StringLiteral, r#""hello \x3f \x7F""#),
            r#"                            ~~"# => (TokenTag::Whitespace, "  "),
        };
    }

    #[test]
    fn char_literal() {
        test! {
            r"  'a' '\t'  ",
            r"~~          " => (TokenTag::Whitespace, "  "),
            r"  ~~~       " => (TokenTag::CharLiteral, "'a'"),
            r"     ~      " => (TokenTag::Whitespace, " "),
            r"      ~~~~  " => (TokenTag::CharLiteral, r"'\t'"),
            r"          ~~" => (TokenTag::Whitespace, "  "),
        };
    }

    #[test]
    fn bin_literal() {
        test! {
            "  0b010110  ",
            "~~          " => (TokenTag::Whitespace, "  "),
            "  ~~~~~~~~  " => (TokenTag::IntLiteral, "0b010110"),
            "          ~~" => (TokenTag::Whitespace, "  "),
        };
    }

    #[test]
    fn oct_literal() {
        test! {
            "  0o12371  ",
            "~~         " => (TokenTag::Whitespace, "  "),
            "  ~~~~~~~  " => (TokenTag::IntLiteral, "0o12371"),
            "         ~~" => (TokenTag::Whitespace, "  "),
        };
    }

    #[test]
    fn dec_literal() {
        test! {
            "  123 0 1 2345_65_32  ",
            "~~                    " => (TokenTag::Whitespace, "  "),
            "  ~~~                 " => (TokenTag::IntLiteral, "123"),
            "     ~                " => (TokenTag::Whitespace, " "),
            "      ~               " => (TokenTag::IntLiteral, "0"),
            "       ~              " => (TokenTag::Whitespace, " "),
            "        ~             " => (TokenTag::IntLiteral, "1"),
            "         ~            " => (TokenTag::Whitespace, " "),
            "          ~~~~~~~~~~  " => (TokenTag::IntLiteral, "2345_65_32"),
            "                    ~~" => (TokenTag::Whitespace, "  "),
        };
    }

    #[test]
    fn hex_literal() {
        test! {
            "  0x123AF  ",
            "~~         " => (TokenTag::Whitespace, "  "),
            "  ~~~~~~~  " => (TokenTag::IntLiteral, "0x123AF"),
            "         ~~" => (TokenTag::Whitespace, "  "),
        };
    }

    #[test]
    fn float_literal() {
        test! {
            "  122.345 1.0  ",
            "~~             " => (TokenTag::Whitespace, "  "),
            "  ~~~~~~~      " => (TokenTag::FloatLiteral, "122.345"),
            "         ~     " => (TokenTag::Whitespace, " "),
            "          ~~~  " => (TokenTag::FloatLiteral, "1.0"),
            "             ~~" => (TokenTag::Whitespace, "  "),
        };
    }

    #[test]
    fn keywords() {
        test! {
            "  as case else if import in let record Record then Type where  ",
            "~~                                                             " => (TokenTag::Whitespace, "  "),
            "  ~~                                                           " => (TokenTag::Identifier, "as"),
            "    ~                                                          " => (TokenTag::Whitespace, " "),
            "     ~~~~                                                      " => (TokenTag::Identifier, "case"),
            "         ~                                                     " => (TokenTag::Whitespace, " "),
            "          ~~~~                                                 " => (TokenTag::Identifier, "else"),
            "              ~                                                " => (TokenTag::Whitespace, " "),
            "               ~~                                              " => (TokenTag::Identifier, "if"),
            "                 ~                                             " => (TokenTag::Whitespace, " "),
            "                  ~~~~~~                                       " => (TokenTag::Identifier, "import"),
            "                        ~                                      " => (TokenTag::Whitespace, " "),
            "                         ~~                                    " => (TokenTag::Identifier, "in"),
            "                           ~                                   " => (TokenTag::Whitespace, " "),
            "                            ~~~                                " => (TokenTag::Identifier, "let"),
            "                               ~                               " => (TokenTag::Whitespace, " "),
            "                                ~~~~~~                         " => (TokenTag::Identifier, "record"),
            "                                      ~                        " => (TokenTag::Whitespace, " "),
            "                                       ~~~~~~                  " => (TokenTag::Identifier, "Record"),
            "                                             ~                 " => (TokenTag::Whitespace, " "),
            "                                              ~~~~             " => (TokenTag::Identifier, "then"),
            "                                                  ~            " => (TokenTag::Whitespace, " "),
            "                                                   ~~~~        " => (TokenTag::Identifier, "Type"),
            "                                                       ~       " => (TokenTag::Whitespace, " "),
            "                                                        ~~~~~  " => (TokenTag::Identifier, "where"),
            "                                                             ~~" => (TokenTag::Whitespace, "  "),
        };
    }

    #[test]
    fn symbols() {
        test! {
            r" \ ^ : , .. = -> => ? ; ",
            r"~                       " => (TokenTag::Whitespace, " "),
            r" ~                      " => (TokenTag::Symbol, r"\"),
            r"  ~                     " => (TokenTag::Whitespace, " "),
            r"   ~                    " => (TokenTag::Symbol, "^"),
            r"    ~                   " => (TokenTag::Whitespace, " "),
            r"     ~                  " => (TokenTag::Symbol, ":"),
            r"      ~                 " => (TokenTag::Whitespace, " "),
            r"       ~                " => (TokenTag::Symbol, ","),
            r"        ~               " => (TokenTag::Whitespace, " "),
            r"         ~~             " => (TokenTag::Symbol, ".."),
            r"           ~            " => (TokenTag::Whitespace, " "),
            r"            ~           " => (TokenTag::Symbol, "="),
            r"             ~          " => (TokenTag::Whitespace, " "),
            r"              ~~        " => (TokenTag::Symbol, "->"),
            r"                ~       " => (TokenTag::Whitespace, " "),
            r"                 ~~     " => (TokenTag::Symbol, "=>"),
            r"                   ~    " => (TokenTag::Whitespace, " "),
            r"                    ~   " => (TokenTag::Symbol, "?"),
            r"                     ~  " => (TokenTag::Whitespace, " "),
            r"                      ~ " => (TokenTag::Symbol, ";"),
            r"                       ~" => (TokenTag::Whitespace, " "),
        }
    }

    #[test]
    fn delimiters() {
        test! {
            " ( ) { } [ ] ",
            "~            " => (TokenTag::Whitespace, " "),
            " ~           " => (TokenTag::Delimiter, "("),
            "  ~          " => (TokenTag::Whitespace, " "),
            "   ~         " => (TokenTag::Delimiter, ")"),
            "    ~        " => (TokenTag::Whitespace, " "),
            "     ~       " => (TokenTag::Delimiter, "{"),
            "      ~      " => (TokenTag::Whitespace, " "),
            "       ~     " => (TokenTag::Delimiter, "}"),
            "        ~    " => (TokenTag::Whitespace, " "),
            "         ~   " => (TokenTag::Delimiter, "["),
            "          ~  " => (TokenTag::Whitespace, " "),
            "           ~ " => (TokenTag::Delimiter, "]"),
            "            ~" => (TokenTag::Whitespace, " "),
        }
    }
}
