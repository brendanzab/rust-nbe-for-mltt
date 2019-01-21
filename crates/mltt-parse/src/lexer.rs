use language_reporting::{Diagnostic, Label};
use mltt_span::{ByteIndex, ByteSize, File, FileSpan};
use std::str::CharIndices;

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
    file: &'file File,
    chars: CharIndices<'file>,
    lookahead: Option<(usize, char)>,
}

impl<'file> Iterator for Lexer<'file> {
    type Item = Result<Token<'file>, Diagnostic<FileSpan>>;

    fn next(&mut self) -> Option<Result<Token<'file>, Diagnostic<FileSpan>>> {
        while let Some((start, ch)) = self.advance() {
            let end = start + ByteSize::from_char_len_utf8(ch);

            return Some(match ch {
                ch if is_whitespace(ch) => continue,
                ch if is_symbol(ch) => Ok(self.continue_symbol(start)),
                ch if is_delimiter(ch) => Ok(self.emit(TokenTag::Delimiter, start, end)),
                ch if is_identifier_start(ch) => Ok(self.continue_identifier(start)),
                '"' => self.continue_string_literal(start),
                '\'' => self.continue_char_literal(start),
                '0' => self.continue_zero_number(start),
                ch if is_dec_digit(ch) => self.continue_dec_literal(start, false),
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
    pub fn new(file: &'file File) -> Lexer<'file> {
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

    /// Emit a token
    fn emit(&self, tag: TokenTag, start: ByteIndex, end: ByteIndex) -> Token<'file> {
        let slice = self.slice(start, end);
        let span = self.span(start, end);
        Token { tag, slice, span }
    }

    /// Return the next character in the source string
    fn lookahead(&self) -> Option<(ByteIndex, char)> {
        self.lookahead.map(|(i, ch)| (ByteIndex::from(i), ch))
    }

    /// Bump the current position in the source string by one character,
    /// returning the current character and byte position.
    fn advance(&mut self) -> Option<(ByteIndex, char)> {
        let current = self.lookahead();
        self.lookahead = self.chars.next();
        current
    }

    /// Bump the current position in the source string by one character,
    /// returning the current character and byte position, or returning an
    /// unexpected end of file error.
    fn expect_advance(&mut self) -> Result<(ByteIndex, char), Diagnostic<FileSpan>> {
        self.advance().ok_or_else(|| {
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
    fn take_while(&mut self, mut keep_going: impl FnMut(char) -> bool) -> ByteIndex {
        self.take_until(|ch| !keep_going(ch))
    }

    /// Consume characters until the predicate matches for the next character
    /// in the lookahead, then return the consumed slice and the end byte
    /// position.
    fn take_until(&mut self, mut terminate: impl FnMut(char) -> bool) -> ByteIndex {
        while let Some((end, ch)) = self.lookahead() {
            if terminate(ch) {
                return end;
            } else {
                self.advance();
            }
        }

        self.eof()
    }

    /// Consume a line comment
    fn continue_line_comment(&mut self, start: ByteIndex) -> Token<'file> {
        let end = self.take_until(|ch| ch == '\n');
        self.emit(TokenTag::LineComment, start, end)
    }

    /// Consume a doc comment
    fn continue_line_doc(&mut self, start: ByteIndex) -> Token<'file> {
        let end = self.take_until(|ch| ch == '\n');
        self.emit(TokenTag::LineDoc, start, end)
    }

    /// Consume a symbol
    fn continue_symbol(&mut self, start: ByteIndex) -> Token<'file> {
        let end = self.take_while(is_symbol);

        match self.slice(start, end) {
            symbol if symbol.starts_with("|||") => self.continue_line_doc(start),
            symbol if symbol.starts_with("--") => self.continue_line_comment(start),
            _ => self.emit(TokenTag::Symbol, start, end),
        }
    }

    /// Consume a identifier
    fn continue_identifier(&mut self, start: ByteIndex) -> Token<'file> {
        let end = self.take_while(is_identifier_continue);
        self.emit(TokenTag::Identifier, start, end)
    }

    /// Consume an escape code
    fn start_escape(&mut self) -> Result<(), Diagnostic<FileSpan>> {
        match self.expect_advance()? {
            (_, '\'') => Ok(()),
            (_, '\"') => Ok(()),
            (_, '\\') => Ok(()),
            (_, '/') => Ok(()),
            (_, 'n') => Ok(()),
            (_, 'r') => Ok(()),
            (_, 't') => Ok(()),
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
    ) -> Result<Token<'file>, Diagnostic<FileSpan>> {
        let mut end = start;

        while let Some((next, ch)) = self.advance() {
            end = next + ByteSize::from_char_len_utf8(ch);
            match ch {
                '\\' => {},
                '"' => return Ok(self.emit(TokenTag::StringLiteral, start, end)),
                _ => {},
            }
        }

        Err(Diagnostic::new_error("unterminated string literal")
            .with_label(Label::new_primary(self.span(start, end))))
    }

    /// Consume a character literal
    fn continue_char_literal(
        &mut self,
        start: ByteIndex,
    ) -> Result<Token<'file>, Diagnostic<FileSpan>> {
        match self.expect_advance()? {
            (_, '\\') => self.start_escape()?,
            (next, '\'') => {
                let end = next + ByteSize::from_char_len_utf8('\'');
                return Err(Diagnostic::new_error("empty character literal")
                    .with_label(Label::new_primary(self.span(start, end))));
            },
            (_, _) => {},
        };

        match self.expect_advance()? {
            (end, '\'') => Ok(self.emit(
                TokenTag::CharLiteral,
                start,
                end + ByteSize::from_char_len_utf8('\''),
            )),
            (next, ch) => Err({
                let end = next + ByteSize::from_char_len_utf8(ch);
                Diagnostic::new_error("unterminated character literal")
                    .with_label(Label::new_primary(self.span(start, end)))
            }),
        }
    }

    /// Consume some digits, separated by `_`, returning the number of digits consumed
    fn separated_digits(&mut self, is_digit: impl Fn(char) -> bool) -> (ByteIndex, usize) {
        let digits = &mut 0;
        let end = self.take_while(|ch| match ch {
            '_' => true,
            ch if is_digit(ch) => {
                *digits += 1;
                true
            },
            _ => false,
        });
        (end, *digits)
    }

    /// Consume a number starting with zero
    fn continue_zero_number(
        &mut self,
        start: ByteIndex,
    ) -> Result<Token<'file>, Diagnostic<FileSpan>> {
        match self.lookahead() {
            Some((_, 'b')) => {
                self.advance(); // skip 'b'
                self.continue_bin_literal(start)
            },
            Some((_, 'o')) => {
                self.advance(); // skip 'o'
                self.continue_oct_literal(start)
            },
            Some((_, 'x')) => {
                self.advance(); // skip 'x'
                self.continue_hex_literal(start)
            },
            _ => self.continue_dec_literal(start, true),
        }
    }

    /// Consume a binary literal token
    fn continue_bin_literal(
        &mut self,
        start: ByteIndex,
    ) -> Result<Token<'file>, Diagnostic<FileSpan>> {
        let (end, digits) = self.separated_digits(is_bin_digit);
        if digits == 0 {
            Err(
                Diagnostic::new_error("no valid digits found in binary literal")
                    .with_label(Label::new_primary(self.span(start, end))),
            )
        } else {
            Ok(self.emit(TokenTag::IntLiteral, start, end))
        }
    }

    /// Consume a octal literal token
    fn continue_oct_literal(
        &mut self,
        start: ByteIndex,
    ) -> Result<Token<'file>, Diagnostic<FileSpan>> {
        let (end, digits) = self.separated_digits(is_oct_digit);
        if digits == 0 {
            Err(
                Diagnostic::new_error("no valid digits found in octal literal")
                    .with_label(Label::new_primary(self.span(start, end))),
            )
        } else {
            Ok(self.emit(TokenTag::IntLiteral, start, end))
        }
    }

    /// Consume a hexadecimal literal token
    fn continue_hex_literal(
        &mut self,
        start: ByteIndex,
    ) -> Result<Token<'file>, Diagnostic<FileSpan>> {
        let (end, digits) = self.separated_digits(is_hex_digit);
        if digits == 0 {
            Err(
                Diagnostic::new_error("no valid digits found in hexadecimal literal")
                    .with_label(Label::new_primary(self.span(start, end))),
            )
        } else {
            Ok(self.emit(TokenTag::IntLiteral, start, end))
        }
    }

    /// Consume a decimal literal
    fn continue_dec_literal(
        &mut self,
        start: ByteIndex,
        has_zero_prefix: bool,
    ) -> Result<Token<'file>, Diagnostic<FileSpan>> {
        let (end, digits) = self.separated_digits(is_dec_digit);
        let digits = digits + if has_zero_prefix { 1 } else { 0 };
        if digits + 1 == 0 {
            return Err(
                Diagnostic::new_error("no valid digits found in decimal literal")
                    .with_label(Label::new_primary(self.span(start, end))),
            );
        }

        if let Some((_, '.')) = self.lookahead() {
            self.advance(); // skip '.'
            self.continue_float_literal(start)
        } else {
            Ok(self.emit(TokenTag::IntLiteral, start, end))
        }
    }

    /// Consume a float literal
    fn continue_float_literal(
        &mut self,
        start: ByteIndex,
    ) -> Result<Token<'file>, Diagnostic<FileSpan>> {
        // FIXME: Should not be able to start with `_`
        let (end, digits) = self.separated_digits(is_dec_digit);

        if digits == 0 {
            return Err(
                Diagnostic::new_error("no valid digits found after decimal place")
                    .with_label(Label::new_primary(self.span(start, end))),
            );
        }

        Ok(self.emit(TokenTag::FloatLiteral, start, end))
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
            "  ~~~~~~~~~~~~~~~~  " => (TokenTag::Identifier, "hello-hahaha8ABC"),
        };
    }

    #[test]
    fn comment() {
        test! {
            "       -- hello this is dog\n  ",
            "       ~~~~~~~~~~~~~~~~~~~~    " => (TokenTag::LineComment, "-- hello this is dog"),
        };
    }

    #[test]
    fn line_doc() {
        test! {
            "       ||| hello this is dog",
            "       ~~~~~~~~~~~~~~~~~~~~~" => (TokenTag::LineDoc, "||| hello this is dog"),
        };
    }

    #[test]
    fn string_literal() {
        test! {
            r#"  "a" "\t"  "#,
            r#"  ~~~       "# => (TokenTag::StringLiteral, "\"a\""),
            r#"      ~~~~  "# => (TokenTag::StringLiteral, "\"\\t\""),
        };
    }

    #[test]
    fn char_literal() {
        test! {
            r"  'a' '\t'  ",
            r"  ~~~       " => (TokenTag::CharLiteral, "'a'"),
            r"      ~~~~  " => (TokenTag::CharLiteral, "'\\t'"),
        };
    }

    #[test]
    fn bin_literal() {
        test! {
            "  0b010110  ",
            "  ~~~~~~~~  " => (TokenTag::IntLiteral, "0b010110"),
        };
    }

    #[test]
    fn oct_literal() {
        test! {
            "  0o12371  ",
            "  ~~~~~~~  " => (TokenTag::IntLiteral, "0o12371"),
        };
    }

    #[test]
    fn dec_literal() {
        test! {
            "  123 0 1 2345_65_32  ",
            "  ~~~                 " => (TokenTag::IntLiteral, "123"),
            "      ~               " => (TokenTag::IntLiteral, "0"),
            "        ~             " => (TokenTag::IntLiteral, "1"),
            "          ~~~~~~~~~~  " => (TokenTag::IntLiteral, "2345_65_32"),
        };
    }

    #[test]
    fn hex_literal() {
        test! {
            "  0x123AF  ",
            "  ~~~~~~~  " => (TokenTag::IntLiteral, "0x123AF"),
        };
    }

    #[test]
    fn float_literal() {
        test! {
            "  122.345  ",
            "  ~~~~~~~  " => (TokenTag::FloatLiteral, "122.345"),
        };
    }

    #[test]
    fn keywords() {
        test! {
            "  as case else if import in let record Record then Type where  ",
            "  ~~                                                              " => (TokenTag::Identifier, "as"),
            "     ~~~~                                                         " => (TokenTag::Identifier, "case"),
            "          ~~~~                                                    " => (TokenTag::Identifier, "else"),
            "               ~~                                                 " => (TokenTag::Identifier, "if"),
            "                  ~~~~~~                                          " => (TokenTag::Identifier, "import"),
            "                         ~~                                       " => (TokenTag::Identifier, "in"),
            "                            ~~~                                   " => (TokenTag::Identifier, "let"),
            "                                ~~~~~~                            " => (TokenTag::Identifier, "record"),
            "                                       ~~~~~~                     " => (TokenTag::Identifier, "Record"),
            "                                              ~~~~                " => (TokenTag::Identifier, "then"),
            "                                                   ~~~~           " => (TokenTag::Identifier, "Type"),
            "                                                        ~~~~~     " => (TokenTag::Identifier, "where"),
        };
    }

    #[test]
    fn symbols() {
        test! {
            r" \ ^ : , .. = -> => ? ; ",
            r" ~                      " => (TokenTag::Symbol, "\\"),
            r"   ~                    " => (TokenTag::Symbol, "^"),
            r"     ~                  " => (TokenTag::Symbol, ":"),
            r"       ~                " => (TokenTag::Symbol, ","),
            r"         ~~             " => (TokenTag::Symbol, ".."),
            r"            ~           " => (TokenTag::Symbol, "="),
            r"              ~~        " => (TokenTag::Symbol, "->"),
            r"                 ~~     " => (TokenTag::Symbol, "=>"),
            r"                    ~   " => (TokenTag::Symbol, "?"),
            r"                      ~ " => (TokenTag::Symbol, ";"),
        }
    }

    #[test]
    fn delimiters() {
        test! {
            " ( ) { } [ ] ",
            " ~           " => (TokenTag::Delimiter, "("),
            "   ~         " => (TokenTag::Delimiter, ")"),
            "     ~       " => (TokenTag::Delimiter, "{"),
            "       ~     " => (TokenTag::Delimiter, "}"),
            "         ~   " => (TokenTag::Delimiter, "["),
            "           ~ " => (TokenTag::Delimiter, "]"),
        }
    }
}
