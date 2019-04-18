use language_reporting::{Diagnostic, Label};
use mltt_concrete::SpannedString;
use mltt_span::{ByteIndex, ByteSize, File, FileSpan};
use std::str::Chars;

use crate::token::{DelimKind, Token, TokenKind};

/// The keywords used in the language.
pub const KEYWORDS: &[&str] = &[
    "case",
    "else",
    "if",
    "in",
    "let",
    "then",
    "Type",
    "Fun",
    "fun",
    "primitive",
    "Record",
    "record",
];

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
        '&' | '!' | ':' | '.' | '=' | '\\' | '/' | '>' | '<' | '-' | '|' | '+' | '*' | '^' => true,
        _ => false,
    }
}

fn is_identifier_start(ch: char) -> bool {
    match ch {
        'a'..='z' | 'A'..='Z' | '_' => true,
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
/// the parser.
pub struct Lexer<'file> {
    /// The file we are lexing.
    file: &'file File,
    /// An iterator of unicode characters to consume.
    chars: Chars<'file>,
    /// One character of lookahead, making this lexer LR(1).
    peeked: Option<char>,
    /// The start of the next token to be emitted.
    token_start: ByteIndex,
    /// The end of the next token to be emitted.
    token_end: ByteIndex,
    /// The diagnostics that we have accumulated during lexing.
    diagnostics: Vec<Diagnostic<FileSpan>>,
}

impl<'file> Lexer<'file> {
    /// Create a new lexer from the source file.
    pub fn new(file: &'file File) -> Lexer<'file> {
        let mut chars = file.contents().chars();
        let peeked = chars.next();

        Lexer {
            file,
            chars,
            peeked,
            token_start: ByteIndex::from(0),
            token_end: ByteIndex::from(0),
            diagnostics: Vec::new(),
        }
    }

    /// The diagnostic that were emitted during lexing.
    pub fn diagnostics(&self) -> &[Diagnostic<FileSpan>] {
        &self.diagnostics
    }

    /// Take the diagnostics from the lexer.
    pub fn take_diagnostics(&mut self) -> Vec<Diagnostic<FileSpan>> {
        std::mem::replace(&mut self.diagnostics, Vec::new())
    }

    /// Record a diagnostic.
    fn add_diagnostic(&mut self, diagnostic: Diagnostic<FileSpan>) {
        log::debug!("diagnostic added: {:?}", diagnostic.message);
        self.diagnostics.push(diagnostic);
    }

    /// Returns a span in the source file.
    fn span(&self, start: ByteIndex, end: ByteIndex) -> FileSpan {
        FileSpan::new(self.file.id(), start, end)
    }

    /// Returns the span of the current token in the source file.
    fn token_span(&self) -> FileSpan {
        self.span(self.token_start, self.token_end)
    }

    /// Returns the string slice of the current token.
    fn token_slice(&self) -> &'file str {
        &self.file.contents()[self.token_start.to_usize()..self.token_end.to_usize()]
    }

    /// Returns the source of the current token.
    fn token_src(&self) -> SpannedString<'file> {
        SpannedString {
            source: self.file.id(),
            slice: self.token_slice(),
            start: self.token_start,
        }
    }

    /// Returns the span of the end of the file.
    fn eof_span(&self) -> FileSpan {
        let end = self.file.span().end();
        self.span(end, end)
    }

    /// Emit a token and reset the start position, ready for the next token.
    fn emit(&mut self, kind: TokenKind) -> Token<'file> {
        let src = self.token_src();
        self.token_start = self.token_end;
        Token { kind, src }
    }

    /// Peek at the current lookahead character.
    fn peek(&self) -> Option<char> {
        self.peeked
    }

    /// Consume the current character and load the next one. Return the old token.
    fn advance(&mut self) -> Option<char> {
        let current = std::mem::replace(&mut self.peeked, self.chars.next());
        self.token_end += current.map_or(ByteSize::from(0), ByteSize::from_char_len_utf8);
        current
    }

    /// Bump the current position in the source string by one character,
    /// returning the current character or an unexpected end of file error.
    fn expect_advance(&mut self) -> Result<char, Diagnostic<FileSpan>> {
        self.advance().ok_or_else(|| {
            Diagnostic::new_error("unexpected end of file")
                .with_label(Label::new_primary(self.eof_span()))
        })
    }

    /// Skip characters while the predicate matches the lookahead character.
    fn skip_while(&mut self, mut keep_going: impl FnMut(char) -> bool) {
        while self.peek().map_or(false, |ch| keep_going(ch)) {
            self.advance();
        }
    }

    /// Skip by one character if the predicate matches the lookahead.
    fn skip_if(&mut self, predicate: impl Fn(char) -> bool) -> bool {
        match self.peek() {
            Some(ch) if predicate(ch) => {
                self.advance();
                true
            },
            Some(_) | None => false,
        }
    }

    /// Consume a token, returning its tag or none on end of file.
    fn consume_token(&mut self) -> Option<TokenKind> {
        self.advance().map(|ch| match ch {
            ',' => TokenKind::Comma,
            ';' => TokenKind::Semicolon,
            '?' => TokenKind::Question,
            '(' => TokenKind::Open(DelimKind::Paren),
            ')' => TokenKind::Close(DelimKind::Paren),
            '{' => TokenKind::Open(DelimKind::Brace),
            '}' => TokenKind::Close(DelimKind::Brace),
            '[' => TokenKind::Open(DelimKind::Bracket),
            ']' => TokenKind::Close(DelimKind::Bracket),
            '"' => self.consume_string_literal(),
            '\'' => self.consume_char_literal(),
            '0' => self.consume_zero_number(),
            ch if is_dec_digit(ch) => self.consume_dec_literal(),
            ch if is_whitespace(ch) => self.consume_whitespace(),
            ch if is_symbol(ch) => self.consume_symbol(),
            ch if is_identifier_start(ch) => self.consume_identifier(),
            ch => {
                self.add_diagnostic(
                    Diagnostic::new_error(format!("unexpected character `{}`", ch))
                        .with_label(Label::new_primary(self.token_span())),
                );
                TokenKind::Error
            },
        })
    }

    /// Consume a line comment.
    fn consume_line_comment(&mut self) -> TokenKind {
        self.skip_while(|ch| ch != '\n');
        TokenKind::LineComment
    }

    /// Consume a doc comment.
    fn consume_line_doc(&mut self) -> TokenKind {
        self.skip_while(|ch| ch != '\n');
        TokenKind::LineDoc
    }

    /// Consume some whitespace.
    fn consume_whitespace(&mut self) -> TokenKind {
        self.skip_while(is_whitespace);
        TokenKind::Whitespace
    }

    /// Consume a symbol.
    fn consume_symbol(&mut self) -> TokenKind {
        self.skip_while(is_symbol);
        match self.token_slice() {
            "^" => TokenKind::Caret,
            ":" => TokenKind::Colon,
            "," => TokenKind::Comma,
            "." => TokenKind::Dot,
            "=" => TokenKind::Equals,
            "->" => TokenKind::RArrow,
            "=>" => TokenKind::RFatArrow,
            "-" => self.consume_neg_number(),
            slice if slice.starts_with("|||") => self.consume_line_doc(),
            slice if slice.starts_with("--") => self.consume_line_comment(),
            _ => TokenKind::Symbol,
        }
    }

    /// Consume a identifier.
    fn consume_identifier(&mut self) -> TokenKind {
        self.skip_while(is_identifier_continue);
        if KEYWORDS.contains(&self.token_slice()) {
            TokenKind::Keyword
        } else {
            TokenKind::Identifier
        }
    }

    /// Skip an ASCII character code.
    fn skip_ascii_char_code(&mut self) -> Result<(), Diagnostic<FileSpan>> {
        if !is_oct_digit(self.expect_advance()?) {
            return Err(Diagnostic::new_error("invalid ASCII character code")
                .with_label(Label::new_primary(self.token_span())));
        }
        if !is_hex_digit(self.expect_advance()?) {
            return Err(Diagnostic::new_error("invalid ASCII character code")
                .with_label(Label::new_primary(self.token_span())));
        }
        Ok(())
    }

    /// Skip a unicode character code.
    fn skip_unicode_char_code(&mut self) -> Result<(), Diagnostic<FileSpan>> {
        if self.expect_advance()? != '{' {
            return Err(Diagnostic::new_error("invalid unicode character code")
                .with_label(Label::new_primary(self.token_span())));
        }

        let mut digits = 0;
        loop {
            match self.expect_advance()? {
                '}' => break,
                '_' => continue,
                ch if is_hex_digit(ch) => {
                    digits += 1;
                    continue;
                },
                _ => {
                    return Err(Diagnostic::new_error("invalid unicode character code")
                        .with_label(Label::new_primary(self.token_span())))
                },
            }
        }

        match digits {
            1..=6 => Ok(()),
            _ => Err(Diagnostic::new_error("expected 1 to 6 hexadecimal digits")
                .with_label(Label::new_primary(self.token_span()))),
        }
    }

    /// Skip an escape.
    fn skip_escape(&mut self) -> Result<(), Diagnostic<FileSpan>> {
        match self.expect_advance()? {
            '\'' | '\"' | '\\' | 'n' | 'r' | 't' | '0' => Ok(()),
            'x' => self.skip_ascii_char_code(),
            'u' => self.skip_unicode_char_code(),
            ch => Err(
                Diagnostic::new_error(format!("unknown escape code `\\{}`", ch))
                    .with_label(Label::new_primary(self.token_span())),
            ),
        }
    }

    /// Consume a string literal.
    fn consume_string_literal(&mut self) -> TokenKind {
        let mut is_escape_error = false;
        while let Some(ch) = self.advance() {
            match ch {
                '\\' => {
                    if let Err(error) = self.skip_escape() {
                        self.add_diagnostic(error);
                        is_escape_error = true;
                    }
                },
                '"' if is_escape_error => return TokenKind::Error,
                '"' => return TokenKind::StringLiteral,
                _ => {},
            }
        }
        self.add_diagnostic(
            Diagnostic::new_error("unterminated string literal")
                .with_label(Label::new_primary(self.token_span())),
        );
        TokenKind::Error
    }

    /// Consume a character literal.
    fn consume_char_literal(&mut self) -> TokenKind {
        let mut is_escape_error = false;
        let mut codepoints = 0;
        while let Some(ch) = self.advance() {
            match ch {
                '\\' => {
                    if let Err(error) = self.skip_escape() {
                        self.add_diagnostic(error);
                        is_escape_error = true;
                    }
                },
                '\'' if is_escape_error => return TokenKind::Error,
                '\'' if codepoints == 1 => return TokenKind::CharLiteral,
                '\'' => {
                    self.add_diagnostic(
                        Diagnostic::new_error(
                            "character literals must contain exactly one codepoint",
                        )
                        .with_label(Label::new_primary(self.token_span())),
                    );
                    return TokenKind::Error;
                },
                _ => {},
            }
            codepoints += 1;
        }
        self.add_diagnostic(
            Diagnostic::new_error("unterminated character literal")
                .with_label(Label::new_primary(self.token_span())),
        );
        TokenKind::Error
    }

    /// Skip some digits, separated by `_`, returning the number of digits consumed.
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

    /// Consume a number starting with a negative sign.
    fn consume_neg_number(&mut self) -> TokenKind {
        match self.expect_advance() {
            Ok('0') => self.consume_zero_number(),
            Ok(ch) if is_dec_digit(ch) => self.consume_dec_literal(),
            Ok(ch) => {
                self.add_diagnostic(
                    Diagnostic::new_error(format!("unexpected character `{}`", ch))
                        .with_label(Label::new_primary(self.token_span())),
                );
                TokenKind::Error
            },
            Err(err) => {
                self.add_diagnostic(err);
                TokenKind::Error
            },
        }
    }

    /// Consume a number starting with zero.
    fn consume_zero_number(&mut self) -> TokenKind {
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

    /// Consume an integer literal that uses a specific radix.
    fn consume_radix_literal(
        &mut self,
        radix_name: &str,
        is_digit: impl Fn(char) -> bool,
    ) -> TokenKind {
        if self.skip_separated_digits(is_digit) == 0 {
            self.add_diagnostic(
                Diagnostic::new_error(format!("no valid digits found in {} literal", radix_name))
                    .with_label(Label::new_primary(self.token_span())),
            );
            TokenKind::Error
        } else {
            TokenKind::IntLiteral
        }
    }

    /// Consume float exponents, returning `true` if an exponent was found.
    fn skip_float_exponent(&mut self) -> Result<bool, Diagnostic<FileSpan>> {
        if self.skip_if(|ch| ch == 'e' || ch == 'E') {
            self.skip_if(|ch| ch == '-' || ch == '+');
            if self.skip_separated_digits(is_dec_digit) == 0 {
                Err(Diagnostic::new_error("no valid digits found in exponent")
                    .with_label(Label::new_primary(self.token_span())))
            } else {
                Ok(true)
            }
        } else {
            Ok(false)
        }
    }

    /// Consume a decimal literal.
    fn consume_dec_literal(&mut self) -> TokenKind {
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
                match self.skip_float_exponent() {
                    Ok(_) => TokenKind::FloatLiteral,
                    Err(error) => {
                        self.add_diagnostic(error);
                        TokenKind::Error
                    },
                }
            } else {
                match self.skip_float_exponent() {
                    Ok(true) => TokenKind::FloatLiteral,
                    Ok(false) => {
                        self.add_diagnostic(
                            Diagnostic::new_error(
                                "expected a digit or exponent after the decimal place",
                            )
                            .with_label(Label::new_primary(self.token_span())),
                        );
                        TokenKind::Error
                    },
                    Err(error) => {
                        self.add_diagnostic(error);
                        TokenKind::Error
                    },
                }
            }
        } else {
            match self.skip_float_exponent() {
                Ok(true) => TokenKind::FloatLiteral,
                Ok(false) => TokenKind::IntLiteral,
                Err(error) => {
                    self.add_diagnostic(error);
                    TokenKind::Error
                },
            }
        }
    }
}

impl<'file> Iterator for Lexer<'file> {
    type Item = Token<'file>;

    fn next(&mut self) -> Option<Token<'file>> {
        let consumed = self.consume_token().map(|tag| self.emit(tag));
        match &consumed {
            None => log::debug!("eof"),
            Some(token) => log::debug!("emit {:?}", token),
        }
        consumed
    }
}
