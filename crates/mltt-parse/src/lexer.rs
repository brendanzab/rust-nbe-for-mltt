use language_reporting::{Diagnostic, Label};
use mltt_span::{ByteIndex, ByteSize, File, FileSpan};
use std::str::CharIndices;

fn is_symbol(ch: char) -> bool {
    match ch {
        '&' | '!' | ':' | ',' | '.' | '=' | '/' | '>' | '<' | '-' | '|' | '+' | ';' | '*' | '^'
        | '?' => true,
        _ => false,
    }
}

fn is_identifier_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_' || ch == '-'
}

fn is_identifier_continue(ch: char) -> bool {
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

/// A token in the source file, to be emitted by the `Lexer`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token<'file> {
    /// The token tag
    tag: TokenTag,
    /// The slice of source code that produced the token
    slice: &'file str,
    /// The span in the source code
    span: FileSpan,
}

/// A tag that makes it easier to remember what type of token this is
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenTag {
    // Data
    Identifier,
    LineComment,
    LineDoc,
    StringLiteral,
    CharLiteral,
    BinIntLiteral,
    OctIntLiteral,
    DecIntLiteral,
    HexIntLiteral,
    DecFloatLiteral,

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
        while let Some((start, ch)) = self.bump() {
            let end = start + ByteSize::from_char_len_utf8(ch);

            return Some(match ch {
                ch if is_symbol(ch) => self.continue_symbol(start),
                '\\' => Ok(self.emit(TokenTag::BSlash, start, end)),
                '(' => Ok(self.emit(TokenTag::LParen, start, end)),
                ')' => Ok(self.emit(TokenTag::RParen, start, end)),
                '{' => Ok(self.emit(TokenTag::LBrace, start, end)),
                '}' => Ok(self.emit(TokenTag::RBrace, start, end)),
                '[' => Ok(self.emit(TokenTag::LBracket, start, end)),
                ']' => Ok(self.emit(TokenTag::RBracket, start, end)),
                '"' => self.continue_string_literal(start),
                '\'' => self.continue_char_literal(start),
                '0' => self.continue_zero_number(start),
                ch if is_dec_digit(ch) => self.continue_dec_literal(start),
                ch if is_identifier_start(ch) => Ok(self.continue_identifier(start)),
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
    fn take_while<F>(&mut self, mut keep_going: F) -> ByteIndex
    where
        F: FnMut(char) -> bool,
    {
        self.take_until(|ch| !keep_going(ch))
    }

    /// Consume characters until the predicate matches for the next character
    /// in the lookahead, then return the consumed slice and the end byte
    /// position.
    fn take_until<F>(&mut self, mut terminate: F) -> ByteIndex
    where
        F: FnMut(char) -> bool,
    {
        while let Some((end, ch)) = self.lookahead() {
            if terminate(ch) {
                return end;
            } else {
                self.bump();
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
    fn continue_symbol(&mut self, start: ByteIndex) -> Result<Token<'file>, Diagnostic<FileSpan>> {
        let end = self.take_while(is_symbol);
        let symbol = self.slice(start, end);

        match symbol {
            ":" => Ok(self.emit(TokenTag::Colon, start, end)),
            "^" => Ok(self.emit(TokenTag::Caret, start, end)),
            "," => Ok(self.emit(TokenTag::Comma, start, end)),
            "." => Ok(self.emit(TokenTag::Dot, start, end)),
            ".." => Ok(self.emit(TokenTag::DotDot, start, end)),
            "=" => Ok(self.emit(TokenTag::Equal, start, end)),
            "->" => Ok(self.emit(TokenTag::LArrow, start, end)),
            "=>" => Ok(self.emit(TokenTag::LFatArrow, start, end)),
            "?" => Ok(self.emit(TokenTag::Question, start, end)),
            ";" => Ok(self.emit(TokenTag::Semi, start, end)),
            symbol if symbol.starts_with("|||") => Ok(self.continue_line_doc(start)),
            symbol if symbol.starts_with("--") => Ok(self.continue_line_comment(start)),
            _ => Err(
                Diagnostic::new_error(format!("unexpected symbol `{}`", symbol))
                    .with_label(Label::new_primary(self.span(start, end))),
            ),
        }
    }

    /// Consume a identifier
    fn continue_identifier(&mut self, start: ByteIndex) -> Token<'file> {
        let end = self.take_while(is_identifier_continue);
        let identifier = self.slice(start, end);

        let token_tag = match identifier {
            "as" => TokenTag::As,
            "case" => TokenTag::Case,
            "else" => TokenTag::Else,
            "if" => TokenTag::If,
            "import" => TokenTag::Import,
            "in" => TokenTag::In,
            "let" => TokenTag::Let,
            "record" => TokenTag::Record,
            "Record" => TokenTag::RecordType,
            "then" => TokenTag::Then,
            "Type" => TokenTag::Type,
            "where" => TokenTag::Where,
            _ => TokenTag::Identifier,
        };

        self.emit(token_tag, start, end)
    }

    /// Consume an escape code
    fn start_escape(&mut self) -> Result<(), Diagnostic<FileSpan>> {
        match self.expect_bump()? {
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

        while let Some((next, ch)) = self.bump() {
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
        match self.expect_bump()? {
            (_, '\\') => self.start_escape()?,
            (next, '\'') => {
                let end = next + ByteSize::from_char_len_utf8('\'');
                return Err(Diagnostic::new_error("empty character literal")
                    .with_label(Label::new_primary(self.span(start, end))));
            },
            (_, _) => {},
        };

        match self.expect_bump()? {
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

    /// Consume a number starting with zero
    fn continue_zero_number(
        &mut self,
        start: ByteIndex,
    ) -> Result<Token<'file>, Diagnostic<FileSpan>> {
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
    ) -> Result<Token<'file>, Diagnostic<FileSpan>> {
        self.bump(); // skip 'b'
        let end = self.take_while(is_bin_digit);
        if end - start <= ByteSize::from(0) {
            Err(Diagnostic::new_error("unterminated binary literal")
                .with_label(Label::new_primary(self.span(start, end))))
        } else {
            Ok(self.emit(TokenTag::BinIntLiteral, start, end))
        }
    }

    /// Consume a octal literal token
    fn continue_oct_literal(
        &mut self,
        start: ByteIndex,
    ) -> Result<Token<'file>, Diagnostic<FileSpan>> {
        self.bump(); // skip 'o'
        let end = self.take_while(is_oct_digit);
        if end - start <= ByteSize::from(0) {
            Err(Diagnostic::new_error("unterminated octal literal")
                .with_label(Label::new_primary(self.span(start, end))))
        } else {
            Ok(self.emit(TokenTag::OctIntLiteral, start, end))
        }
    }

    /// Consume a decimal literal
    fn continue_dec_literal(
        &mut self,
        start: ByteIndex,
    ) -> Result<Token<'file>, Diagnostic<FileSpan>> {
        let end = self.take_while(is_dec_digit);

        if let Some((_, '.')) = self.lookahead() {
            self.bump(); // skip '.'
            let end = self.take_while(is_dec_digit);

            Ok(self.emit(TokenTag::DecFloatLiteral, start, end))
        } else {
            Ok(self.emit(TokenTag::DecIntLiteral, start, end))
        }
    }

    /// Consume a hexadecimal literal token
    fn continue_hex_literal(
        &mut self,
        start: ByteIndex,
    ) -> Result<Token<'file>, Diagnostic<FileSpan>> {
        self.bump(); // skip 'x'
        let end = self.take_while(is_hex_digit);
        if end - start <= ByteSize::from(0) {
            Err(Diagnostic::new_error("unterminated hexadecimal literal")
                .with_label(Label::new_primary(self.span(start, end))))
        } else {
            Ok(self.emit(TokenTag::HexIntLiteral, start, end))
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
            "  ~~~~~~~~  " => (TokenTag::BinIntLiteral, "0b010110"),
        };
    }

    #[test]
    fn oct_literal() {
        test! {
            "  0o12371  ",
            "  ~~~~~~~  " => (TokenTag::OctIntLiteral, "0o12371"),
        };
    }

    #[test]
    fn dec_literal() {
        test! {
            "  123 0  ",
            "  ~~~    " => (TokenTag::DecIntLiteral, "123"),
            "      ~  " => (TokenTag::DecIntLiteral, "0"),
        };
    }

    #[test]
    fn hex_literal() {
        test! {
            "  0x123AF  ",
            "  ~~~~~~~  " => (TokenTag::HexIntLiteral, "0x123AF"),
        };
    }

    #[test]
    fn float_literal() {
        test! {
            "  122.345  ",
            "  ~~~~~~~  " => (TokenTag::DecFloatLiteral, "122.345"),
        };
    }

    #[test]
    fn keywords() {
        test! {
            "  as case else if import in let record Record then Type where  ",
            "  ~~                                                              " => (TokenTag::As, "as"),
            "     ~~~~                                                         " => (TokenTag::Case, "case"),
            "          ~~~~                                                    " => (TokenTag::Else, "else"),
            "               ~~                                                 " => (TokenTag::If, "if"),
            "                  ~~~~~~                                          " => (TokenTag::Import, "import"),
            "                         ~~                                       " => (TokenTag::In, "in"),
            "                            ~~~                                   " => (TokenTag::Let, "let"),
            "                                ~~~~~~                            " => (TokenTag::Record, "record"),
            "                                       ~~~~~~                     " => (TokenTag::RecordType, "Record"),
            "                                              ~~~~                " => (TokenTag::Then, "then"),
            "                                                   ~~~~           " => (TokenTag::Type, "Type"),
            "                                                        ~~~~~     " => (TokenTag::Where, "where"),
        };
    }

    #[test]
    fn symbols() {
        test! {
            r" \ ^ : , .. = -> => ? ; ",
            r" ~                      " => (TokenTag::BSlash, "\\"),
            r"   ~                    " => (TokenTag::Caret, "^"),
            r"     ~                  " => (TokenTag::Colon, ":"),
            r"       ~                " => (TokenTag::Comma, ","),
            r"         ~~             " => (TokenTag::DotDot, ".."),
            r"            ~           " => (TokenTag::Equal, "="),
            r"              ~~        " => (TokenTag::LArrow, "->"),
            r"                 ~~     " => (TokenTag::LFatArrow, "=>"),
            r"                    ~   " => (TokenTag::Question, "?"),
            r"                      ~ " => (TokenTag::Semi, ";"),
        }
    }

    #[test]
    fn delimiters() {
        test! {
            " ( ) { } [ ] ",
            " ~           " => (TokenTag::LParen, "("),
            "   ~         " => (TokenTag::RParen, ")"),
            "     ~       " => (TokenTag::LBrace, "{"),
            "       ~     " => (TokenTag::RBrace, "}"),
            "         ~   " => (TokenTag::LBracket, "["),
            "           ~ " => (TokenTag::RBracket, "]"),
        }
    }
}
