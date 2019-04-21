use mltt_concrete::SpannedString;
use mltt_parse::lexer::Lexer;
use mltt_parse::token::{DelimKind, Token, TokenKind};
use mltt_span::{ByteIndex, Files};
use pretty_assertions::assert_eq;

/// A handy macro to give us a nice syntax for declaring test cases
///
/// This was inspired by the tests in the LALRPOP lexer
macro_rules! test {
    ($src:expr, $($span:expr => $token_kind:expr,)*) => {{
        let _ = pretty_env_logger::try_init();

        let mut files = Files::new();
        let src = $src;
        let file_id = files.add("test", src);
        let lexed_tokens: Vec<_> = Lexer::new(&files[file_id])
            .map(|result| result)
            .collect();
        let expected_tokens = vec![$({
            let start = $span.find("~").unwrap();
            let end = $span.rfind("~").unwrap() + 1;
            let token_src = SpannedString::new(ByteIndex::from(start), &src[start..end]);
            Token { kind: $token_kind, src: token_src }
        }),*];

        assert_eq!(lexed_tokens, expected_tokens);
    }};
}

#[test]
fn data() {
    test! {
        "  hello-hahaha8ABC  ",
        "~~                  " => TokenKind::Whitespace,
        "  ~~~~~~~~~~~~~~~~  " => TokenKind::Identifier,
        "                  ~~" => TokenKind::Whitespace,
    };
}

#[test]
fn comment() {
    test! {
        "       -- hello this is dog\n  ",
        "~~~~~~~                        " => TokenKind::Whitespace,
        "       ~~~~~~~~~~~~~~~~~~~~    " => TokenKind::LineComment,
        "                           ~~~ " => TokenKind::Whitespace,
    };
}

#[test]
fn line_doc() {
    test! {
        "       ||| hello this is dog",
        "~~~~~~~                     " => TokenKind::Whitespace,
        "       ~~~~~~~~~~~~~~~~~~~~~" => TokenKind::LineDoc,
    };
}

#[test]
fn string_literal() {
    test! {
        r#"  "a" "\t" "hello \x3f \x7F \u{7fff} \u{7FFF}"  "#,
        r#"~~                                              "# => TokenKind::Whitespace,
        r#"  ~~~                                           "# => TokenKind::StringLiteral,
        r#"     ~                                          "# => TokenKind::Whitespace,
        r#"      ~~~~                                      "# => TokenKind::StringLiteral,
        r#"          ~                                     "# => TokenKind::Whitespace,
        r#"           ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~  "# => TokenKind::StringLiteral,
        r#"                                              ~~"# => TokenKind::Whitespace,
    };
}

#[test]
fn char_literal() {
    test! {
        r"  'a' '\t'  ",
        r"~~          " => TokenKind::Whitespace,
        r"  ~~~       " => TokenKind::CharLiteral,
        r"     ~      " => TokenKind::Whitespace,
        r"      ~~~~  " => TokenKind::CharLiteral,
        r"          ~~" => TokenKind::Whitespace,
    };
}

#[test]
fn bin_literal() {
    test! {
        "  0b010110  -0b010110  ",
        "~~                     " => TokenKind::Whitespace,
        "  ~~~~~~~~             " => TokenKind::IntLiteral,
        "          ~~           " => TokenKind::Whitespace,
        "            ~~~~~~~~~  " => TokenKind::IntLiteral,
        "                     ~~" => TokenKind::Whitespace,
    };
}

#[test]
fn oct_literal() {
    test! {
        "  0o12371  -0o12371  ",
        "~~                   " => TokenKind::Whitespace,
        "  ~~~~~~~            " => TokenKind::IntLiteral,
        "         ~~          " => TokenKind::Whitespace,
        "           ~~~~~~~~  " => TokenKind::IntLiteral,
        "                   ~~" => TokenKind::Whitespace,
    };
}

#[test]
fn dec_literal() {
    test! {
        "  123 0 1 2345_65_32 -2345_65_32  ",
        "~~                                " => TokenKind::Whitespace,
        "  ~~~                             " => TokenKind::IntLiteral,
        "     ~                            " => TokenKind::Whitespace,
        "      ~                           " => TokenKind::IntLiteral,
        "       ~                          " => TokenKind::Whitespace,
        "        ~                         " => TokenKind::IntLiteral,
        "         ~                        " => TokenKind::Whitespace,
        "          ~~~~~~~~~~              " => TokenKind::IntLiteral,
        "                    ~             " => TokenKind::Whitespace,
        "                     ~~~~~~~~~~~  " => TokenKind::IntLiteral,
        "                                ~~" => TokenKind::Whitespace,
    };
}

#[test]
fn hex_literal() {
    test! {
        "  0x123AF  -0x123AF  ",
        "~~                   " => TokenKind::Whitespace,
        "  ~~~~~~~            " => TokenKind::IntLiteral,
        "         ~~          " => TokenKind::Whitespace,
        "           ~~~~~~~~  " => TokenKind::IntLiteral,
        "                   ~~" => TokenKind::Whitespace,
    };
}

#[test]
fn float_literal() {
    test! {
        "  122.345 1.0 0e1 0E2 0.3e-2_3 0_1.0e_1_ -1.0  ",
        "~~                                             " => TokenKind::Whitespace,
        "  ~~~~~~~                                      " => TokenKind::FloatLiteral,
        "         ~                                     " => TokenKind::Whitespace,
        "          ~~~                                  " => TokenKind::FloatLiteral,
        "             ~                                 " => TokenKind::Whitespace,
        "              ~~~                              " => TokenKind::FloatLiteral,
        "                 ~                             " => TokenKind::Whitespace,
        "                  ~~~                          " => TokenKind::FloatLiteral,
        "                     ~                         " => TokenKind::Whitespace,
        "                      ~~~~~~~~                 " => TokenKind::FloatLiteral,
        "                              ~                " => TokenKind::Whitespace,
        "                               ~~~~~~~~~       " => TokenKind::FloatLiteral,
        "                                        ~      " => TokenKind::Whitespace,
        "                                         ~~~~  " => TokenKind::FloatLiteral,
        "                                             ~~" => TokenKind::Whitespace,
    };
}

#[test]
fn keywords() {
    test! {
        "  as case else if import in let record Record then Type where  ",
        "~~                                                             " => TokenKind::Whitespace,
        "  ~~                                                           " => TokenKind::Identifier,
        "    ~                                                          " => TokenKind::Whitespace,
        "     ~~~~                                                      " => TokenKind::Keyword,
        "         ~                                                     " => TokenKind::Whitespace,
        "          ~~~~                                                 " => TokenKind::Keyword,
        "              ~                                                " => TokenKind::Whitespace,
        "               ~~                                              " => TokenKind::Keyword,
        "                 ~                                             " => TokenKind::Whitespace,
        "                  ~~~~~~                                       " => TokenKind::Identifier,
        "                        ~                                      " => TokenKind::Whitespace,
        "                         ~~                                    " => TokenKind::Keyword,
        "                           ~                                   " => TokenKind::Whitespace,
        "                            ~~~                                " => TokenKind::Keyword,
        "                               ~                               " => TokenKind::Whitespace,
        "                                ~~~~~~                         " => TokenKind::Keyword,
        "                                      ~                        " => TokenKind::Whitespace,
        "                                       ~~~~~~                  " => TokenKind::Keyword,
        "                                             ~                 " => TokenKind::Whitespace,
        "                                              ~~~~             " => TokenKind::Keyword,
        "                                                  ~            " => TokenKind::Whitespace,
        "                                                   ~~~~        " => TokenKind::Keyword,
        "                                                       ~       " => TokenKind::Whitespace,
        "                                                        ~~~~~  " => TokenKind::Identifier,
        "                                                             ~~" => TokenKind::Whitespace,
    };
}

#[test]
fn symbols() {
    test! {
        r" \ ^ : , .. = -> => ? ; ",
        r"~                       " => TokenKind::Whitespace,
        r" ~                      " => TokenKind::Symbol,
        r"  ~                     " => TokenKind::Whitespace,
        r"   ~                    " => TokenKind::Caret,
        r"    ~                   " => TokenKind::Whitespace,
        r"     ~                  " => TokenKind::Colon,
        r"      ~                 " => TokenKind::Whitespace,
        r"       ~                " => TokenKind::Comma,
        r"        ~               " => TokenKind::Whitespace,
        r"         ~~             " => TokenKind::Symbol,
        r"           ~            " => TokenKind::Whitespace,
        r"            ~           " => TokenKind::Equals,
        r"             ~          " => TokenKind::Whitespace,
        r"              ~~        " => TokenKind::RArrow,
        r"                ~       " => TokenKind::Whitespace,
        r"                 ~~     " => TokenKind::RFatArrow,
        r"                   ~    " => TokenKind::Whitespace,
        r"                    ~   " => TokenKind::Question,
        r"                     ~  " => TokenKind::Whitespace,
        r"                      ~ " => TokenKind::Semicolon,
        r"                       ~" => TokenKind::Whitespace,
    }
}

#[test]
fn delimiters() {
    test! {
        " ( ) { } [ ] ",
        "~            " => TokenKind::Whitespace,
        " ~           " => TokenKind::Open(DelimKind::Paren),
        "  ~          " => TokenKind::Whitespace,
        "   ~         " => TokenKind::Close(DelimKind::Paren),
        "    ~        " => TokenKind::Whitespace,
        "     ~       " => TokenKind::Open(DelimKind::Brace),
        "      ~      " => TokenKind::Whitespace,
        "       ~     " => TokenKind::Close(DelimKind::Brace),
        "        ~    " => TokenKind::Whitespace,
        "         ~   " => TokenKind::Open(DelimKind::Bracket),
        "          ~  " => TokenKind::Whitespace,
        "           ~ " => TokenKind::Close(DelimKind::Bracket),
        "            ~" => TokenKind::Whitespace,
    }
}
