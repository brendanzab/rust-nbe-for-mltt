use mltt_parse::lexer::Lexer;
use mltt_parse::token::{DelimKind, Token, TokenKind};
use mltt_span::{ByteIndex, ByteSize, FileSpan, Files};
use pretty_assertions::assert_eq;

/// A handy macro to give us a nice syntax for declaring test cases
///
/// This was inspired by the tests in the LALRPOP lexer
macro_rules! test {
    ($src:expr, $($span:expr => $token:expr,)*) => {{
        let _ = pretty_env_logger::try_init();

        let mut files = Files::new();
        let file_id = files.add("test", $src);
        let lexed_tokens: Vec<_> = Lexer::new(&files[file_id])
            .map(|result| result)
            .collect();
        let expected_tokens = vec![$({
            let (kind, slice) = $token;
            let start = ByteIndex::from($span.find("~").unwrap());
            let end = ByteIndex::from($span.rfind("~").unwrap()) + ByteSize::from(1);
            let span = FileSpan::new(file_id, start, end);
            Token { kind, slice, span }
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
        r#"  "a" "\t" "hello \x3f \x7F \u{7fff} \u{7FFF}"  "#,
        r#"~~                                              "# => (TokenKind::Whitespace, "  "),
        r#"  ~~~                                           "# => (TokenKind::StringLiteral, r#""a""#),
        r#"     ~                                          "# => (TokenKind::Whitespace, " "),
        r#"      ~~~~                                      "# => (TokenKind::StringLiteral, r#""\t""#),
        r#"          ~                                     "# => (TokenKind::Whitespace, " "),
        r#"           ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~  "# => (TokenKind::StringLiteral, r#""hello \x3f \x7F \u{7fff} \u{7FFF}""#),
        r#"                                              ~~"# => (TokenKind::Whitespace, "  "),
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
        "  122.345 1.0 0e1 0E2 0.3e-2_3 0_1.0e_1_  ",
        "~~                                        " => (TokenKind::Whitespace, "  "),
        "  ~~~~~~~                                 " => (TokenKind::FloatLiteral, "122.345"),
        "         ~                                " => (TokenKind::Whitespace, " "),
        "          ~~~                             " => (TokenKind::FloatLiteral, "1.0"),
        "             ~                            " => (TokenKind::Whitespace, " "),
        "              ~~~                         " => (TokenKind::FloatLiteral, "0e1"),
        "                 ~                        " => (TokenKind::Whitespace, " "),
        "                  ~~~                     " => (TokenKind::FloatLiteral, "0E2"),
        "                     ~                    " => (TokenKind::Whitespace, " "),
        "                      ~~~~~~~~            " => (TokenKind::FloatLiteral, "0.3e-2_3"),
        "                              ~           " => (TokenKind::Whitespace, " "),
        "                               ~~~~~~~~~  " => (TokenKind::FloatLiteral, "0_1.0e_1_"),
        "                                        ~~" => (TokenKind::Whitespace, "  "),
    };
}

#[test]
fn keywords() {
    test! {
        "  as case else if import in let record Record then Type where  ",
        "~~                                                             " => (TokenKind::Whitespace, "  "),
        "  ~~                                                           " => (TokenKind::Identifier, "as"),
        "    ~                                                          " => (TokenKind::Whitespace, " "),
        "     ~~~~                                                      " => (TokenKind::Keyword, "case"),
        "         ~                                                     " => (TokenKind::Whitespace, " "),
        "          ~~~~                                                 " => (TokenKind::Keyword, "else"),
        "              ~                                                " => (TokenKind::Whitespace, " "),
        "               ~~                                              " => (TokenKind::Keyword, "if"),
        "                 ~                                             " => (TokenKind::Whitespace, " "),
        "                  ~~~~~~                                       " => (TokenKind::Identifier, "import"),
        "                        ~                                      " => (TokenKind::Whitespace, " "),
        "                         ~~                                    " => (TokenKind::Keyword, "in"),
        "                           ~                                   " => (TokenKind::Whitespace, " "),
        "                            ~~~                                " => (TokenKind::Keyword, "let"),
        "                               ~                               " => (TokenKind::Whitespace, " "),
        "                                ~~~~~~                         " => (TokenKind::Keyword, "record"),
        "                                      ~                        " => (TokenKind::Whitespace, " "),
        "                                       ~~~~~~                  " => (TokenKind::Keyword, "Record"),
        "                                             ~                 " => (TokenKind::Whitespace, " "),
        "                                              ~~~~             " => (TokenKind::Keyword, "then"),
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
        r" ~                      " => (TokenKind::Symbol, r"\"),
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
        r"                    ~   " => (TokenKind::Question, "?"),
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
        " ~           " => (TokenKind::Open(DelimKind::Paren), "("),
        "  ~          " => (TokenKind::Whitespace, " "),
        "   ~         " => (TokenKind::Close(DelimKind::Paren), ")"),
        "    ~        " => (TokenKind::Whitespace, " "),
        "     ~       " => (TokenKind::Open(DelimKind::Brace), "{"),
        "      ~      " => (TokenKind::Whitespace, " "),
        "       ~     " => (TokenKind::Close(DelimKind::Brace), "}"),
        "        ~    " => (TokenKind::Whitespace, " "),
        "         ~   " => (TokenKind::Open(DelimKind::Bracket), "["),
        "          ~  " => (TokenKind::Whitespace, " "),
        "           ~ " => (TokenKind::Close(DelimKind::Bracket), "]"),
        "            ~" => (TokenKind::Whitespace, " "),
    }
}
