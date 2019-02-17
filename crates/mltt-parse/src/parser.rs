//! The parser
//!
//! # Naive grammar
//!
//! The language follows the following [BNF]-style grammar:
//!
//! ```text
//! module  ::= item* EOF
//!
//! item    ::= DOC_COMMENT* IDENTIFIER ":" term ";"
//!           | DOC_COMMENT* IDENTIFIER pattern* (":" term)? "=" term ";"
//!
//! pattern ::= IDENTIFIER
//!
//! term    ::= IDENTIFIER
//!           | STRING_LITERAL
//!           | CHAR_LITERAL
//!           | INT_LITERAL
//!           | FLOAT_LITERAL
//!           | "let" IDENTIFIER "=" term "in" term
//!           | term ":" term
//!           | "(" term ")"
//!           | "Fun" ("(" IDENTIFIER+ ":" term ")")+ "->" term
//!           | term "->" term
//!           | "fun" pattern+ "=>" term
//!           | term term
//!           | "Record" "{" (record-type-field ";")* record-type-field? "}"
//!           | "record" "{" (record-intro-field ";")* record-intro-field? "}"
//!           | term "." IDENTIFIER
//!           | "Type" ("^" INT_LITERAL)?
//!
//! record-type-field   ::= DOC_COMMENT* IDENTIFIER ":" term
//! record-intro-field  ::= IDENTIFIER
//!                       | IDENTIFIER pattern* (":" term)? "=" term
//! ```
//!
//! Note that there are a number of ambiguities here that we will have to
//! address through the use of top-down operator precedence parsing and some
//! ordered choice.
//!
//! [BNF]: https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form
//!

use language_reporting::{Diagnostic, Label};
use mltt_concrete::{
    Declaration, Definition, Item, Literal, LiteralKind, Pattern, RecordIntroField,
    RecordTypeField, Term,
};
use mltt_span::FileSpan;

use crate::token::{DelimKind, Token, TokenKind};

pub fn parse_module<'file>(
    tokens: impl Iterator<Item = Token<'file>> + 'file,
) -> Result<Vec<Item>, Diagnostic<FileSpan>> {
    let mut parser = Parser::new(tokens);
    let module = parser.parse_module()?;
    parser.expect_eof()?;
    Ok(module)
}

pub fn parse_item<'file>(
    tokens: impl Iterator<Item = Token<'file>> + 'file,
) -> Result<Item, Diagnostic<FileSpan>> {
    let mut parser = Parser::new(tokens);
    let item = parser.parse_item()?;
    parser.expect_eof()?;
    Ok(item)
}

pub fn parse_term<'file>(
    tokens: impl Iterator<Item = Token<'file>> + 'file,
) -> Result<Term, Diagnostic<FileSpan>> {
    let mut parser = Parser::new(tokens);
    let term = parser.parse_term(Prec(0))?;
    parser.expect_eof()?;
    Ok(term)
}

trait Matcher<Given> {
    fn is_match(&self, given: &Given) -> bool;
}

impl Matcher<Token<'_>> for TokenKind {
    fn is_match(&self, given: &Token<'_>) -> bool {
        given.kind == *self
    }
}

struct Keyword<'a>(pub &'a str);

impl Matcher<Token<'_>> for Keyword<'_> {
    fn is_match(&self, given: &Token<'_>) -> bool {
        given.kind == TokenKind::Keyword && given.slice == self.0
    }
}

struct ArgTermStart;

impl Matcher<Token<'_>> for ArgTermStart {
    fn is_match(&self, given: &Token<'_>) -> bool {
        match given.kind {
            TokenKind::Identifier
            | TokenKind::StringLiteral
            | TokenKind::CharLiteral
            | TokenKind::IntLiteral
            | TokenKind::FloatLiteral
            | TokenKind::Open(DelimKind::Paren) => true,
            _ => false,
        }
    }
}

/// The precedence or 'binding strength' of an infix operator
///
/// This controls how different operators should [be prioritised][order-of-operations]
/// in the absence of explicit grouping. For example, if `*` has a greater
/// precedence than `+`, then `a * b + c` will be parsed as `(a * b) + c`.
///
/// [order-of-operations]: https://en.wikipedia.org/wiki/Order_of_operations
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Prec(pub u32);

impl std::ops::Add<u32> for Prec {
    type Output = Prec;

    fn add(self, other: u32) -> Prec {
        Prec(self.0 + other)
    }
}

impl std::ops::Sub<u32> for Prec {
    type Output = Prec;

    fn sub(self, other: u32) -> Prec {
        Prec(self.0.saturating_sub(other))
    }
}

impl PartialEq<u32> for Prec {
    fn eq(&self, other: &u32) -> bool {
        self.eq(&Prec(*other))
    }
}

impl PartialOrd<u32> for Prec {
    fn partial_cmp(&self, other: &u32) -> Option<std::cmp::Ordering> {
        self.partial_cmp(&Prec(*other))
    }
}

/// Skip whitespace or line comment tokens
fn next_non_whitespace<'file>(
    tokens: &mut impl Iterator<Item = Token<'file>>,
) -> Option<Token<'file>> {
    tokens.skip_while(Token::is_whitespace).next()
}

/// A language parser
struct Parser<Tokens: Iterator> {
    /// The underlying iterator of tokens.
    tokens: Tokens,
    /// For remembering the peeked token.
    peeked: Option<Tokens::Item>,
}

impl<'file, Tokens> Parser<Tokens>
where
    Tokens: Iterator<Item = Token<'file>> + 'file,
{
    /// Create a new parser from an iterator of tokens
    fn new(mut tokens: Tokens) -> Parser<Tokens> {
        let peeked = next_non_whitespace(&mut tokens);
        Parser { tokens, peeked }
    }

    /// Peek at the current lookahead token.
    fn peek(&self) -> Option<&Token<'file>> {
        self.peeked.as_ref()
    }

    /// Consume the current token and load the next one. Return the old token.
    fn advance(&mut self) -> Option<Token<'file>> {
        let next_token = std::mem::replace(&mut self.peeked, next_non_whitespace(&mut self.tokens));

        log::trace!(
            "shift: consumed = {:?}, lookahead = {:?}",
            next_token,
            self.peek(),
        );

        next_token
    }

    fn check_match(&self, matcher: impl Matcher<Token<'file>>) -> bool {
        self.peek().map_or(false, |token| matcher.is_match(token))
    }

    fn try_match(&mut self, matcher: impl Matcher<Token<'file>>) -> Option<Token<'file>> {
        if self.check_match(matcher) {
            self.advance()
        } else {
            None
        }
    }

    fn expect_match(
        &mut self,
        matcher: impl Matcher<Token<'file>>,
    ) -> Result<Token<'file>, Diagnostic<FileSpan>> {
        self.try_match(matcher).ok_or_else(|| {
            log::debug!("unexpected: lookahead = {:?}", self.peek());
            match self.peek() {
                None => Diagnostic::new_error("unexpected EOF"), // FIXME: Span
                Some(token) => Diagnostic::new_error("unexpected token")
                    .with_label(Label::new_primary(token.span).with_message("token found here")),
            }
        })
    }

    fn try_identifier(&mut self) -> Option<String> {
        Some(self.try_match(TokenKind::Identifier)?.slice.to_owned())
    }

    fn expect_identifier(&mut self) -> Result<String, Diagnostic<FileSpan>> {
        Ok(self.expect_match(TokenKind::Identifier)?.slice.to_owned())
    }

    fn expect_eof(&mut self) -> Result<(), Diagnostic<FileSpan>> {
        match self.peek() {
            None => Ok(()),
            Some(token) => {
                log::debug!("non-eof token {:?}", token);
                Err(Diagnostic::new_error("expected EOF")
                    .with_label(Label::new_primary(token.span).with_message("unexpected token")))
            },
        }
    }

    fn expect_doc_comments(&mut self) -> Vec<String> {
        let mut docs = Vec::new();
        while let Some(doc_token) = self.try_match(TokenKind::LineDoc) {
            docs.push(doc_token.slice.to_owned());
        }
        docs
    }

    /// Expect a module
    ///
    /// ```text
    /// module ::= item*
    /// ```
    fn parse_module(&mut self) -> Result<Vec<Item>, Diagnostic<FileSpan>> {
        let mut items = Vec::new();
        while self.peek().is_some() {
            items.push(self.parse_item()?);
        }
        Ok(items)
    }

    /// Expect an item
    ///
    /// ```text
    /// item ::= DOC_COMMENT* IDENTIFIER ":" term(0) ";"
    ///        | DOC_COMMENT* IDENTIFIER IDENTIFIER* (":" term(0))? "=" term(0) ";"
    /// ```
    fn parse_item(&mut self) -> Result<Item, Diagnostic<FileSpan>> {
        log::trace!("expecting item");

        let docs = self.expect_doc_comments();
        let label = self.expect_identifier()?;

        log::trace!("item label: {:?}", label);

        if self.try_match(TokenKind::Colon).is_some() {
            log::trace!("expecting item declaration");

            let ann = self.parse_term(Prec(0))?;
            self.expect_match(TokenKind::Semicolon)?;

            let declaration = Declaration { docs, label, ann };

            Ok(Item::Declaration(declaration))
        } else {
            log::trace!("expecting item definition");

            let patterns = self.parse_patterns()?;

            let body_ty = if self.try_match(TokenKind::Colon).is_some() {
                Some(self.parse_term(Prec(0))?)
            } else {
                None
            };

            if self.try_match(TokenKind::Equals).is_some() {
                let body = self.parse_term(Prec(0))?;
                self.expect_match(TokenKind::Semicolon)?;

                let definition = Definition {
                    docs,
                    label,
                    patterns,
                    body_ty,
                    body,
                };

                Ok(Item::Definition(definition))
            } else if patterns.is_empty() {
                // TODO: Span
                Err(Diagnostic::new_error("expected declaration or definition"))
            } else {
                // TODO: Span
                Err(Diagnostic::new_error(
                    "expected equals after definition parameters",
                ))
            }
        }
    }

    /// Parse zero-or-more patterns
    ///
    /// ```text
    /// patterns ::= pattern*
    /// ```
    fn parse_patterns(&mut self) -> Result<Vec<Pattern>, Diagnostic<FileSpan>> {
        let mut patterns = Vec::new();
        while self.check_match(ArgTermStart) {
            patterns.push(self.parse_pattern()?);
        }
        Ok(patterns)
    }

    /// Parse a pattern
    ///
    /// ```text
    /// pattern ::= IDENTIFIER
    /// ```
    fn parse_pattern(&mut self) -> Result<Pattern, Diagnostic<FileSpan>> {
        let token = self.expect_match(TokenKind::Identifier)?;
        Ok(Pattern::Var(token.slice.to_owned()))
    }

    /// Parse a term
    ///
    /// ```text
    /// term(prec) ::= operators(prec) {
    ///     prefix  "let"               ::= let
    ///     prefix  "("                 ::= parens fun-app
    ///     prefix  "Fun"               ::= fun-type
    ///     prefix  "fun"               ::= fun-intro
    ///     prefix  "Record"            ::= record-type
    ///     prefix  "record"            ::= record-intro
    ///     prefix  "Type"              ::= universe
    ///     prefix  IDENTIFIER          ::= fun-app
    ///     nilfix  STRING_LITERAL
    ///     nilfix  CHAR_LITERAL
    ///     nilfix  INT_LITERAL
    ///     nilfix  FLOAT_LITERAL
    ///
    ///     infixr  "."             80  ::= record-proj fun-app
    ///     infixr  ":"             20  ::= ann
    ///     infixr  "->"            50  ::= fun-arrow-type
    /// }
    /// ```
    fn parse_term(&mut self, right_prec: Prec) -> Result<Term, Diagnostic<FileSpan>> {
        // Use Top-Down Operator Precedence Parsing (a.k.a. Pratt Parsing) to
        // recognise the term syntax. This is not yet abstracted out into a more
        // general form.

        let token = self.advance().ok_or_else(
            || Diagnostic::new_error("unexpected EOF"), // FIXME: Spanned diagnostic
        )?;

        // Prefix operators
        let mut term = match (token.kind, token.slice) {
            (TokenKind::Identifier, _) => {
                let term = self.parse_var(token)?;
                self.parse_fun_app(term)
            },
            (TokenKind::StringLiteral, _) => self.parse_string_literal(token),
            (TokenKind::CharLiteral, _) => self.parse_char_literal(token),
            (TokenKind::IntLiteral, _) => self.parse_int_literal(token),
            (TokenKind::FloatLiteral, _) => self.parse_float_literal(token),
            (TokenKind::Open(DelimKind::Paren), _) => {
                let term = self.parse_parens(token)?;
                self.parse_fun_app(term)
            },
            (TokenKind::Keyword, "Fun") => self.parse_fun_ty(token),
            (TokenKind::Keyword, "fun") => self.parse_fun_intro(token),
            (TokenKind::Keyword, "Record") => self.parse_record_ty(token),
            (TokenKind::Keyword, "record") => self.parse_record_intro(token),
            (TokenKind::Keyword, "let") => self.parse_let(token),
            (TokenKind::Keyword, "Type") => self.parse_universe(token),
            (_, _) => Err(Diagnostic::new_error("expected a term")
                .with_label(Label::new_primary(token.span).with_message("term expected here"))),
        }?;

        // Infix operators
        while let Some(token) = self.peek() {
            match token.kind {
                TokenKind::Dot if right_prec < 80 => {
                    let token = self.advance().unwrap();
                    term = self.parse_record_proj(term, token)?;
                    term = self.parse_fun_app(term)?;
                },
                TokenKind::Colon if right_prec < 20 => {
                    let token = self.advance().unwrap();
                    term = self.parse_ann(term, token)?;
                },
                TokenKind::RArrow if right_prec < 50 => {
                    let token = self.advance().unwrap();
                    term = self.parse_fun_arrow_type(term, token)?;
                },
                _ => break,
            }
        }

        Ok(term)
    }

    /// Parse an argument term
    ///
    /// ```text
    /// arg-term(prec) ::= operators(prec) {
    ///     prefix  "("                 ::= parens
    ///     prefix  "Type"              ::= universe
    ///     nilfix  IDENTIFIER
    ///     nilfix  STRING_LITERAL
    ///     nilfix  CHAR_LITERAL
    ///     nilfix  INT_LITERAL
    ///     nilfix  FLOAT_LITERAL
    ///
    ///     infixr  "."             80  ::= record-proj
    /// }
    /// ```
    fn parse_arg_term(&mut self, right_prec: Prec) -> Result<Term, Diagnostic<FileSpan>> {
        // Use Top-Down Operator Precedence Parsing (a.k.a. Pratt Parsing) to
        // recognise the term syntax. This is not yet abstracted out into a more
        // general form.

        let token = self.advance().ok_or_else(
            || Diagnostic::new_error("unexpected EOF"), // FIXME: Spanned diagnostic
        )?;

        // Prefix operators
        let mut term = match (token.kind, token.slice) {
            (TokenKind::Identifier, _) => self.parse_var(token),
            (TokenKind::StringLiteral, _) => self.parse_string_literal(token),
            (TokenKind::CharLiteral, _) => self.parse_char_literal(token),
            (TokenKind::IntLiteral, _) => self.parse_int_literal(token),
            (TokenKind::FloatLiteral, _) => self.parse_float_literal(token),
            (TokenKind::Open(DelimKind::Paren), _) => self.parse_parens(token),
            (TokenKind::Keyword, "Type") => self.parse_universe(token),
            (_, _) => Err(Diagnostic::new_error("expected a term")
                .with_label(Label::new_primary(token.span).with_message("term expected here"))),
        }?;

        // Infix operators
        while let Some(token) = self.peek() {
            match token.kind {
                TokenKind::Dot if right_prec < 80 => {
                    let token = self.advance().unwrap();
                    term = self.parse_record_proj(term, token)?;
                },
                _ => break,
            }
        }

        Ok(term)
    }

    /// Parse the trailing part of a variable
    fn parse_var(&mut self, token: Token<'file>) -> Result<Term, Diagnostic<FileSpan>> {
        Ok(Term::Var(token.slice.to_owned()))
    }

    /// Parse the trailing part of a string literal
    fn parse_string_literal(&mut self, token: Token<'file>) -> Result<Term, Diagnostic<FileSpan>> {
        Ok(Term::Literal(Literal {
            kind: LiteralKind::String,
            value: token.slice.to_owned(),
        }))
    }

    /// Parse the trailing part of a character literal
    fn parse_char_literal(&mut self, token: Token<'file>) -> Result<Term, Diagnostic<FileSpan>> {
        Ok(Term::Literal(Literal {
            kind: LiteralKind::Char,
            value: token.slice.to_owned(),
        }))
    }

    /// Parse the trailing part of a integer literal
    fn parse_int_literal(&mut self, token: Token<'file>) -> Result<Term, Diagnostic<FileSpan>> {
        Ok(Term::Literal(Literal {
            kind: LiteralKind::Int,
            value: token.slice.to_owned(),
        }))
    }

    /// Parse the trailing part of a floating point literal
    fn parse_float_literal(&mut self, token: Token<'file>) -> Result<Term, Diagnostic<FileSpan>> {
        Ok(Term::Literal(Literal {
            kind: LiteralKind::Float,
            value: token.slice.to_owned(),
        }))
    }

    /// Parse the trailing part of a function introduction
    ///
    /// ```text
    /// fun-ty ::= ("("IDENTIFIER+ ":" term(0) ")")+ "->" term(50 - 1)
    /// ```
    fn parse_fun_ty(&mut self, token: Token<'file>) -> Result<Term, Diagnostic<FileSpan>> {
        let mut params = Vec::new();

        while let Some(paren_token) = self.try_match(TokenKind::Open(DelimKind::Paren)) {
            let mut param_names = Vec::new();
            while let Some(param_name) = self.try_identifier() {
                param_names.push(param_name);
            }
            if param_names.is_empty() {
                return Err(Diagnostic::new_error("expected at least one parameter")
                    .with_label(Label::new_primary(paren_token.span).with_message(
                        "at least one parameter was expected after this parenthesis",
                    )));
            }

            self.expect_match(TokenKind::Colon)?;
            let param_ty = self.parse_term(Prec(0))?;
            params.push((param_names, param_ty));

            self.expect_match(TokenKind::Close(DelimKind::Paren))?;
        }

        if params.is_empty() {
            return Err(
                Diagnostic::new_error("expected at least one parameter").with_label(
                    Label::new_primary(token.span)
                        .with_message("at least one parameter was expected after this keyword"),
                ),
            );
        }

        self.expect_match(TokenKind::RArrow)?;
        let body_ty = self.parse_term(Prec(50 - 1))?;

        Ok(Term::FunType(params, Box::new(body_ty)))
    }

    /// Parse the trailing part of a function introduction
    ///
    /// ```text
    /// fun-intro ::= IDENTIFIER+ "=>" term(0)
    /// ```
    fn parse_fun_intro(&mut self, token: Token<'file>) -> Result<Term, Diagnostic<FileSpan>> {
        let patterns = self.parse_patterns()?;
        if patterns.is_empty() {
            return Err(
                Diagnostic::new_error("expected at least one parameters").with_label(
                    Label::new_primary(token.span)
                        .with_message("at least one parameter was expected after this keyword"),
                ),
            );
        }
        self.expect_match(TokenKind::RFatArrow)?;
        let body = self.parse_term(Prec(0))?;

        Ok(Term::FunIntro(patterns, Box::new(body)))
    }

    /// Parse the trailing part of a parenthesis grouping
    ///
    /// ```text
    /// parens ::= term(0) ")"
    /// ```
    fn parse_parens(&mut self, _token: Token<'file>) -> Result<Term, Diagnostic<FileSpan>> {
        let term = self.parse_term(Prec(0))?;
        self.expect_match(TokenKind::Close(DelimKind::Paren))?;

        Ok(Term::Parens(Box::new(term)))
    }

    /// Parse the trailing part of a record type
    ///
    /// ```text
    /// record-type         ::= "{" (record-type-field ";")* record-type-field? "}"
    /// record-type-field   ::= DOC_COMMENT* IDENTIFIER ":" term(0)
    /// ```
    fn parse_record_ty(&mut self, _token: Token<'file>) -> Result<Term, Diagnostic<FileSpan>> {
        let mut fields = Vec::new();

        self.expect_match(TokenKind::Open(DelimKind::Brace))?;

        loop {
            let docs = self.expect_doc_comments();

            if let Some(label) = self.try_identifier() {
                self.expect_match(TokenKind::Colon)?;
                let ann = self.parse_term(Prec(0))?;

                fields.push(RecordTypeField { docs, label, ann });

                if self.try_match(TokenKind::Semicolon).is_some() {
                    continue;
                } else {
                    self.expect_match(TokenKind::Close(DelimKind::Brace))?;
                    return Ok(Term::RecordType(fields));
                }
            } else {
                break;
            }
        }

        self.expect_match(TokenKind::Close(DelimKind::Brace))?;

        Ok(Term::RecordType(fields))
    }

    /// Parse the trailing part of a record introduction
    ///
    /// ```text
    /// record-intro        ::= "{" (record-intro-field ";")* record-intro-field? "}"
    /// record-intro-field  ::= IDENTIFIER
    ///                       | IDENTIFIER IDENTIFIER* (":" term(0))? "=" term(0)
    /// ```
    fn parse_record_intro(&mut self, _token: Token<'file>) -> Result<Term, Diagnostic<FileSpan>> {
        let mut fields = Vec::new();

        self.expect_match(TokenKind::Open(DelimKind::Brace))?;

        while let Some(label) = self.try_identifier() {
            let patterns = self.parse_patterns()?;

            // TODO: implement punned fields

            let body_ty = match self.try_match(TokenKind::Colon) {
                None => None,
                Some(_) => Some(self.parse_term(Prec(0))?),
            };

            self.expect_match(TokenKind::Equals)?;
            let body = self.parse_term(Prec(0))?;

            fields.push(RecordIntroField::Explicit {
                label,
                patterns,
                body_ty,
                body,
            });

            if self.try_match(TokenKind::Semicolon).is_some() {
                continue;
            } else {
                self.expect_match(TokenKind::Close(DelimKind::Brace))?;
                return Ok(Term::RecordIntro(fields));
            }
        }

        self.expect_match(TokenKind::Close(DelimKind::Brace))?;

        Ok(Term::RecordIntro(fields))
    }

    /// Parse the trailing part of a let expression
    ///
    /// ```text
    /// let ::= IDENTIFIER "=" term(0) "in" term(0)
    /// ```
    fn parse_let(&mut self, _token: Token<'file>) -> Result<Term, Diagnostic<FileSpan>> {
        let name = self.expect_identifier()?;
        self.expect_match(TokenKind::Equals)?;
        let def_term = self.parse_term(Prec(0))?;
        self.expect_match(Keyword("in"))?;
        let body_term = self.parse_term(Prec(0))?;

        Ok(Term::Let(name, Box::new(def_term), Box::new(body_term)))
    }

    /// Parse the trailing part of a universe
    ///
    /// ```text
    /// universe ::= ("^" INT_LITERAL)?
    /// ```
    fn parse_universe(&mut self, _token: Token<'file>) -> Result<Term, Diagnostic<FileSpan>> {
        if self.try_match(TokenKind::Caret).is_some() {
            let integer_token = self.expect_match(TokenKind::IntLiteral)?;
            // FIXME: if prefixed integer
            // FIXME: if separators
            Ok(Term::Universe(Some(integer_token.slice.parse().unwrap())))
        } else {
            Ok(Term::Universe(None))
        }
    }

    /// Parse the trailing part of a projection
    ///
    /// ```text
    /// record-proj ::= IDENTIFIER
    /// ```
    fn parse_record_proj(
        &mut self,
        lhs: Term,
        _token: Token<'file>,
    ) -> Result<Term, Diagnostic<FileSpan>> {
        let label = self.expect_identifier()?;
        Ok(Term::RecordProj(Box::new(lhs), label))
    }

    /// Parse the trailing part of a type annotation
    ///
    /// ```text
    /// ann ::= term(20 - 1)
    /// ```
    fn parse_ann(&mut self, lhs: Term, _token: Token<'file>) -> Result<Term, Diagnostic<FileSpan>> {
        let rhs = self.parse_term(Prec(20 - 1))?;

        Ok(Term::Ann(Box::new(lhs), Box::new(rhs)))
    }

    /// Parse the trailing part of a function arrow
    ///
    /// ```text
    /// fun-arrow-type ::= term(50 - 1)
    /// ```
    fn parse_fun_arrow_type(
        &mut self,
        lhs: Term,
        _token: Token<'file>,
    ) -> Result<Term, Diagnostic<FileSpan>> {
        let rhs = self.parse_term(Prec(50 - 1))?;

        Ok(Term::FunArrowType(Box::new(lhs), Box::new(rhs)))
    }

    /// Parse the trailing part of a function application
    ///
    /// ```text
    /// fun-app ::= arg-term(0)*
    /// ```
    fn parse_fun_app(&mut self, lhs: Term) -> Result<Term, Diagnostic<FileSpan>> {
        let mut args = Vec::new();

        while self.check_match(ArgTermStart) {
            args.push(self.parse_arg_term(Prec(0))?);
        }

        if args.is_empty() {
            Ok(lhs)
        } else {
            Ok(Term::FunApp(Box::new(lhs), args))
        }
    }
}

#[cfg(test)]
mod tests {
    use language_reporting::termcolor::{ColorChoice, StandardStream};
    use mltt_span::Files;
    use pretty_assertions::assert_eq;

    use super::*;
    use crate::lexer::Lexer;

    macro_rules! test_term {
        ($src:expr, $expected_term:expr,) => {{
            test_term!($src, $expected_term);
        }};
        ($src:expr, $expected_term:expr) => {{
            let _ = pretty_env_logger::try_init();

            let mut files = Files::new();
            let file_id = files.add("test", $src);
            let term = match parse_term(Lexer::new(&files[file_id])) {
                Ok(term) => term,
                Err(diagnostic) => {
                    let writer = StandardStream::stdout(ColorChoice::Always);
                    language_reporting::emit(
                        &mut writer.lock(),
                        &files,
                        &diagnostic,
                        &language_reporting::DefaultConfig,
                    )
                    .unwrap();
                    panic!("error encountered");
                },
            };

            assert_eq!(term, $expected_term);
        }};
    }

    #[test]
    fn var() {
        test_term!("var", Term::Var("var".to_owned()));
    }

    #[test]
    fn string_literal() {
        test_term!(
            "\"value\"",
            Term::Literal(Literal {
                kind: LiteralKind::String,
                value: "\"value\"".to_owned()
            }),
        );
    }

    #[test]
    fn char_literal() {
        test_term!(
            "'\\n'",
            Term::Literal(Literal {
                kind: LiteralKind::Char,
                value: "'\\n'".to_owned()
            }),
        );
    }

    #[test]
    fn int_literal() {
        test_term!(
            "0xA_F00",
            Term::Literal(Literal {
                kind: LiteralKind::Int,
                value: "0xA_F00".to_owned()
            }),
        );
    }

    #[test]
    fn float_literal() {
        test_term!(
            "0.3_46e_23",
            Term::Literal(Literal {
                kind: LiteralKind::Float,
                value: "0.3_46e_23".to_owned()
            }),
        );
    }

    #[test]
    fn let_expr() {
        test_term!(
            "let var = Type in var",
            Term::Let(
                "var".to_owned(),
                Box::new(Term::Universe(None)),
                Box::new(Term::Var("var".to_owned())),
            ),
        );
    }

    #[test]
    fn parens() {
        test_term!("(foo)", Term::Parens(Box::new(Term::Var("foo".to_owned()))));
    }

    #[test]
    fn fun_ty() {
        test_term!(
            r"Fun (x y : Type) (z : Type) -> x",
            Term::FunType(
                vec![
                    (vec!["x".to_owned(), "y".to_owned()], Term::Universe(None)),
                    (vec!["z".to_owned()], Term::Universe(None)),
                ],
                Box::new(Term::Var("x".to_owned())),
            ),
        );
    }

    #[test]
    fn fun_arrow_type() {
        test_term!(
            "Foo -> Bar",
            Term::FunArrowType(
                Box::new(Term::Var("Foo".to_owned())),
                Box::new(Term::Var("Bar".to_owned()))
            ),
        );
    }

    #[test]
    fn fun_arrow_type_nested() {
        test_term!(
            "Foo -> Bar -> Baz",
            Term::FunArrowType(
                Box::new(Term::Var("Foo".to_owned())),
                Box::new(Term::FunArrowType(
                    Box::new(Term::Var("Bar".to_owned())),
                    Box::new(Term::Var("Baz".to_owned())),
                )),
            ),
        );
    }

    #[test]
    fn fun_arrow_type_fun_app() {
        test_term!(
            "Option A -> Option B -> Option C",
            Term::FunArrowType(
                Box::new(Term::FunApp(
                    Box::new(Term::Var("Option".to_owned())),
                    vec![Term::Var("A".to_owned())]
                )),
                Box::new(Term::FunArrowType(
                    Box::new(Term::FunApp(
                        Box::new(Term::Var("Option".to_owned())),
                        vec![Term::Var("B".to_owned())]
                    )),
                    Box::new(Term::FunApp(
                        Box::new(Term::Var("Option".to_owned())),
                        vec![Term::Var("C".to_owned())]
                    )),
                ),)
            ),
        );
    }

    #[test]
    fn fun_intro() {
        test_term!(
            r"fun x => x",
            Term::FunIntro(
                vec![Pattern::Var("x".to_owned())],
                Box::new(Term::Var("x".to_owned())),
            ),
        );
    }

    #[test]
    fn fun_intro_multi_params() {
        test_term!(
            r"fun x y z => x",
            Term::FunIntro(
                vec![
                    Pattern::Var("x".to_owned()),
                    Pattern::Var("y".to_owned()),
                    Pattern::Var("z".to_owned()),
                ],
                Box::new(Term::Var("x".to_owned())),
            ),
        );
    }

    #[test]
    fn fun_app_1() {
        test_term!(
            r"foo arg",
            Term::FunApp(
                Box::new(Term::Var("foo".to_owned())),
                vec![Term::Var("arg".to_owned())],
            ),
        );
    }

    #[test]
    fn fun_app_2a() {
        test_term!(
            r"foo arg1 arg2",
            Term::FunApp(
                Box::new(Term::Var("foo".to_owned())),
                vec![Term::Var("arg1".to_owned()), Term::Var("arg2".to_owned())],
            ),
        );
    }

    #[test]
    fn fun_app_2b() {
        test_term!(
            r"foo (arg1) arg2.foo.bar arg3",
            Term::FunApp(
                Box::new(Term::Var("foo".to_owned())),
                vec![
                    Term::Parens(Box::new(Term::Var("arg1".to_owned()))),
                    Term::RecordProj(
                        Box::new(Term::RecordProj(
                            Box::new(Term::Var("arg2".to_owned())),
                            "foo".to_owned()
                        )),
                        "bar".to_owned()
                    ),
                    Term::Var("arg3".to_owned()),
                ],
            ),
        );
    }

    #[test]
    fn record_type() {
        test_term!(
            "Record { x : Type; y : Type }",
            Term::RecordType(vec![
                RecordTypeField {
                    docs: Vec::new(),
                    label: "x".to_owned(),
                    ann: Term::Universe(None),
                },
                RecordTypeField {
                    docs: Vec::new(),
                    label: "y".to_owned(),
                    ann: Term::Universe(None),
                },
            ]),
        );
    }

    #[test]
    fn record_type_trailing_semicolon() {
        test_term!(
            "Record { x : Type; y : Type; }",
            Term::RecordType(vec![
                RecordTypeField {
                    docs: Vec::new(),
                    label: "x".to_owned(),
                    ann: Term::Universe(None),
                },
                RecordTypeField {
                    docs: Vec::new(),
                    label: "y".to_owned(),
                    ann: Term::Universe(None),
                },
            ]),
        );
    }

    #[test]
    fn record_intro() {
        test_term!(
            "record { x = x; y = y }",
            Term::RecordIntro(vec![
                RecordIntroField::Explicit {
                    label: "x".to_owned(),
                    patterns: Vec::new(),
                    body_ty: None,
                    body: Term::Var("x".to_owned()),
                },
                RecordIntroField::Explicit {
                    label: "y".to_owned(),
                    patterns: Vec::new(),
                    body_ty: None,
                    body: Term::Var("y".to_owned()),
                },
            ]),
        );
    }

    #[test]
    fn record_intro_fun_sugar() {
        test_term!(
            "record { f x y = x; g x y : Type = x }",
            Term::RecordIntro(vec![
                RecordIntroField::Explicit {
                    label: "f".to_owned(),
                    patterns: vec![Pattern::Var("x".to_owned()), Pattern::Var("y".to_owned())],
                    body_ty: None,
                    body: Term::Var("x".to_owned()),
                },
                RecordIntroField::Explicit {
                    label: "g".to_owned(),
                    patterns: vec![Pattern::Var("x".to_owned()), Pattern::Var("y".to_owned())],
                    body_ty: Some(Term::Universe(None)),
                    body: Term::Var("x".to_owned()),
                },
            ]),
        );
    }

    #[test]
    fn record_intro_trailing_semicolon() {
        test_term!(
            "record { x = x; y : Type = y; }",
            Term::RecordIntro(vec![
                RecordIntroField::Explicit {
                    label: "x".to_owned(),
                    patterns: Vec::new(),
                    body_ty: None,
                    body: Term::Var("x".to_owned()),
                },
                RecordIntroField::Explicit {
                    label: "y".to_owned(),
                    patterns: Vec::new(),
                    body_ty: Some(Term::Universe(None)),
                    body: Term::Var("y".to_owned()),
                },
            ]),
        );
    }

    #[test]
    fn record_proj() {
        test_term!(
            "foo.bar",
            Term::RecordProj(Box::new(Term::Var("foo".to_owned())), "bar".to_owned()),
        );
    }

    #[test]
    fn record_proj_proj() {
        test_term!(
            "foo.bar.baz",
            Term::RecordProj(
                Box::new(Term::RecordProj(
                    Box::new(Term::Var("foo".to_owned(),)),
                    "bar".to_owned()
                )),
                "baz".to_owned()
            ),
        );
    }

    #[test]
    fn record_proj_fun_app() {
        test_term!(
            "foo.bar baz foo.bar",
            Term::FunApp(
                Box::new(Term::RecordProj(
                    Box::new(Term::Var("foo".to_owned())),
                    "bar".to_owned()
                )),
                vec![
                    Term::Var("baz".to_owned()),
                    Term::RecordProj(Box::new(Term::Var("foo".to_owned())), "bar".to_owned()),
                ],
            ),
        );
    }

    #[test]
    fn ann() {
        test_term!(
            "foo : Bar : Baz",
            Term::Ann(
                Box::new(Term::Var("foo".to_owned())),
                Box::new(Term::Ann(
                    Box::new(Term::Var("Bar".to_owned())),
                    Box::new(Term::Var("Baz".to_owned()))
                )),
            ),
        );
    }

    #[test]
    fn universe() {
        test_term!("Type", Term::Universe(None));
    }

    #[test]
    fn universe_level_0() {
        test_term!("Type^0", Term::Universe(Some(0)));
    }

    #[test]
    fn universe_level_23() {
        test_term!("Type^23", Term::Universe(Some(23)));
    }
}
