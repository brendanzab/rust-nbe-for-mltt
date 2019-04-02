//! The MLTT language parser.
//!
//! # Naive grammar
//!
//! The language follows the following [BNF]-style grammar:
//!
//! ```text
//! module  ::= item* EOF
//!
//! item    ::= DOC_COMMENT* IDENTIFIER ":" term ";"
//!           | DOC_COMMENT* IDENTIFIER intro-param* (":" term)? "=" term ";"
//!
//! pattern ::= IDENTIFIER
//!           | STRING_LITERAL
//!           | CHAR_LITERAL
//!           | INT_LITERAL
//!           | FLOAT_LITERAL
//!
//! term    ::= IDENTIFIER
//!           | "?"
//!           | "(" term ")"
//!           | term ":" term
//!           | "let" item+ "in" term
//!           | "if" term "then" term "else" term
//!           | "case" term* "{" (case-clause ";")* case-clause? "}"
//!           | STRING_LITERAL
//!           | CHAR_LITERAL
//!           | INT_LITERAL
//!           | FLOAT_LITERAL
//!           | "primitive" STRING_LITERAL
//!           | "Fun" type-param+ "->" term
//!           | term "->" term
//!           | "fun" intro-param+ "=>" term
//!           | term arg
//!           | "Record" "{" (record-type-field ";")* record-type-field? "}"
//!           | "record" "{" (record-intro-field ";")* record-intro-field? "}"
//!           | term "." IDENTIFIER
//!           | "Type" ("^" INT_LITERAL)?
//!
//! type-param  ::= "(" IDENTIFIER+ ":" term ")"
//!               | "{" IDENTIFIER+ (":" term)? "}"
//!               | "{{" IDENTIFIER ":" term "}}"
//! intro-param ::= pattern
//!               | "{" IDENTIFIER ("=" pattern)? "}"
//!               | "{{" IDENTIFIER ("=" pattern)? "}}"
//! arg         ::= term
//!               | "{" IDENTIFIER ("=" term)? "}"
//!               | "{{" IDENTIFIER ("=" term)? "}}"
//!
//! case-clause         ::= intro-param+ "=>" term
//! record-type-field   ::= DOC_COMMENT* IDENTIFIER ":" term
//! record-intro-field  ::= IDENTIFIER
//!                       | IDENTIFIER intro-param* (":" term)? "=" term
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
    Arg, Declaration, Definition, IntroParam, Item, LiteralKind, Pattern, RecordIntroField,
    RecordTypeField, SpannedString, Term, TypeParam,
};
use mltt_span::FileSpan;

use crate::token::{DelimKind, Token, TokenKind};

pub fn parse_module<'file>(
    tokens: impl Iterator<Item = Token<'file>> + 'file,
) -> Result<Vec<Item<'file>>, Diagnostic<FileSpan>> {
    let mut parser = Parser::new(tokens);
    let module = parser.parse_module()?;
    parser.expect_eof()?;
    Ok(module)
}

pub fn parse_item<'file>(
    tokens: impl Iterator<Item = Token<'file>> + 'file,
) -> Result<Item<'file>, Diagnostic<FileSpan>> {
    let mut parser = Parser::new(tokens);
    let item = parser.parse_item()?;
    parser.expect_eof()?;
    Ok(item)
}

pub fn parse_term<'file>(
    tokens: impl Iterator<Item = Token<'file>> + 'file,
) -> Result<Term<'file>, Diagnostic<FileSpan>> {
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
        given.kind == TokenKind::Keyword && given.src.slice == self.0
    }
}

struct ItemStart;

impl Matcher<Token<'_>> for ItemStart {
    fn is_match(&self, given: &Token<'_>) -> bool {
        match given.kind {
            TokenKind::LineDoc | TokenKind::Identifier => true,
            _ => false,
        }
    }
}

struct ScrutineeStart;

impl Matcher<Token<'_>> for ScrutineeStart {
    fn is_match(&self, given: &Token<'_>) -> bool {
        match given.kind {
            TokenKind::Identifier
            | TokenKind::StringLiteral
            | TokenKind::CharLiteral
            | TokenKind::IntLiteral
            | TokenKind::FloatLiteral => true,
            TokenKind::Keyword if given.src.slice == "Type" => true,
            _ => false,
        }
    }
}

struct ArgParamStart;

impl Matcher<Token<'_>> for ArgParamStart {
    fn is_match(&self, given: &Token<'_>) -> bool {
        match given.kind {
            TokenKind::Identifier
            | TokenKind::StringLiteral
            | TokenKind::CharLiteral
            | TokenKind::IntLiteral
            | TokenKind::FloatLiteral
            | TokenKind::Open(DelimKind::Paren)
            | TokenKind::Open(DelimKind::Brace) => true,
            TokenKind::Keyword if given.src.slice == "Type" => true,
            _ => false,
        }
    }
}

/// The precedence or 'binding strength' of an infix operator.
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

/// Skip whitespace or line comment tokens.
fn next_non_whitespace<'file>(
    tokens: &mut impl Iterator<Item = Token<'file>>,
) -> Option<Token<'file>> {
    tokens.skip_while(Token::is_whitespace).next()
}

/// A language parser.
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
    /// Create a new parser from an iterator of tokens.
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

    fn is_peek_match(&self, matcher: impl Matcher<Token<'file>>) -> bool {
        self.peek().map_or(false, |token| matcher.is_match(token))
    }

    fn try_match(&mut self, matcher: impl Matcher<Token<'file>>) -> Option<Token<'file>> {
        if self.is_peek_match(matcher) {
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
                    .with_label(Label::new_primary(token.span()).with_message("token found here")),
            }
        })
    }

    fn try_identifier(&mut self) -> Option<SpannedString<'file>> {
        let token = self.try_match(TokenKind::Identifier)?;
        Some(token.src)
    }

    fn expect_identifier(&mut self) -> Result<SpannedString<'file>, Diagnostic<FileSpan>> {
        let token = self.expect_match(TokenKind::Identifier)?;
        Ok(token.src)
    }

    fn expect_eof(&mut self) -> Result<(), Diagnostic<FileSpan>> {
        match self.peek() {
            None => Ok(()),
            Some(token) => {
                log::debug!("non-eof token {:?}", token);
                Err(Diagnostic::new_error("expected EOF")
                    .with_label(Label::new_primary(token.span()).with_message("unexpected token")))
            },
        }
    }

    fn expect_doc_comments(&mut self) -> Vec<SpannedString<'file>> {
        let mut docs = Vec::new();
        while let Some(doc_token) = self.try_match(TokenKind::LineDoc) {
            docs.push(doc_token.src);
        }
        docs
    }

    /// Parse a module.
    ///
    /// ```text
    /// module ::= item*
    /// ```
    fn parse_module(&mut self) -> Result<Vec<Item<'file>>, Diagnostic<FileSpan>> {
        let mut items = Vec::new();
        while self.peek().is_some() {
            items.push(self.parse_item()?);
        }
        Ok(items)
    }

    /// Parse an item.
    ///
    /// ```text
    /// item ::= DOC_COMMENT* IDENTIFIER ":" term(0) ";"
    ///        | DOC_COMMENT* IDENTIFIER intro-param* (":" term(0))? "=" term(0) ";"
    /// ```
    fn parse_item(&mut self) -> Result<Item<'file>, Diagnostic<FileSpan>> {
        log::trace!("expecting item");

        let docs = self.expect_doc_comments();
        let name = self.expect_identifier()?;

        log::trace!("item name: {:?}", name);

        let params = self.parse_intro_params()?;

        let body_ty = if self.try_match(TokenKind::Colon).is_some() {
            let body_ty = self.parse_term(Prec(0))?;

            if params.is_empty() && self.try_match(TokenKind::Semicolon).is_some() {
                let decl = Declaration {
                    docs,
                    name,
                    body_ty,
                };

                return Ok(Item::Declaration(decl));
            } else {
                Some(body_ty)
            }
        } else {
            None
        };

        if self.try_match(TokenKind::Equals).is_some() {
            let body = self.parse_term(Prec(0))?;
            self.expect_match(TokenKind::Semicolon)?;

            let defn = Definition {
                docs,
                name,
                params,
                body_ty,
                body,
            };

            Ok(Item::Definition(defn))
        } else if params.is_empty() {
            // TODO: Span
            Err(Diagnostic::new_error("expected declaration or definition"))
        } else {
            // TODO: Span
            Err(Diagnostic::new_error(
                "expected equals after definition parameters",
            ))
        }
    }

    /// Parse zero-or-more function introduction parameters.
    ///
    /// ```text
    /// intro-params ::= intro-param*
    /// ```
    fn parse_intro_params(&mut self) -> Result<Vec<IntroParam<'file>>, Diagnostic<FileSpan>> {
        let mut params = Vec::new();
        while self.is_peek_match(ArgParamStart) {
            params.push(self.parse_intro_param()?);
        }
        Ok(params)
    }

    /// Parse a function introduction parameter.
    ///
    /// ```text
    /// intro-param ::= pattern(0)
    ///               | "{" IDENTIFIER ("=" pattern(0))? "}"
    ///               | "{{" IDENTIFIER ("=" pattern(0))? "}}"
    /// ```
    fn parse_intro_param(&mut self) -> Result<IntroParam<'file>, Diagnostic<FileSpan>> {
        if let Some(start_token) = self.try_match(TokenKind::Open(DelimKind::Brace)) {
            let is_instance = self.try_match(TokenKind::Open(DelimKind::Brace)).is_some();

            let label = self.expect_identifier()?;
            let term = match self.try_match(TokenKind::Equals) {
                Some(_) => Some(self.parse_pattern(Prec(0))?),
                None => None,
            };

            let end_token = if is_instance {
                self.expect_match(TokenKind::Close(DelimKind::Brace))?;
                self.expect_match(TokenKind::Close(DelimKind::Brace))?
            } else {
                self.expect_match(TokenKind::Close(DelimKind::Brace))?
            };

            let span = FileSpan::merge(start_token.span(), end_token.span());

            Ok(if is_instance {
                IntroParam::Instance(span, label, term)
            } else {
                IntroParam::Implicit(span, label, term)
            })
        } else {
            Ok(IntroParam::Explicit(self.parse_pattern(Prec(0))?))
        }
    }

    /// Parse an argument.
    ///
    /// ```text
    /// arg ::= arg-term(0)
    ///       | "{" IDENTIFIER ("=" term(0))? "}"
    ///       | "{{" IDENTIFIER ("=" term(0))? "}}"
    /// ```
    fn parse_arg(&mut self) -> Result<Arg<'file>, Diagnostic<FileSpan>> {
        if let Some(start_arg_token) = self.try_match(TokenKind::Open(DelimKind::Brace)) {
            let is_instance = self.try_match(TokenKind::Open(DelimKind::Brace)).is_some();

            let label = self.expect_identifier()?;
            let term = match self.try_match(TokenKind::Equals) {
                Some(_) => Some(self.parse_term(Prec(0))?),
                None => None,
            };

            let end_arg_token = if is_instance {
                self.expect_match(TokenKind::Close(DelimKind::Brace))?;
                self.expect_match(TokenKind::Close(DelimKind::Brace))?
            } else {
                self.expect_match(TokenKind::Close(DelimKind::Brace))?
            };

            let arg_span = FileSpan::merge(start_arg_token.span(), end_arg_token.span());

            Ok(if is_instance {
                Arg::Instance(arg_span, label, term)
            } else {
                Arg::Implicit(arg_span, label, term)
            })
        } else {
            Ok(Arg::Explicit(self.parse_arg_term(Prec(0))?))
        }
    }

    /// Parse a pattern.
    ///
    /// ```text
    /// pattern(prec) ::= operators(prec) {
    ///     nilfix  IDENTIFIER
    ///     nilfix  STRING_LITERAL
    ///     nilfix  CHAR_LITERAL
    ///     nilfix  INT_LITERAL
    ///     nilfix  FLOAT_LITERAL
    /// }
    /// ```
    fn parse_pattern(&mut self, _right_prec: Prec) -> Result<Pattern<'file>, Diagnostic<FileSpan>> {
        // Use Top-Down Operator Precedence Parsing (a.k.a. Pratt Parsing) to
        // recognise the term syntax. This is not yet abstracted out into a more
        // general form.

        let token = self.advance().ok_or_else(
            || Diagnostic::new_error("unexpected EOF"), // FIXME: Spanned diagnostic
        )?;

        // Prefix operators
        let pattern = match (token.kind, token.src.slice) {
            (TokenKind::Identifier, _) => Ok(Pattern::Var(self.parse_var(token)?)),
            (TokenKind::StringLiteral, _) => {
                let (kind, literal) = self.parse_string_literal(token)?;
                Ok(Pattern::LiteralIntro(kind, literal))
            },
            (TokenKind::CharLiteral, _) => {
                let (kind, literal) = self.parse_char_literal(token)?;
                Ok(Pattern::LiteralIntro(kind, literal))
            },
            (TokenKind::IntLiteral, _) => {
                let (kind, literal) = self.parse_int_literal(token)?;
                Ok(Pattern::LiteralIntro(kind, literal))
            },
            (TokenKind::FloatLiteral, _) => {
                let (kind, literal) = self.parse_float_literal(token)?;
                Ok(Pattern::LiteralIntro(kind, literal))
            },
            (_, _) => Err(Diagnostic::new_error("expected a pattern").with_label(
                Label::new_primary(token.span()).with_message("pattern expected here"),
            )),
        }?;

        // Infix operators
        while let Some(token) = self.peek() {
            match token.kind {
                _ => break,
            }
        }

        Ok(pattern)
    }

    /// Parse a term.
    ///
    /// ```text
    /// term(prec) ::= operators(prec) {
    ///     prefix  "let"               ::= let-expr
    ///     prefix  "if"                ::= if-expr
    ///     prefix  "case"              ::= case-expr
    ///     prefix  "("                 ::= parens fun-elim
    ///     prefix  "Fun"               ::= fun-type
    ///     prefix  "fun"               ::= fun-intro
    ///     prefix  "Record"            ::= record-type
    ///     prefix  "record"            ::= record-intro
    ///     prefix  "Type"              ::= universe
    ///     prefix  "primitive"         ::= primitive
    ///     prefix  IDENTIFIER          ::= fun-elim
    ///     nilfix  "?"                 ::= hole fun-elim
    ///     nilfix  STRING_LITERAL
    ///     nilfix  CHAR_LITERAL
    ///     nilfix  INT_LITERAL
    ///     nilfix  FLOAT_LITERAL
    ///
    ///     infixr  "."             80  ::= record-elim fun-elim
    ///     infixr  ":"             20  ::= ann
    ///     infixr  "->"            50  ::= fun-arrow-type
    /// }
    /// ```
    fn parse_term(&mut self, right_prec: Prec) -> Result<Term<'file>, Diagnostic<FileSpan>> {
        // Use Top-Down Operator Precedence Parsing (a.k.a. Pratt Parsing) to
        // recognise the term syntax. This is not yet abstracted out into a more
        // general form.

        let token = self.advance().ok_or_else(
            || Diagnostic::new_error("unexpected EOF"), // FIXME: Spanned diagnostic
        )?;

        // Prefix operators
        let mut term = match (token.kind, token.src.slice) {
            (TokenKind::Identifier, _) => {
                let term = Term::Var(self.parse_var(token)?);
                self.parse_fun_elim(term)
            },
            (TokenKind::Question, _) => {
                let term = self.parse_hole(token)?;
                self.parse_fun_elim(term)
            },
            (TokenKind::StringLiteral, _) => {
                let (kind, literal) = self.parse_string_literal(token)?;
                Ok(Term::LiteralIntro(kind, literal))
            },
            (TokenKind::CharLiteral, _) => {
                let (kind, literal) = self.parse_char_literal(token)?;
                Ok(Term::LiteralIntro(kind, literal))
            },
            (TokenKind::IntLiteral, _) => {
                let (kind, literal) = self.parse_int_literal(token)?;
                Ok(Term::LiteralIntro(kind, literal))
            },
            (TokenKind::FloatLiteral, _) => {
                let (kind, literal) = self.parse_float_literal(token)?;
                Ok(Term::LiteralIntro(kind, literal))
            },
            (TokenKind::Open(DelimKind::Paren), _) => {
                let term = self.parse_parens(token)?;
                self.parse_fun_elim(term)
            },
            (TokenKind::Keyword, "Fun") => self.parse_fun_ty(token),
            (TokenKind::Keyword, "fun") => self.parse_fun_intro(token),
            (TokenKind::Keyword, "Record") => self.parse_record_ty(token),
            (TokenKind::Keyword, "record") => self.parse_record_intro(token),
            (TokenKind::Keyword, "let") => self.parse_let_expr(token),
            (TokenKind::Keyword, "if") => self.parse_if_expr(token),
            (TokenKind::Keyword, "case") => self.parse_case_expr(token),
            (TokenKind::Keyword, "Type") => self.parse_universe(token),
            (TokenKind::Keyword, "primitive") => self.parse_prim(token),
            (_, _) => Err(Diagnostic::new_error("expected a term")
                .with_label(Label::new_primary(token.span()).with_message("term expected here"))),
        }?;

        // Infix operators
        while let Some(token) = self.peek() {
            match token.kind {
                TokenKind::Dot if right_prec < 80 => {
                    let token = self.advance().unwrap();
                    term = self.parse_record_elim(term, token)?;
                    term = self.parse_fun_elim(term)?;
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

    /// Parse an argument term.
    ///
    /// ```text
    /// arg-term(prec) ::= operators(prec) {
    ///     prefix  "("                 ::= parens
    ///     prefix  "Type"              ::= universe
    ///     nilfix  IDENTIFIER
    ///     nilfix  "?"
    ///     nilfix  STRING_LITERAL
    ///     nilfix  CHAR_LITERAL
    ///     nilfix  INT_LITERAL
    ///     nilfix  FLOAT_LITERAL
    ///
    ///     infixr  "."             80  ::= record-elim
    /// }
    /// ```
    fn parse_arg_term(&mut self, right_prec: Prec) -> Result<Term<'file>, Diagnostic<FileSpan>> {
        // Use Top-Down Operator Precedence Parsing (a.k.a. Pratt Parsing) to
        // recognise the term syntax. This is not yet abstracted out into a more
        // general form.

        let token = self.advance().ok_or_else(
            || Diagnostic::new_error("unexpected EOF"), // FIXME: Spanned diagnostic
        )?;

        // Prefix operators
        let mut term = match (token.kind, token.src.slice) {
            (TokenKind::Identifier, _) => Ok(Term::Var(self.parse_var(token)?)),
            (TokenKind::Question, _) => self.parse_hole(token),
            (TokenKind::StringLiteral, _) => {
                let (kind, literal) = self.parse_string_literal(token)?;
                Ok(Term::LiteralIntro(kind, literal))
            },
            (TokenKind::CharLiteral, _) => {
                let (kind, literal) = self.parse_char_literal(token)?;
                Ok(Term::LiteralIntro(kind, literal))
            },
            (TokenKind::IntLiteral, _) => {
                let (kind, literal) = self.parse_int_literal(token)?;
                Ok(Term::LiteralIntro(kind, literal))
            },
            (TokenKind::FloatLiteral, _) => {
                let (kind, literal) = self.parse_float_literal(token)?;
                Ok(Term::LiteralIntro(kind, literal))
            },
            (TokenKind::Open(DelimKind::Paren), _) => self.parse_parens(token),
            (TokenKind::Keyword, "Type") => self.parse_universe(token),
            (_, _) => Err(Diagnostic::new_error("expected a term")
                .with_label(Label::new_primary(token.span()).with_message("term expected here"))),
        }?;

        // Infix operators
        while let Some(token) = self.peek() {
            match token.kind {
                TokenKind::Dot if right_prec < 80 => {
                    let token = self.advance().unwrap();
                    term = self.parse_record_elim(term, token)?;
                },
                _ => break,
            }
        }

        Ok(term)
    }

    /// Parse the trailing part of a variable.
    fn parse_var(
        &mut self,
        token: Token<'file>,
    ) -> Result<SpannedString<'file>, Diagnostic<FileSpan>> {
        Ok(token.src)
    }

    /// Parse the trailing part of a hole.
    fn parse_hole(&mut self, token: Token<'file>) -> Result<Term<'file>, Diagnostic<FileSpan>> {
        Ok(Term::Hole(token.span()))
    }

    /// Parse the trailing part of a string literal.
    fn parse_string_literal(
        &mut self,
        token: Token<'file>,
    ) -> Result<(LiteralKind, SpannedString<'file>), Diagnostic<FileSpan>> {
        Ok((LiteralKind::String, token.src))
    }

    /// Parse the trailing part of a character literal.
    fn parse_char_literal(
        &mut self,
        token: Token<'file>,
    ) -> Result<(LiteralKind, SpannedString<'file>), Diagnostic<FileSpan>> {
        Ok((LiteralKind::Char, token.src))
    }

    /// Parse the trailing part of a integer literal.
    fn parse_int_literal(
        &mut self,
        token: Token<'file>,
    ) -> Result<(LiteralKind, SpannedString<'file>), Diagnostic<FileSpan>> {
        Ok((LiteralKind::Int, token.src))
    }

    /// Parse the trailing part of a floating point literal.
    fn parse_float_literal(
        &mut self,
        token: Token<'file>,
    ) -> Result<(LiteralKind, SpannedString<'file>), Diagnostic<FileSpan>> {
        Ok((LiteralKind::Float, token.src))
    }

    /// Parse the trailing part of a function introduction.
    ///
    /// ```text
    /// fun-ty  ::= type-param+ "->" term(50 - 1)
    ///
    /// type-param  ::= "(" IDENTIFIER+ ":" term(0) ")"
    ///               | "{" IDENTIFIER+ (":" term(0))? "}"
    ///               | "{{" IDENTIFIER ":" term(0) "}}"
    /// ```
    fn parse_fun_ty(
        &mut self,
        start_token: Token<'file>,
    ) -> Result<Term<'file>, Diagnostic<FileSpan>> {
        let mut params = Vec::new();

        loop {
            if let Some(start_param_token) = self.try_match(TokenKind::Open(DelimKind::Paren)) {
                let mut param_names = Vec::new();
                while let Some(param_name) = self.try_identifier() {
                    param_names.push(param_name);
                }
                if param_names.is_empty() {
                    return Err(Diagnostic::new_error("expected at least one parameter")
                        .with_label(Label::new_primary(start_param_token.span()).with_message(
                            "at least one parameter was expected after this parenthesis",
                        )));
                }

                self.expect_match(TokenKind::Colon)?;
                let param_ty = self.parse_term(Prec(0))?;
                let end_param_token = self.expect_match(TokenKind::Close(DelimKind::Paren))?;
                let param_span = FileSpan::merge(start_param_token.span(), end_param_token.span());

                params.push(TypeParam::Explicit(param_span, param_names, param_ty));
            } else if let Some(start_param_token) =
                self.try_match(TokenKind::Open(DelimKind::Brace))
            {
                if self.try_match(TokenKind::Open(DelimKind::Brace)).is_some() {
                    let param_name = self.expect_identifier()?;
                    self.expect_match(TokenKind::Colon)?;
                    let param_ty = self.parse_term(Prec(0))?;
                    self.expect_match(TokenKind::Close(DelimKind::Brace))?;
                    let end_param_token = self.expect_match(TokenKind::Close(DelimKind::Brace))?;
                    let param_span =
                        FileSpan::merge(start_param_token.span(), end_param_token.span());

                    params.push(TypeParam::Instance(param_span, param_name, param_ty));
                } else {
                    let mut param_names = Vec::new();
                    while let Some(param_name) = self.try_identifier() {
                        param_names.push(param_name);
                    }
                    if param_names.is_empty() {
                        return Err(Diagnostic::new_error("expected at least one parameter")
                            .with_label(
                                Label::new_primary(start_param_token.span()).with_message(
                                    "at least one parameter was expected after this brace",
                                ),
                            ));
                    }

                    let param_ty = match self.try_match(TokenKind::Colon) {
                        Some(_) => Some(self.parse_term(Prec(0))?),
                        None => None,
                    };

                    let end_param_token = self.expect_match(TokenKind::Close(DelimKind::Brace))?;
                    let param_span =
                        FileSpan::merge(start_param_token.span(), end_param_token.span());

                    params.push(TypeParam::Implicit(param_span, param_names, param_ty));
                }
            } else {
                break;
            }
        }

        if params.is_empty() {
            return Err(
                Diagnostic::new_error("expected at least one parameter").with_label(
                    Label::new_primary(start_token.span())
                        .with_message("at least one parameter was expected after this keyword"),
                ),
            );
        }

        self.expect_match(TokenKind::RArrow)?;
        let body_ty = self.parse_term(Prec(50 - 1))?;
        let span = FileSpan::merge(start_token.span(), body_ty.span());

        Ok(Term::FunType(span, params, Box::new(body_ty)))
    }

    /// Parse the trailing part of a function introduction.
    ///
    /// ```text
    /// fun-intro ::= intro-param+ "=>" term(0)
    /// ```
    fn parse_fun_intro(
        &mut self,
        start_token: Token<'file>,
    ) -> Result<Term<'file>, Diagnostic<FileSpan>> {
        let params = self.parse_intro_params()?;
        if params.is_empty() {
            return Err(
                Diagnostic::new_error("expected at least one parameters").with_label(
                    Label::new_primary(start_token.span())
                        .with_message("at least one parameter was expected after this keyword"),
                ),
            );
        }
        self.expect_match(TokenKind::RFatArrow)?;
        let body = self.parse_term(Prec(0))?;
        let span = FileSpan::merge(start_token.span(), body.span());

        Ok(Term::FunIntro(span, params, Box::new(body)))
    }

    /// Parse the trailing part of a parenthesis grouping.
    ///
    /// ```text
    /// parens ::= term(0) ")"
    /// ```
    fn parse_parens(
        &mut self,
        start_token: Token<'file>,
    ) -> Result<Term<'file>, Diagnostic<FileSpan>> {
        let term = self.parse_term(Prec(0))?;
        let end_token = self.expect_match(TokenKind::Close(DelimKind::Paren))?;
        let span = FileSpan::merge(start_token.span(), end_token.span());

        Ok(Term::Parens(span, Box::new(term)))
    }

    /// Parse the trailing part of a record type.
    ///
    /// ```text
    /// record-type         ::= "{" (record-type-field ";")* record-type-field? "}"
    /// record-type-field   ::= DOC_COMMENT* IDENTIFIER ":" term(0)
    /// ```
    fn parse_record_ty(
        &mut self,
        start_token: Token<'file>,
    ) -> Result<Term<'file>, Diagnostic<FileSpan>> {
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
                    let end_token = self.expect_match(TokenKind::Close(DelimKind::Brace))?;
                    let span = FileSpan::merge(start_token.span(), end_token.span());

                    return Ok(Term::RecordType(span, fields));
                }
            } else {
                break;
            }
        }

        let end_token = self.expect_match(TokenKind::Close(DelimKind::Brace))?;
        let span = FileSpan::merge(start_token.span(), end_token.span());

        Ok(Term::RecordType(span, fields))
    }

    /// Parse the trailing part of a record introduction.
    ///
    /// ```text
    /// record-intro        ::= "{" (record-intro-field ";")* record-intro-field? "}"
    /// record-intro-field  ::= IDENTIFIER
    ///                       | IDENTIFIER intro-param* (":" term(0))? "=" term(0)
    /// ```
    fn parse_record_intro(
        &mut self,
        start_token: Token<'file>,
    ) -> Result<Term<'file>, Diagnostic<FileSpan>> {
        let mut fields = Vec::new();

        self.expect_match(TokenKind::Open(DelimKind::Brace))?;

        while let Some(label) = self.try_identifier() {
            let params = self.parse_intro_params()?;

            // TODO: implement punned fields

            let body_ty = match self.try_match(TokenKind::Colon) {
                None => None,
                Some(_) => Some(self.parse_term(Prec(0))?),
            };

            self.expect_match(TokenKind::Equals)?;
            let body = self.parse_term(Prec(0))?;

            fields.push(RecordIntroField::Explicit {
                label,
                params,
                body_ty,
                body,
            });

            if self.try_match(TokenKind::Semicolon).is_some() {
                continue;
            } else {
                let end_token = self.expect_match(TokenKind::Close(DelimKind::Brace))?;
                let span = FileSpan::merge(start_token.span(), end_token.span());

                return Ok(Term::RecordIntro(span, fields));
            }
        }

        let end_token = self.expect_match(TokenKind::Close(DelimKind::Brace))?;
        let span = FileSpan::merge(start_token.span(), end_token.span());

        Ok(Term::RecordIntro(span, fields))
    }

    /// Parse the trailing part of a let expression.
    ///
    /// ```text
    /// let-expr ::= item+ "in" term(0)
    /// ```
    fn parse_let_expr(
        &mut self,
        start_token: Token<'file>,
    ) -> Result<Term<'file>, Diagnostic<FileSpan>> {
        let mut items = Vec::new();
        while self.is_peek_match(ItemStart) {
            items.push(self.parse_item()?);
        }
        if items.is_empty() {
            return Err(
                Diagnostic::new_error("expected at least one item").with_label(
                    Label::new_primary(start_token.span())
                        .with_message("at least one item was expected after this keyword"),
                ),
            );
        }

        self.expect_match(Keyword("in"))?;
        let body_term = self.parse_term(Prec(0))?;

        let span = FileSpan::merge(start_token.span(), body_term.span());

        Ok(Term::Let(span, items, Box::new(body_term)))
    }

    /// Parse the trailing part of an if expression.
    ///
    /// ```text
    /// if-expr ::= term(0) "then" term(0) "else" term(0)
    /// ```
    fn parse_if_expr(
        &mut self,
        start_token: Token<'file>,
    ) -> Result<Term<'file>, Diagnostic<FileSpan>> {
        let condition = self.parse_term(Prec(0))?;
        self.expect_match(Keyword("then"))?;
        let consequent = self.parse_term(Prec(0))?;
        self.expect_match(Keyword("else"))?;
        let alternative = self.parse_term(Prec(0))?;

        let span = FileSpan::merge(start_token.span(), alternative.span());

        Ok(Term::If(
            span,
            Box::new(condition),
            Box::new(consequent),
            Box::new(alternative),
        ))
    }

    /// Parse the trailing part of a case expression.
    ///
    /// ```text
    /// case-expr   ::= arg-term(0)* "{" (case-clause ";")* case-clause? "}"
    /// case-clause ::= intro-param+ "=>" term(0)
    /// ```
    fn parse_case_expr(
        &mut self,
        start_token: Token<'file>,
    ) -> Result<Term<'file>, Diagnostic<FileSpan>> {
        let mut scrutinees = Vec::new();
        while self.is_peek_match(ScrutineeStart) {
            scrutinees.push(self.parse_arg_term(Prec(0))?);
        }

        self.expect_match(TokenKind::Open(DelimKind::Brace))?;

        let mut clauses = Vec::new();
        while !self.is_peek_match(TokenKind::Close(DelimKind::Brace)) {
            let params = self.parse_intro_params()?;
            if params.is_empty() {
                return Err(
                    Diagnostic::new_error("expected at least one parameter")
                        .with_label(Label::new_primary(start_token.span()).with_message(
                            "at least one parameter was expected after this keyword",
                        )),
                );
            }

            self.expect_match(TokenKind::RFatArrow)?;

            let body = self.parse_term(Prec(0))?;

            clauses.push((params, body));

            if self.try_match(TokenKind::Semicolon).is_some() {
                continue;
            } else {
                let end_token = self.expect_match(TokenKind::Close(DelimKind::Brace))?;
                let span = FileSpan::merge(start_token.span(), end_token.span());

                return Ok(Term::Case(span, scrutinees, clauses));
            }
        }

        let end_token = self.expect_match(TokenKind::Close(DelimKind::Brace))?;
        let span = FileSpan::merge(start_token.span(), end_token.span());

        Ok(Term::Case(span, scrutinees, clauses))
    }

    /// Parse the trailing part of a universe.
    ///
    /// ```text
    /// universe ::= ("^" INT_LITERAL)?
    /// ```
    fn parse_universe(
        &mut self,
        start_token: Token<'file>,
    ) -> Result<Term<'file>, Diagnostic<FileSpan>> {
        if self.try_match(TokenKind::Caret).is_some() {
            let level_token = self.expect_match(TokenKind::IntLiteral)?;
            let span = FileSpan::merge(start_token.span(), level_token.span());

            Ok(Term::Universe(span, Some(level_token.src)))
        } else {
            Ok(Term::Universe(start_token.span(), None))
        }
    }

    /// Parse the trailing part of a primitive.
    ///
    /// ```text
    /// primitive ::= STRING_LITERAL
    /// ```
    fn parse_prim(
        &mut self,
        start_token: Token<'file>,
    ) -> Result<Term<'file>, Diagnostic<FileSpan>> {
        let name_token = self.expect_match(TokenKind::StringLiteral)?;
        let span = FileSpan::merge(start_token.span(), name_token.span());

        Ok(Term::Prim(span, name_token.src))
    }

    /// Parse the trailing part of a record elimination.
    ///
    /// ```text
    /// record-elim ::= IDENTIFIER
    /// ```
    fn parse_record_elim(
        &mut self,
        lhs: Term<'file>,
        _start_token: Token<'file>,
    ) -> Result<Term<'file>, Diagnostic<FileSpan>> {
        let label = self.expect_identifier()?;
        Ok(Term::RecordElim(Box::new(lhs), label))
    }

    /// Parse the trailing part of a type annotation.
    ///
    /// ```text
    /// ann ::= term(20 - 1)
    /// ```
    fn parse_ann(
        &mut self,
        lhs: Term<'file>,
        _start_token: Token<'file>,
    ) -> Result<Term<'file>, Diagnostic<FileSpan>> {
        let rhs = self.parse_term(Prec(20 - 1))?;

        Ok(Term::Ann(Box::new(lhs), Box::new(rhs)))
    }

    /// Parse the trailing part of a function arrow.
    ///
    /// ```text
    /// fun-arrow-type ::= term(50 - 1)
    /// ```
    fn parse_fun_arrow_type(
        &mut self,
        lhs: Term<'file>,
        _start_token: Token<'file>,
    ) -> Result<Term<'file>, Diagnostic<FileSpan>> {
        let rhs = self.parse_term(Prec(50 - 1))?;

        Ok(Term::FunArrowType(Box::new(lhs), Box::new(rhs)))
    }

    /// Parse the trailing part of a function elimination.
    ///
    /// ```text
    /// fun-elim    ::= arg*
    /// ```
    fn parse_fun_elim(&mut self, lhs: Term<'file>) -> Result<Term<'file>, Diagnostic<FileSpan>> {
        let mut args = Vec::new();
        while self.is_peek_match(ArgParamStart) {
            args.push(self.parse_arg()?);
        }

        if args.is_empty() {
            Ok(lhs)
        } else {
            Ok(Term::FunElim(Box::new(lhs), args))
        }
    }
}
