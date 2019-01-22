//! The parser
//!
//! # Basic grammar (without precedences)
//!
//! ```text
//! module  ::= item*
//!
//! item    ::= DOC_COMMENT* IDENTIFIER ":" term ";"
//!           | DOC_COMMENT* IDENTIFIER IDENTIFIER* "=" term ";"
//!
//! term    ::= IDENTIFIER
//!           | STRING_LITERAL
//!           | CHAR_LITERAL
//!           | INT_LITERAL
//!           | FLOAT_LITERAL
//!           | "let" IDENTIFIER "=" term "in" term
//!           | term ":" term
//!           | "(" term ")"
//!           | ("(" IDENTIFIER+ ":" term ")")+ "->" term
//!           | term "->" term
//!           | "\\" IDENTIFIER+ "=>" term
//!           | term term
//!           | "(" ident ":" term ")" "*" term
//!           | "{" term "," term "}"
//!           | term "." "1"
//!           | term "." "2"
//!           | "Type" "^" INT_LITERAL
//! ```
//!
//! # Top-down precedence grammar
//!
//! ```text
//! module  ::= item*
//!
//! item    ::= DOC_COMMENT* IDENTIFIER ":" term(-1) ";"
//!           | DOC_COMMENT* IDENTIFIER IDENTIFIER* "=" term(-1) ";"
//!
//! app-term ::= term(_)+
//!
//! term(p) ::= operators(p) {
//!     prefix  "let"           ?   ::= IDENTIFIER "=" term(_) "in" term(_)
//!     prefix  "("             ?   ::= IDENTIFIER+ ":" term(_) ")" ("(" IDENTIFIER+ ":" term(_) ")")* "->" term(_)
//!                                   / IDENTIFIER ":" term(_) ")" "*" term(_)
//!                                   / term(_) ")"
//!     prefix  "\\"            ?   ::= IDENTIFIER+ "=>" term(_)
//!     prefix  "{"             ?   ::= term(_) "," term(_) "}"
//!     prefix  "Type"          ?   ::= "^" INT_LITERAL
//!     nilfix  IDENTIFIER
//!     nilfix  STRING_LITERAL
//!     nilfix  CHAR_LITERAL
//!     nilfix  INT_LITERAL
//!     nilfix  FLOAT_LITERAL
//!
//!     infixr  ":"             ?   ::= term(_)             precedence?
//!     infixl  "."             ?   ::= "1" | "2"           precedence?
//!     infixl  "->"            ?   ::= term(_)             precedence?
//!     infixl                  ?   ::= term(_)             precedence? FIXME: application?
//! }
//! ```
//!

use language_reporting::{Diagnostic, Label};
use mltt_concrete::syntax::concrete;
use mltt_span::{ByteIndex, ByteSize, File, FileSpan};
use std::iter::Peekable;

use crate::token::{Token, TokenTag};

/// The precedence or 'binding strength' of an infix operator
///
/// This controls how different operators should be prioritised in the absense
/// of parentheses. For example, if `*` has a greater precedence than `+`, then
/// `a * b + c` will be parsed as `(a * b) + c`.
///
/// https://en.wikipedia.org/wiki/Order_of_operations
pub struct Precedence(pub u32);

/// The associativity of an infix operator
///
/// This determines how to group operators of the same precedence in the absence
/// of parentheses.
///
/// For example, if `*` and `/` were of the same precedence, and left
/// associative then `a * b / c` would be grouped as `(a * b) / c`. If they were
/// both right associative, then they would be grouped as `a * (b / c)`.
/// Encountering operators of the same precedence but differing associativity
/// is regarded as an error.
///
/// https://en.wikipedia.org/wiki/Operator_associativity
pub enum Associativity {
    /// This operator associates to the left
    Left,
    /// This operator associates to the right
    Right,
}

pub struct InfixGrouping {
    pub precedence: Precedence,
    pub associativity: Associativity,
}

// type ParseFn<'file, Tokens, Output> =
//     fn(&mut Parser<'file, Tokens>) -> Result<Output, Diagnostic<FileSpan>>;

// pub struct InfixParseRule<'file, Tokens: Iterator> {
//     /// The parser to use if the operator is found in a prefix position, eg. `x - y`
//     ///
//     /// This is known as `led` or the 'left denotation' in many resources on
//     /// Pratt parsing.
//     pub parser: ParseFn<'file, Tokens, concrete::Term>,
//     /// The precedence of the operator
//     pub precedence: Precedence,
//     /// The associativity of the operator
//     pub associativity: Associativity,
// }

// pub struct PrefixParser<'file, Tokens: Iterator> {
//     /// The parser to use if the operator is found in a prefix position, eg. `-x`
//     ///
//     /// This is known as `nud` or the 'null denotation' in many resources on
//     /// Pratt parsing.
//     prefix: ParseFn<'file, Tokens, concrete::Term>,
// }

// - https://github.com/elm/parser/blob/master/src/Parser.elm
// - https://github.com/elm/parser/blob/master/src/Parser/Advanced.elm

trait Parser {
    type Input: Iterator;
    type Output;

    fn parse(&self, input: &mut Self::Input) -> Result<Self::Output, Diagnostic<FileSpan>>;
}

fn succeed<I: Iterator, A: Clone>(a: A) -> impl Parser<Input = I, Output = A> {
    struct Succeed<I, A>(A, std::marker::PhantomData<I>);

    impl<I, A> Parser for Succeed<I, A>
    where
        I: Iterator,
        A: Clone,
    {
        type Input = I;
        type Output = A;

        fn parse(&self, _input: &mut I) -> Result<A, Diagnostic<FileSpan>> {
            Ok(self.0.clone())
        }
    }

    Succeed::<I, A>(a, std::marker::PhantomData)
}

fn map<I, A, B>(
    p: impl Parser<Input = I, Output = A>,
    f: impl Fn(A) -> B,
) -> impl Parser<Input = I, Output = B>
where
    I: Iterator,
{
    struct Map<P, F>(P, F);

    impl<P, F, B> Parser for Map<P, F>
    where
        P: Parser,
        F: Fn(P::Output) -> B,
    {
        type Input = P::Input;
        type Output = B;

        fn parse(&self, input: &mut P::Input) -> Result<B, Diagnostic<FileSpan>> {
            Ok((self.1)(self.0.parse(input)?))
        }
    }

    Map(p, f)
}

struct PrefixRule {}
struct InfixRule {}

/// A parser that implements top-down operator precedence parsing (a.k.a. Pratt parsing)
struct PrecedenceParser<Input, Output> {
    marker: std::marker::PhantomData<(Input, Output)>,
    prefix_rules: Vec<PrefixRule>,
    infix_rules: Vec<InfixRule>,
}

impl<Input, Output> Parser for PrecedenceParser<Input, Output>
where
    Input: Iterator,
{
    type Input = Input;
    type Output = Output;

    fn parse<'file>(&self, input: &mut Input) -> Result<Output, Diagnostic<FileSpan>> {
        // advance
        // parse prefix rule for current token

        // while precedence > next token's infix precedence
        //     advance
        //     parse current infix rule

        // parse expression

        unimplemented!()
    }
}

impl<Input, Output> PrecedenceParser<Input, Output>
where
    Input: Iterator,
{
    fn add_prefix(
        &mut self,
        tag: TokenTag,
        prefix_parser: impl Parser<Input = Input, Output = Output>,
    ) {
        self.prefix_rules.push(PrefixRule {});
    }

    fn add_nilfix(&mut self, tag: TokenTag) {
        self.prefix_rules.push(PrefixRule {});
    }

    fn add_infix(&mut self) {
        self.infix_rules.push(InfixRule {});
    }

    fn add_infixr(&mut self, tag: TokenTag) {
        self.add_infix();
    }

    fn add_infixl(
        &mut self,
        tag: TokenTag,
        infix_parser: impl Parser<Input = Input, Output = Output>,
    ) {
        self.add_infix();
    }

    fn add_suffix(&mut self, tag: TokenTag) {
        self.add_infix();
    }
}

// self.add_prefix(TokenTag::Let, Parser::prefix_let);
// self.add_prefix(TokenTag::LParen, Parser::prefix_parens_or_binder_type);
// self.add_prefix(TokenTag::BSlash, Parser::prefix_fun_intro);
// self.add_prefix(TokenTag::LBRace, Parser::prefix_pair_intro);
// self.add_prefix(TokenTag::Type, Parser::prefix_universe);
// self.add_nilfix(TokenTag::Identifier, Parser::prefix_var);
// self.add_nilfix(TokenTag::StringLiteral, Parser::prefix_string);
// self.add_nilfix(TokenTag::CharLiteral, Parser::prefix_char);
// self.add_nilfix(TokenTag::IntLiteral, Parser::prefix_int);
// self.add_nilfix(TokenTag::FloatLiteral, Parser::prefix_float);
// self.add_infixr(TokenTag::Colon, Precedence(???), Parser::infix_annotation);
// self.add_infixl(TokenTag::Dot, Precedence(???), Parser::infix_projection);
// self.add_infixl(TokenTag::Arrow, Precedence(???), Parser::infix_fun_arrow_type);

/// A language parser
pub struct TopParser<'file, Tokens: Iterator> {
    tokens: Peekable<Tokens>,
    current: Option<Token<'file>>,
}

impl<'file, Tokens> TopParser<'file, Tokens>
where
    Tokens: Iterator<Item = Result<Token<'file>, Diagnostic<FileSpan>>>,
{
    /// Create a new parser from an iterator of tokens
    pub fn new(tokens: Tokens) -> TopParser<'file, Tokens> {
        TopParser {
            tokens: tokens.peekable(),
            current: None,
        }
    }

    /// Return the next token from the lexer
    fn peek(&mut self) -> Result<Option<Token<'file>>, Diagnostic<FileSpan>> {
        match self.tokens.peek() {
            Some(&Ok(ref token)) => Ok(Some(token.clone())),
            Some(&Err(ref err)) => Err(err.clone()),
            None => Ok(None),
        }
    }

    /// Bump the current position in the source string by one character,
    /// returning the current character and byte position.
    fn advance(&mut self) -> Result<Option<Token<'file>>, Diagnostic<FileSpan>> {
        match self.tokens.next() {
            None => self.current = None,
            Some(item) => self.current = Some(item?),
        }
        Ok(self.current.clone())
    }

    /// Parse a term
    fn parse_term(&mut self) -> Result<concrete::Term, Diagnostic<FileSpan>> {
        match self.advance()? {
            Some(token) => match (token.tag, token.slice) {
                (TokenTag::Identifier, _) => {
                    self.advance()?;
                    Ok(concrete::Term::Var(token.slice.to_owned()))
                },
                (TokenTag::StringLiteral, _) => unimplemented!("string literal"),
                (TokenTag::CharLiteral, _) => unimplemented!("char literal"),
                (TokenTag::IntLiteral, _) => unimplemented!("int literal"),
                (TokenTag::FloatLiteral, _) => unimplemented!("float literal"),
                _ => unimplemented!(),
            },
            // FIXME: span at EOF
            None => Err(Diagnostic::new_error("unexpected end of file")),
        }
    }
}
