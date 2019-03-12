//! The concrete syntax of the MLTT language
//!
//! This could also be referred to as a 'parse tree'. We should aim to be able
//! to reproduce the source code that the user typed in based on this syntax
//! tree.
//!
//! In the future we might want to use a different representation that makes
//! incremental updates faster. [Swift's parse tree] seems like an interesting
//! approach to this problem, but comes with the downside of extra memory
//! overhead and complexity.
//!
//! [Swift's parse tree]: https://github.com/apple/swift/tree/daf7d249a528ceea3c6b8ff8f5226be9af67f85c/lib/Syntax

#![warn(rust_2018_idioms)]

use pretty::{BoxDoc, Doc};
use std::fmt;

pub mod resugar;

/// Top-level items in a module
#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    /// Forward-declarations
    Declaration(Declaration),
    /// Term definitions
    Definition(Definition),
}

impl Item {
    /// Returns `true` if the item is a definition
    pub fn is_definition(&self) -> bool {
        match self {
            Item::Declaration(_) => false,
            Item::Definition(_) => true,
        }
    }

    /// Convert the item into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            Item::Declaration(declaration) => declaration.to_doc(),
            Item::Definition(definition) => definition.to_doc(),
        }
    }
}

/// Forward-declarations
#[derive(Debug, Clone, PartialEq)]
pub struct Declaration {
    pub docs: Vec<String>,
    pub label: String,
    pub body_ty: Term,
}

impl Declaration {
    /// Convert the declaration into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        let docs = Doc::concat(
            self.docs
                .iter()
                .map(|doc| Doc::text(doc).append(Doc::newline())),
        );

        Doc::nil()
            .append(docs)
            .append(&self.label)
            .append(Doc::space())
            .append(":")
            .append(Doc::space())
            .append(self.body_ty.to_doc())
            .append(";")
    }
}

/// Term definitions
#[derive(Debug, Clone, PartialEq)]
pub struct Definition {
    pub docs: Vec<String>,
    pub label: String,
    pub params: Vec<IntroParam>,
    pub body_ty: Option<Term>,
    pub body: Term,
}

impl Definition {
    /// Convert the definition into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        let docs = Doc::concat(
            self.docs
                .iter()
                .map(|doc| Doc::text(doc).append(Doc::newline())),
        );
        let params = Doc::intersperse(self.params.iter().map(IntroParam::to_doc), Doc::space());
        let body_ty = self.body_ty.as_ref().map_or(Doc::nil(), |body_ty| {
            Doc::nil()
                .append(":")
                .append(Doc::space())
                .append(body_ty.to_doc())
                .append(Doc::space())
        });

        Doc::nil()
            .append(docs)
            .append(&self.label)
            .append(Doc::space())
            .append(params)
            .append(Doc::space())
            .append(body_ty)
            .append("=")
            .append(Doc::space())
            .append(self.body.to_doc())
            .append(";")
    }
}

/// Concrete patterns
#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    /// Variable patterns
    Var(String),
    // TODO:
    // /// Literal patterns
    // Literal(Literal),
    // /// Patterns with an explicit type annotation
    // Ann(Box<Pattern>, Box<Term>),
    // /// Pair patterns
    // PairIntro(Box<Pattern>, Box<Pattern>),
}

impl Pattern {
    /// Convert the pattern into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            Pattern::Var(name) => Doc::as_string(name),
        }
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_doc().group().pretty(1_000_000_000).fmt(f)
    }
}

/// The kind of literal
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum LiteralKind {
    /// String literals
    String,
    /// Char literals
    Char,
    /// Integer literals
    Int,
    /// Floating point literals
    Float,
}

impl LiteralKind {
    /// Returns a string description of the literal kind
    pub fn description(self) -> &'static str {
        match self {
            LiteralKind::String => "string",
            LiteralKind::Char => "character",
            LiteralKind::Int => "integer",
            LiteralKind::Float => "floating point",
        }
    }
}

/// Concrete literals
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Literal {
    /// The kind of literal
    pub kind: LiteralKind,
    /// We use a string here, because we'll be using type information to do
    /// further parsing of these. For example we need to know the size of an
    /// integer literal before we can know whether the literal is overflowing.
    pub value: String,
}

impl Literal {
    /// Convert the literal into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::as_string(&self.value)
    }
}

/// A group of parameters to be used in a function type
#[derive(Debug, Clone, PartialEq)]
pub enum TypeParam {
    Explicit(Vec<String>, Term),
    Implicit(Vec<String>, Option<Term>),
}

impl TypeParam {
    /// Convert the parameter into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            TypeParam::Explicit(param_names, param_ty) => Doc::nil()
                .append("(")
                .append(Doc::intersperse(
                    param_names.iter().map(Doc::text),
                    Doc::space(),
                ))
                .append(Doc::space())
                .append(":")
                .append(Doc::space())
                .append(param_ty.to_doc())
                .append(")"),
            TypeParam::Implicit(param_labels, None) => Doc::nil()
                .append("{")
                .append(Doc::intersperse(
                    param_labels.iter().map(Doc::text),
                    Doc::space(),
                ))
                .append("}"),
            TypeParam::Implicit(param_labels, Some(term)) => Doc::nil()
                .append("{")
                .append(Doc::intersperse(
                    param_labels.iter().map(Doc::text),
                    Doc::space(),
                ))
                .append(Doc::space())
                .append(":")
                .append(Doc::space())
                .append(term.to_doc())
                .append("}"),
        }
    }
}

/// A parameter pattern to be used in a function introduction
#[derive(Debug, Clone, PartialEq)]
pub enum IntroParam {
    Explicit(Pattern),
    Implicit(String, Option<Pattern>),
}

impl IntroParam {
    /// Convert the parameter into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            IntroParam::Explicit(pattern) => pattern.to_doc(),
            IntroParam::Implicit(param_label, None) => {
                Doc::nil().append("{").append(param_label).append("}")
            },
            IntroParam::Implicit(param_label, Some(pattern)) => Doc::nil()
                .append("{")
                .append(param_label)
                .append(Doc::space())
                .append("=")
                .append(Doc::space())
                .append(pattern.to_doc())
                .append("}"),
        }
    }
}

/// An argument passed to a function
#[derive(Debug, Clone, PartialEq)]
pub enum Arg {
    Explicit(Term),
    Implicit(String, Option<Term>),
}

impl Arg {
    /// Convert the argument into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            Arg::Explicit(term) => term.to_doc(),
            Arg::Implicit(param_label, None) => Doc::text("{").append(param_label).append(")"),
            Arg::Implicit(param_label, Some(term)) => Doc::nil()
                .append("{")
                .append(param_label)
                .append(Doc::space())
                .append("=")
                .append(Doc::space())
                .append(term.to_doc())
                .append("}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordTypeField {
    pub docs: Vec<String>,
    pub label: String,
    pub ann: Term,
}

impl RecordTypeField {
    /// Convert the field into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::nil()
            .append(&self.label)
            .append(Doc::space())
            .append(":")
            .append(Doc::space())
            .append(self.ann.to_doc())
            .append(";")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum RecordIntroField {
    Punned {
        label: String,
    },
    Explicit {
        label: String,
        params: Vec<IntroParam>,
        body_ty: Option<Term>,
        body: Term,
    },
}

impl RecordIntroField {
    /// Convert the field into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            RecordIntroField::Punned { label } => Doc::text(label).append(";"),
            RecordIntroField::Explicit {
                label,
                params,
                body_ty,
                body,
            } => {
                let params = Doc::intersperse(params.iter().map(IntroParam::to_doc), Doc::space());
                let body_ty = body_ty.as_ref().map_or(Doc::nil(), |body_ty| {
                    Doc::nil()
                        .append(":")
                        .append(Doc::space())
                        .append(body_ty.to_doc())
                        .append(Doc::space())
                });

                Doc::nil()
                    .append(label)
                    .append(Doc::space())
                    .append(params)
                    .append(Doc::space())
                    .append(body_ty)
                    .append("=")
                    .append(Doc::space())
                    .append(body.to_doc())
                    .append(";")
            },
        }
    }
}

/// Concrete terms
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// Variables
    Var(String),
    /// Holes
    Hole,

    /// A parenthesized term
    Parens(Box<Term>),
    /// A term that is explicitly annotated with a type
    Ann(Box<Term>, Box<Term>),
    /// Let bindings
    Let(Vec<Item>, Box<Term>),

    /// Literals
    Literal(Literal),

    /// Dependent function type
    ///
    /// Also known as a _pi type_ or _dependent product type_.
    FunType(Vec<TypeParam>, Box<Term>),
    /// Non-dependent function types
    FunArrowType(Box<Term>, Box<Term>),
    /// Introduce a function
    ///
    /// Also known as a _lambda expression_ or _anonymous function_.
    FunIntro(Vec<IntroParam>, Box<Term>),
    /// Eliminate a function by applying it to an argument
    FunElim(Box<Term>, Vec<Arg>),

    /// Dependent record type
    RecordType(Vec<RecordTypeField>),
    /// Record introduction
    RecordIntro(Vec<RecordIntroField>),
    /// Eliminate a record by projecting on it
    RecordElim(Box<Term>, String),

    /// Universe of types
    Universe(Option<u32>),
}

impl Term {
    /// Convert the term into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            Term::Var(name) => Doc::as_string(name),
            Term::Hole => Doc::text("?"),
            Term::Parens(term) => Doc::text("(").append(term.to_doc()).append(")"),
            Term::Ann(term, ann) => Doc::nil()
                .append(term.to_doc())
                .append(Doc::space())
                .append(":")
                .append(Doc::space())
                .append(ann.to_doc()),
            Term::Let(items, body) => {
                let items = Doc::intersperse(items.iter().map(Item::to_doc), Doc::newline());

                Doc::nil()
                    .append("let")
                    .append(Doc::space())
                    .append(Doc::newline())
                    .append(items.nest(4))
                    .append(Doc::newline())
                    .append(Doc::space())
                    .append("in")
                    .append(Doc::space())
                    .append(body.to_doc())
            },
            Term::Literal(literal) => literal.to_doc(),
            Term::FunType(params, body_ty) => Doc::nil()
                .append("Fun")
                .append(Doc::space())
                .append(Doc::intersperse(
                    params.iter().map(TypeParam::to_doc),
                    Doc::space(),
                ))
                .append(Doc::space())
                .append("->")
                .append(Doc::space())
                .append(body_ty.to_doc()),
            Term::FunArrowType(param_ty, body_ty) => Doc::nil()
                .append(param_ty.to_doc())
                .append(Doc::space())
                .append("->")
                .append(Doc::space())
                .append(body_ty.to_doc()),
            Term::FunIntro(param_names, body) => Doc::nil()
                .append("fun")
                .append(Doc::space())
                .append(Doc::intersperse(
                    param_names.iter().map(IntroParam::to_doc),
                    Doc::space(),
                ))
                .append(Doc::space())
                .append("=>")
                .append(Doc::space())
                .append(body.to_doc()),
            Term::FunElim(fun, args) => {
                let args = Doc::intersperse(args.iter().map(Arg::to_doc), Doc::space());

                Doc::nil()
                    .append(fun.to_doc())
                    .append(Doc::space())
                    .append(args)
            },
            Term::RecordType(ty_fields) if ty_fields.is_empty() => Doc::text("Record {}"),
            Term::RecordType(ty_fields) => {
                let ty_fields = Doc::intersperse(
                    ty_fields.iter().map(RecordTypeField::to_doc),
                    Doc::newline(),
                );

                Doc::nil()
                    .append("Record")
                    .append(Doc::space())
                    .append("{")
                    .append(Doc::newline())
                    .append(ty_fields.nest(4))
                    .append(Doc::newline())
                    .append("}")
            },
            Term::RecordIntro(intro_fields) if intro_fields.is_empty() => Doc::text("record {}"),
            Term::RecordIntro(intro_fields) => {
                let intro_fields = Doc::intersperse(
                    intro_fields.iter().map(RecordIntroField::to_doc),
                    Doc::newline(),
                );

                Doc::nil()
                    .append("record")
                    .append(Doc::space())
                    .append("{")
                    .append(Doc::newline())
                    .append(intro_fields.nest(4))
                    .append(Doc::newline())
                    .append("}")
            },
            Term::RecordElim(record, label) => record.to_doc().append(".").append(label),
            Term::Universe(None) => Doc::text("Type"),
            Term::Universe(Some(level)) => Doc::text("Type^").append(Doc::as_string(level)),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_doc().group().pretty(1_000_000_000).fmt(f)
    }
}
