//! The concrete syntax tree for the language
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

use pretty::{BoxDoc, Doc};
use std::fmt;

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
}

/// Forward-declarations
#[derive(Debug, Clone, PartialEq)]
pub struct Declaration {
    pub docs: Vec<String>,
    pub name: String,
    pub ann: Term,
}

/// Term definitions
#[derive(Debug, Clone, PartialEq)]
pub struct Definition {
    pub docs: Vec<String>,
    pub name: String,
    pub patterns: Vec<Pattern>,
    pub body_ty: Option<Term>,
    pub body: Term,
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
#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq)]
pub struct RecordTypeField {
    pub docs: Vec<String>,
    pub label: String,
    pub ann: Term,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RecordIntroField {
    Punned {
        label: String,
    },
    Explicit {
        label: String,
        patterns: Vec<Pattern>,
        term_ty: Option<Term>,
        term: Term,
    },
}

/// Concrete terms
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// Variables
    Var(String),
    /// Literals
    Literal(Literal),
    /// Let bindings
    Let(String, Box<Term>, Box<Term>),
    /// A term that is explicitly annotated with a type
    Ann(Box<Term>, Box<Term>),
    /// A parenthesized term
    Parens(Box<Term>),

    /// Dependent function type
    ///
    /// Also known as a _pi type_ or _dependent product type_.
    FunType(Vec<(Vec<String>, Term)>, Box<Term>),
    /// Non-dependent function types
    FunArrowType(Box<Term>, Box<Term>),
    /// Introduce a function
    ///
    /// Also known as a _lambda expression_ or _anonymous function_.
    FunIntro(Vec<Pattern>, Box<Term>),
    /// Apply a function to an argument
    FunApp(Box<Term>, Vec<Term>),

    /// Dependent record type
    RecordType(Vec<RecordTypeField>),
    /// Record introduction
    RecordIntro(Vec<RecordIntroField>),
    /// Record projection
    RecordProj(Box<Term>, String),

    /// Universe of types
    Universe(Option<u32>),
}

impl Term {
    /// Convert the term into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        // Using precedence climbing (mirroring the language grammar) in
        // order to cut down on extraneous parentheses.

        fn to_doc_term(term: &Term) -> Doc<'_, BoxDoc<'_, ()>> {
            match term {
                Term::Ann(term, ann) => Doc::nil()
                    .append(to_doc_expr(term))
                    .append(Doc::space())
                    .append(":")
                    .append(Doc::space())
                    .append(to_doc_app(ann)),
                _ => to_doc_expr(term),
            }
        }

        fn to_doc_expr(term: &Term) -> Doc<'_, BoxDoc<'_, ()>> {
            match term {
                Term::Let(def_name, def, body) => Doc::nil()
                    .append("let")
                    .append(Doc::space())
                    .append(def_name)
                    .append(Doc::space())
                    .append("=")
                    .append(Doc::space())
                    .append(to_doc_app(def))
                    .append(Doc::space())
                    .append("in")
                    .append(Doc::space())
                    .append(to_doc_term(body)),
                Term::FunType(params, body_ty) => Doc::nil()
                    .append(Doc::group(
                        Doc::nil()
                            .append("Fun")
                            .append(Doc::space())
                            .append(Doc::intersperse(
                                params.iter().map(|(param_names, param_ty)| {
                                    Doc::nil()
                                        .append("(")
                                        .append(Doc::intersperse(
                                            param_names.iter().map(Doc::text),
                                            Doc::space(),
                                        ))
                                        .append(Doc::space())
                                        .append(":")
                                        .append(Doc::space())
                                        .append(to_doc_term(param_ty))
                                        .append(")")
                                }),
                                Doc::space(),
                            )),
                    ))
                    .append(Doc::space())
                    .append("->")
                    .append(Doc::space())
                    .append(to_doc_app(body_ty)),
                Term::FunIntro(param_names, body) => Doc::nil()
                    .append("fun")
                    .append(Doc::space())
                    .append(Doc::intersperse(
                        param_names.iter().map(Pattern::to_doc),
                        Doc::space(),
                    ))
                    .append(Doc::space())
                    .append("=>")
                    .append(Doc::space())
                    .append(to_doc_app(body)),
                Term::RecordType(ty_fields) if ty_fields.is_empty() => Doc::text("Record {}"),
                Term::RecordType(ty_fields) => Doc::nil()
                    .append("Record")
                    .append(Doc::space())
                    .append("{")
                    .append(Doc::newline())
                    .append(
                        Doc::intersperse(
                            ty_fields.iter().map(|ty_field| {
                                Doc::nil()
                                    .append(&ty_field.label)
                                    .append(Doc::space())
                                    .append(":")
                                    .append(Doc::space())
                                    .append(to_doc_app(&ty_field.ann))
                                    .append(";")
                            }),
                            Doc::newline(),
                        )
                        .nest(4),
                    )
                    .append(Doc::newline())
                    .append("}"),
                Term::RecordIntro(intro_fields) if intro_fields.is_empty() => {
                    Doc::text("record {}")
                },
                Term::RecordIntro(intro_fields) => Doc::nil()
                    .append("record")
                    .append(Doc::space())
                    .append("{")
                    .append(Doc::newline())
                    .append(
                        Doc::intersperse(
                            intro_fields.iter().map(|intro_field| match intro_field {
                                RecordIntroField::Punned { label } => Doc::text(label).append(";"),
                                RecordIntroField::Explicit {
                                    label,
                                    patterns,
                                    term_ty,
                                    term,
                                } => Doc::nil()
                                    .append(label)
                                    .append(Doc::space())
                                    .append(Doc::intersperse(
                                        patterns.iter().map(Pattern::to_doc),
                                        Doc::space(),
                                    ))
                                    .append(Doc::space())
                                    .append(term_ty.as_ref().map_or(Doc::nil(), |term_ty| {
                                        Doc::nil()
                                            .append(":")
                                            .append(Doc::space())
                                            .append(to_doc_app(term_ty))
                                            .append(Doc::space())
                                    }))
                                    .append("=")
                                    .append(Doc::space())
                                    .append(to_doc_app(term))
                                    .append(";"),
                            }),
                            Doc::newline(),
                        )
                        .nest(4),
                    )
                    .append(Doc::newline())
                    .append("}"),
                _ => to_doc_arrow(term),
            }
        }

        fn to_doc_arrow(term: &Term) -> Doc<'_, BoxDoc<'_, ()>> {
            match term {
                Term::FunArrowType(param_ty, body_ty) => Doc::nil()
                    .append(to_doc_app(param_ty))
                    .append(Doc::space())
                    .append("->")
                    .append(Doc::space())
                    .append(to_doc_app(body_ty)),
                _ => to_doc_app(term),
            }
        }

        fn to_doc_app(term: &Term) -> Doc<'_, BoxDoc<'_, ()>> {
            match term {
                Term::FunApp(fun, args) => Doc::nil()
                    .append(to_doc_term(fun))
                    .append(Doc::space())
                    .append(Doc::intersperse(
                        args.iter().map(to_doc_atomic),
                        Doc::space(),
                    )),
                _ => to_doc_atomic(term),
            }
        }

        fn to_doc_atomic(term: &Term) -> Doc<'_, BoxDoc<'_, ()>> {
            match term {
                Term::Var(name) => Doc::as_string(name),
                Term::Literal(literal) => literal.to_doc(),
                Term::Parens(term) => Doc::text("(").append(to_doc_term(term)).append(")"),
                Term::RecordProj(record, label) => to_doc_atomic(record).append(".").append(label),
                Term::Universe(None) => Doc::text("Type"),
                Term::Universe(Some(level)) => Doc::text("Type^").append(Doc::as_string(level)),
                _ => Doc::text("(").append(to_doc_term(term)).append(")"),
            }
        }

        to_doc_term(self)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_doc().group().pretty(1_000_000_000).fmt(f)
    }
}
