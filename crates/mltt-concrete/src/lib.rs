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

use mltt_span::{ByteIndex, ByteSize, FileId, FileSpan};
use pretty::{BoxDoc, Doc};
use std::borrow::Cow;
use std::fmt;

/// Top-level items in a module
#[derive(Debug, Clone, PartialEq)]
pub enum Item<'file> {
    /// Forward-declarations
    Declaration(Declaration<'file>),
    /// Term definitions
    Definition(Definition<'file>),
}

impl<'file> Item<'file> {
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
pub struct Declaration<'file> {
    pub docs: Vec<SpannedString<'file>>,
    pub label: SpannedString<'file>,
    pub body_ty: Term<'file>,
}

impl<'file> Declaration<'file> {
    /// Convert the declaration into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        let docs = Doc::concat(
            self.docs
                .iter()
                .map(|doc| doc.to_doc().append(Doc::newline())),
        );

        Doc::nil()
            .append(docs)
            .append(self.label.to_doc())
            .append(Doc::space())
            .append(":")
            .append(Doc::space())
            .append(self.body_ty.to_doc())
            .append(";")
    }
}

/// Term definitions
#[derive(Debug, Clone, PartialEq)]
pub struct Definition<'file> {
    pub docs: Vec<SpannedString<'file>>,
    pub label: SpannedString<'file>,
    pub params: Vec<IntroParam<'file>>,
    pub body_ty: Option<Term<'file>>,
    pub body: Term<'file>,
}

impl<'file> Definition<'file> {
    /// Convert the definition into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        let docs = Doc::concat(
            self.docs
                .iter()
                .map(|doc| doc.to_doc().append(Doc::newline())),
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
            .append(self.label.to_doc())
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

#[derive(Debug, Clone, PartialEq)]
pub struct SpannedString<'file> {
    pub source: FileId,
    pub start: ByteIndex,
    pub slice: &'file str,
}

impl<'file> SpannedString<'file> {
    pub fn new(
        source: FileId,
        start: impl Into<ByteIndex>,
        slice: &'file str,
    ) -> SpannedString<'file> {
        SpannedString {
            source,
            start: start.into(),
            slice,
        }
    }

    pub fn span(&self) -> FileSpan {
        FileSpan::new(
            self.source,
            self.start,
            self.start + ByteSize::from_str_len_utf8(&self.slice),
        )
    }

    /// Convert the string into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::text(self.slice)
    }
}

impl<'file> fmt::Display for SpannedString<'file> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.slice.fmt(f)
    }
}

/// Concrete patterns
#[derive(Debug, Clone, PartialEq)]
pub enum Pattern<'file> {
    /// Variable patterns
    Var(SpannedString<'file>),
    // TODO:
    // /// Literal patterns
    // Literal(Literal<'file>),
    // /// Patterns with an explicit type annotation
    // Ann(Box<Pattern<'file>>, Box<Term<'file>>),
    // /// Pair patterns
    // PairIntro(Box<Pattern<'file>>, Box<Pattern<'file>>),
}

impl<'file> Pattern<'file> {
    pub fn span(&self) -> FileSpan {
        match self {
            Pattern::Var(name) => name.span(),
        }
    }

    /// Convert the pattern into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            Pattern::Var(name) => name.to_doc(),
        }
    }
}

impl<'file> fmt::Display for Pattern<'file> {
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
pub struct Literal<'file> {
    /// The span where this literal was introduced
    pub span: FileSpan,
    /// The kind of literal
    pub kind: LiteralKind,
    /// We use a string here, because we'll be using type information to do
    /// further parsing of these. For example we need to know the size of an
    /// integer literal before we can know whether the literal is overflowing.
    pub slice: &'file str,
}

impl<'file> Literal<'file> {
    pub fn span(&self) -> FileSpan {
        self.span
    }

    /// Convert the literal into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::as_string(self.slice)
    }
}

/// A group of parameters to be used in a function type
#[derive(Debug, Clone, PartialEq)]
pub enum TypeParam<'file> {
    Explicit(FileSpan, Vec<SpannedString<'file>>, Term<'file>),
    Implicit(FileSpan, Vec<SpannedString<'file>>, Option<Term<'file>>),
}

impl<'file> TypeParam<'file> {
    pub fn span(&self) -> FileSpan {
        match self {
            TypeParam::Explicit(span, _, _) | TypeParam::Implicit(span, _, _) => *span,
        }
    }

    /// Convert the parameter into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            TypeParam::Explicit(_, param_names, param_ty) => Doc::nil()
                .append("(")
                .append(Doc::intersperse(
                    param_names.iter().map(SpannedString::to_doc),
                    Doc::space(),
                ))
                .append(Doc::space())
                .append(":")
                .append(Doc::space())
                .append(param_ty.to_doc())
                .append(")"),
            TypeParam::Implicit(_, param_labels, None) => Doc::nil()
                .append("{")
                .append(Doc::intersperse(
                    param_labels.iter().map(SpannedString::to_doc),
                    Doc::space(),
                ))
                .append("}"),
            TypeParam::Implicit(_, param_labels, Some(term)) => Doc::nil()
                .append("{")
                .append(Doc::intersperse(
                    param_labels.iter().map(SpannedString::to_doc),
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
pub enum IntroParam<'file> {
    Explicit(Pattern<'file>),
    Implicit(FileSpan, SpannedString<'file>, Option<Pattern<'file>>),
}

impl<'file> IntroParam<'file> {
    pub fn span(&self) -> FileSpan {
        match self {
            IntroParam::Explicit(pattern) => pattern.span(),
            IntroParam::Implicit(span, _, _) => *span,
        }
    }

    /// Convert the parameter into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            IntroParam::Explicit(pattern) => pattern.to_doc(),
            IntroParam::Implicit(_, param_label, None) => Doc::nil()
                .append("{")
                .append(param_label.to_doc())
                .append("}"),
            IntroParam::Implicit(_, param_label, Some(pattern)) => Doc::nil()
                .append("{")
                .append(param_label.to_doc())
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
pub enum Arg<'file> {
    Explicit(Term<'file>),
    Implicit(FileSpan, SpannedString<'file>, Option<Term<'file>>),
}

impl<'file> Arg<'file> {
    pub fn span(&self) -> FileSpan {
        match self {
            Arg::Explicit(term) => term.span(),
            Arg::Implicit(span, _, _) => *span,
        }
    }

    /// Convert the argument into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            Arg::Explicit(term) => term.to_doc(),
            Arg::Implicit(_, param_label, None) => {
                Doc::text("{").append(param_label.to_doc()).append(")")
            },
            Arg::Implicit(_, param_label, Some(term)) => Doc::nil()
                .append("{")
                .append(param_label.to_doc())
                .append(Doc::space())
                .append("=")
                .append(Doc::space())
                .append(term.to_doc())
                .append("}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordTypeField<'file> {
    pub docs: Vec<SpannedString<'file>>,
    pub label: SpannedString<'file>,
    pub ann: Term<'file>,
}

impl<'file> RecordTypeField<'file> {
    /// Convert the field into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::nil()
            .append(self.label.to_doc())
            .append(Doc::space())
            .append(":")
            .append(Doc::space())
            .append(self.ann.to_doc())
            .append(";")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum RecordIntroField<'file> {
    Punned {
        label: SpannedString<'file>,
    },
    Explicit {
        label: SpannedString<'file>,
        params: Vec<IntroParam<'file>>,
        body_ty: Option<Term<'file>>,
        body: Term<'file>,
    },
}

impl<'file> RecordIntroField<'file> {
    /// Desugar punned fields
    pub fn desugar(
        &self,
    ) -> (
        &SpannedString<'file>,
        &[IntroParam<'file>],
        std::option::Option<&Term<'file>>,
        std::borrow::Cow<'_, Term<'file>>,
    ) {
        match self {
            RecordIntroField::Punned { label } => {
                (label, &[][..], None, Cow::Owned(Term::Var(label.clone())))
            },
            RecordIntroField::Explicit {
                label,
                params,
                body_ty,
                body,
            } => (label, &params[..], body_ty.as_ref(), Cow::Borrowed(body)),
        }
    }

    /// Convert the field into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            RecordIntroField::Punned { label } => label.to_doc().append(";"),
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
                    .append(label.to_doc())
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
pub enum Term<'file> {
    /// Variables
    Var(SpannedString<'file>),
    /// Holes
    Hole(FileSpan),

    /// A parenthesized term
    Parens(FileSpan, Box<Term<'file>>),
    /// A term that is explicitly annotated with a type
    Ann(Box<Term<'file>>, Box<Term<'file>>),
    /// Let bindings
    Let(FileSpan, Vec<Item<'file>>, Box<Term<'file>>),

    /// Literals
    Literal(Literal<'file>),

    /// Dependent function type
    ///
    /// Also known as a _pi type_ or _dependent product type_.
    FunType(FileSpan, Vec<TypeParam<'file>>, Box<Term<'file>>),
    /// Non-dependent function types
    FunArrowType(Box<Term<'file>>, Box<Term<'file>>),
    /// Introduce a function
    ///
    /// Also known as a _lambda expression_ or _anonymous function_.
    FunIntro(FileSpan, Vec<IntroParam<'file>>, Box<Term<'file>>),
    /// Eliminate a function by applying it to an argument
    FunElim(Box<Term<'file>>, Vec<Arg<'file>>),

    /// Dependent record type
    RecordType(FileSpan, Vec<RecordTypeField<'file>>),
    /// Record introduction
    RecordIntro(FileSpan, Vec<RecordIntroField<'file>>),
    /// Eliminate a record by projecting on it
    RecordElim(Box<Term<'file>>, SpannedString<'file>),

    /// Universe of types
    Universe(FileSpan, Option<(FileSpan, u32)>),
}

impl<'file> Term<'file> {
    pub fn span(&self) -> FileSpan {
        match self {
            Term::Var(name) => name.span(),
            Term::Hole(span) => *span,
            Term::Parens(span, _) => *span,
            Term::Ann(term, term_ty) => FileSpan::merge(term.span(), term_ty.span()),
            Term::Let(span, _, _) => *span,
            Term::Literal(literal) => literal.span(),
            Term::FunType(span, _, _) => *span,
            Term::FunArrowType(param_ty, body_ty) => {
                FileSpan::merge(param_ty.span(), body_ty.span())
            },
            Term::FunIntro(span, _, _) => *span,
            Term::FunElim(fun, args) => {
                let mut span = fun.span();
                if let Some(last_arg) = args.last() {
                    span = FileSpan::merge(span, last_arg.span());
                }
                span
            },
            Term::RecordType(span, _) => *span,
            Term::RecordIntro(span, _) => *span,
            Term::RecordElim(record, label) => FileSpan::merge(record.span(), label.span()),
            Term::Universe(span, _) => *span,
        }
    }

    /// Convert the term into a pretty-printable document
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            Term::Var(name) => name.to_doc(),
            Term::Hole(_) => Doc::text("?"),
            Term::Parens(_, term) => Doc::text("(").append(term.to_doc()).append(")"),
            Term::Ann(term, ann) => Doc::nil()
                .append(term.to_doc())
                .append(Doc::space())
                .append(":")
                .append(Doc::space())
                .append(ann.to_doc()),
            Term::Let(_, items, body) => {
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
            Term::FunType(_, params, body_ty) => Doc::nil()
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
            Term::FunIntro(_, param_names, body) => Doc::nil()
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
            Term::RecordType(_, ty_fields) if ty_fields.is_empty() => Doc::text("Record {}"),
            Term::RecordType(_, ty_fields) => {
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
            Term::RecordIntro(_, intro_fields) if intro_fields.is_empty() => Doc::text("record {}"),
            Term::RecordIntro(_, intro_fields) => {
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
            Term::RecordElim(record, label) => record.to_doc().append(".").append(label.to_doc()),
            Term::Universe(_, None) => Doc::text("Type"),
            Term::Universe(_, Some((_, level))) => Doc::text("Type^").append(Doc::as_string(level)),
        }
    }
}

impl<'file> fmt::Display for Term<'file> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_doc().group().pretty(1_000_000_000).fmt(f)
    }
}
