//! The concrete syntax of the MLTT language.
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
use std::borrow::Cow;
use std::fmt;

pub mod pretty;

/// Top-level items in a module.
#[derive(Debug, Clone, PartialEq)]
pub enum Item<'file> {
    /// Forward-declarations.
    Declaration(Declaration<'file>),
    /// Term definitions.
    Definition(Definition<'file>),
}

impl<'file> Item<'file> {
    /// Returns `true` if the item is a definition.
    pub fn is_definition(&self) -> bool {
        match self {
            Item::Declaration(_) => false,
            Item::Definition(_) => true,
        }
    }

    pub fn span(&self) -> FileSpan {
        match self {
            Item::Declaration(declaration) => declaration.span(),
            Item::Definition(definition) => definition.span(),
        }
    }
}

/// Forward-declarations.
#[derive(Debug, Clone, PartialEq)]
pub struct Declaration<'file> {
    pub docs: Vec<SpannedString<'file>>,
    pub label: SpannedString<'file>,
    pub body_ty: Term<'file>,
}

impl<'file> Declaration<'file> {
    pub fn span(&self) -> FileSpan {
        FileSpan::merge(self.label.span(), self.body_ty.span())
    }
}

/// Term definitions.
#[derive(Debug, Clone, PartialEq)]
pub struct Definition<'file> {
    pub docs: Vec<SpannedString<'file>>,
    pub label: SpannedString<'file>,
    pub params: Vec<IntroParam<'file>>,
    pub body_ty: Option<Term<'file>>,
    pub body: Term<'file>,
}

impl<'file> Definition<'file> {
    pub fn span(&self) -> FileSpan {
        FileSpan::merge(self.label.span(), self.body.span())
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
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
}

impl<'file> fmt::Debug for SpannedString<'file> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{span:?} {slice:?}",
            span = self.span(),
            slice = self.slice,
        )
    }
}

impl<'file> fmt::Display for SpannedString<'file> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.slice.fmt(f)
    }
}

impl<'file> Into<String> for SpannedString<'file> {
    fn into(self) -> String {
        self.to_string()
    }
}

impl<'a, 'file> Into<String> for &'a SpannedString<'file> {
    fn into(self) -> String {
        self.to_string()
    }
}

/// Concrete patterns.
#[derive(Debug, Clone, PartialEq)]
pub enum Pattern<'file> {
    /// Variable patterns.
    Var(SpannedString<'file>),
    /// Literal introductions.
    LiteralIntro(LiteralKind, SpannedString<'file>),
    // TODO:
    // /// Patterns with an explicit type annotation.
    // Ann(Box<Pattern<'file>>, Box<Term<'file>>),
}

impl<'file> Pattern<'file> {
    pub fn span(&self) -> FileSpan {
        match self {
            Pattern::Var(name) => name.span(),
            Pattern::LiteralIntro(_, literal) => literal.span(),
        }
    }
}

impl<'file> fmt::Display for Pattern<'file> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_doc().group().pretty(1_000_000_000).fmt(f)
    }
}

/// The kind of literal.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum LiteralKind {
    /// String literals.
    String,
    /// Char literals.
    Char,
    /// Integer literals.
    Int,
    /// Floating point literals.
    Float,
}

impl LiteralKind {
    /// Returns a string description of the literal kind.
    pub fn description(self) -> &'static str {
        match self {
            LiteralKind::String => "string",
            LiteralKind::Char => "character",
            LiteralKind::Int => "integer",
            LiteralKind::Float => "floating point",
        }
    }
}

/// A group of parameters to be used in a function type.
#[derive(Debug, Clone, PartialEq)]
pub enum TypeParam<'file> {
    Explicit(FileSpan, Vec<SpannedString<'file>>, Term<'file>),
    Implicit(FileSpan, Vec<SpannedString<'file>>, Option<Term<'file>>),
    Instance(FileSpan, SpannedString<'file>, Term<'file>),
}

impl<'file> TypeParam<'file> {
    pub fn span(&self) -> FileSpan {
        match self {
            TypeParam::Explicit(span, _, _)
            | TypeParam::Implicit(span, _, _)
            | TypeParam::Instance(span, _, _) => *span,
        }
    }
}

impl<'file> fmt::Display for TypeParam<'file> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_doc().group().pretty(1_000_000_000).fmt(f)
    }
}

/// A parameter pattern to be used in a function introduction.
#[derive(Debug, Clone, PartialEq)]
pub enum IntroParam<'file> {
    Explicit(Pattern<'file>),
    Implicit(FileSpan, SpannedString<'file>, Option<Pattern<'file>>),
    Instance(FileSpan, SpannedString<'file>, Option<Pattern<'file>>),
}

impl<'file> IntroParam<'file> {
    pub fn span(&self) -> FileSpan {
        match self {
            IntroParam::Explicit(pattern) => pattern.span(),
            IntroParam::Implicit(span, _, _) | IntroParam::Instance(span, _, _) => *span,
        }
    }
}

impl<'file> fmt::Display for IntroParam<'file> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_doc().group().pretty(1_000_000_000).fmt(f)
    }
}

/// An argument passed to a function.
#[derive(Debug, Clone, PartialEq)]
pub enum Arg<'file> {
    Explicit(Term<'file>),
    Implicit(FileSpan, SpannedString<'file>, Option<Term<'file>>),
    Instance(FileSpan, SpannedString<'file>, Option<Term<'file>>),
}

impl<'file> Arg<'file> {
    pub fn span(&self) -> FileSpan {
        match self {
            Arg::Explicit(term) => term.span(),
            Arg::Implicit(span, _, _) | Arg::Instance(span, _, _) => *span,
        }
    }

    pub fn desugar_arg_term(&self) -> Cow<'_, Term<'file>> {
        match self {
            Arg::Explicit(term) => Cow::Borrowed(term),
            Arg::Implicit(_, label, term) | Arg::Instance(_, label, term) => match term {
                None => Cow::Owned(Term::Var(label.clone())),
                Some(term) => Cow::Borrowed(term),
            },
        }
    }
}

impl<'file> fmt::Display for Arg<'file> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_doc().group().pretty(1_000_000_000).fmt(f)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordTypeField<'file> {
    pub docs: Vec<SpannedString<'file>>,
    pub label: SpannedString<'file>,
    pub ann: Term<'file>,
}

impl<'file> fmt::Display for RecordTypeField<'file> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_doc().group().pretty(1_000_000_000).fmt(f)
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
    /// Desugar punned fields.
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

    pub fn span(&self) -> FileSpan {
        match self {
            RecordIntroField::Punned { label } => label.span(),
            RecordIntroField::Explicit { label, body, .. } => {
                FileSpan::merge(label.span(), body.span())
            },
        }
    }
}

impl<'file> fmt::Display for RecordIntroField<'file> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_doc().group().pretty(1_000_000_000).fmt(f)
    }
}

/// Concrete terms.
#[derive(Debug, Clone, PartialEq)]
pub enum Term<'file> {
    /// Variables
    Var(SpannedString<'file>),
    /// Primitives
    Prim(FileSpan, SpannedString<'file>),
    /// Holes
    Hole(FileSpan),

    /// A parenthesized term
    Parens(FileSpan, Box<Term<'file>>),
    /// A term that is explicitly annotated with a type
    Ann(Box<Term<'file>>, Box<Term<'file>>),
    /// Let bindings
    Let(FileSpan, Vec<Item<'file>>, Box<Term<'file>>),
    /// If expressions
    If(
        FileSpan,
        Box<Term<'file>>,
        Box<Term<'file>>,
        Box<Term<'file>>,
    ),
    /// Case expressions
    Case(
        FileSpan,
        Box<Term<'file>>,
        Vec<(Pattern<'file>, Term<'file>)>,
    ),

    /// Literal introductions.
    LiteralIntro(LiteralKind, SpannedString<'file>),

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
    Universe(FileSpan, Option<SpannedString<'file>>),
}

impl<'file> Term<'file> {
    pub fn span(&self) -> FileSpan {
        match self {
            Term::Var(name) => name.span(),
            Term::Prim(span, _) => *span,
            Term::Hole(span) => *span,
            Term::Parens(span, _) => *span,
            Term::Ann(term, term_ty) => FileSpan::merge(term.span(), term_ty.span()),
            Term::Let(span, _, _) => *span,
            Term::If(span, _, _, _) => *span,
            Term::Case(span, _, _) => *span,
            Term::LiteralIntro(_, literal) => literal.span(),
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
}

impl<'file> fmt::Display for Term<'file> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.to_doc().group().pretty(1_000_000_000).fmt(f)
    }
}
