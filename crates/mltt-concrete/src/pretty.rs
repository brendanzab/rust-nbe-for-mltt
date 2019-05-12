use pretty::{BoxDoc, Doc};

use crate::{
    Arg, Declaration, Definition, IntroParam, Item, Pattern, RecordIntroField, RecordTypeField,
    SpannedString, Term, TypeParam,
};

impl<'file> Item<'file> {
    /// Convert the item into a pretty-printable document.
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            Item::Declaration(decl) => decl.to_doc(),
            Item::Definition(defn) => defn.to_doc(),
        }
    }
}

impl<'file> Declaration<'file> {
    /// Convert the declaration into a pretty-printable document.
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        let docs = Doc::concat(
            self.docs
                .iter()
                .map(|doc| doc.to_doc().append(Doc::newline())),
        );

        Doc::nil()
            .append(docs)
            .append(self.name.to_doc())
            .append(Doc::space())
            .append(":")
            .append(Doc::space())
            .append(self.body_ty.to_doc())
            .append(";")
    }
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
            .append(self.name.to_doc())
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

impl<'file> SpannedString<'file> {
    /// Convert the string into a pretty-printable document.
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        Doc::text(self.slice)
    }
}

impl<'file> Pattern<'file> {
    /// Convert the pattern into a pretty-printable document.
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            Pattern::Var(name) => name.to_doc(),
            Pattern::LiteralIntro(_, literal) => literal.to_doc(),
        }
    }
}

impl<'file> TypeParam<'file> {
    /// Convert the parameter into a pretty-printable document.
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
            TypeParam::Instance(_, param_label, term) => Doc::nil()
                .append("{{")
                .append(param_label.to_doc())
                .append(Doc::space())
                .append(":")
                .append(Doc::space())
                .append(term.to_doc())
                .append("}}"),
        }
    }
}

impl<'file> IntroParam<'file> {
    /// Convert the parameter into a pretty-printable document.
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
            IntroParam::Instance(_, param_label, None) => Doc::nil()
                .append("{{")
                .append(param_label.to_doc())
                .append("}}"),
            IntroParam::Instance(_, param_label, Some(pattern)) => Doc::nil()
                .append("{{")
                .append(param_label.to_doc())
                .append(Doc::space())
                .append("=")
                .append(Doc::space())
                .append(pattern.to_doc())
                .append("}}"),
        }
    }
}

impl<'file> Arg<'file> {
    /// Convert the argument into a pretty-printable document.
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            Arg::Explicit(term) => term.to_doc(),
            Arg::Implicit(_, param_label, None) => {
                Doc::text("{").append(param_label.to_doc()).append("}")
            },
            Arg::Implicit(_, param_label, Some(term)) => Doc::nil()
                .append("{")
                .append(param_label.to_doc())
                .append(Doc::space())
                .append("=")
                .append(Doc::space())
                .append(term.to_doc())
                .append("}"),
            Arg::Instance(_, param_label, None) => {
                Doc::text("{{").append(param_label.to_doc()).append("}}")
            },
            Arg::Instance(_, param_label, Some(term)) => Doc::nil()
                .append("{{")
                .append(param_label.to_doc())
                .append(Doc::space())
                .append("=")
                .append(Doc::space())
                .append(term.to_doc())
                .append("}}"),
        }
    }
}

impl<'file> RecordTypeField<'file> {
    /// Convert the field into a pretty-printable document.
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

impl<'file> RecordIntroField<'file> {
    /// Convert the field into a pretty-printable document.
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

impl<'file> Term<'file> {
    /// Convert the term into a pretty-printable document.
    pub fn to_doc(&self) -> Doc<'_, BoxDoc<'_, ()>> {
        match self {
            Term::Var(name) => name.to_doc(),
            Term::Prim(_, name) => Doc::nil()
                .append("primitive")
                .append(Doc::space())
                .append(name.to_doc()),
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
            Term::If(_, condition, consequent, alternative) => Doc::nil()
                .append("if")
                .append(Doc::space())
                .append(condition.to_doc())
                .append(Doc::space())
                .append("then")
                .append(Doc::space())
                .append(consequent.to_doc())
                .append(Doc::space())
                .append("else")
                .append(Doc::space())
                .append(alternative.to_doc()),
            Term::Case(_, scrutinee, clauses) => {
                let clauses = Doc::intersperse(
                    clauses.iter().map(|(param, body)| {
                        Doc::nil()
                            .append(param.to_doc())
                            .append(Doc::space())
                            .append("=>")
                            .append(Doc::space())
                            .append(body.to_doc())
                    }),
                    Doc::text(";").append(Doc::space()),
                );

                Doc::nil()
                    .append("case")
                    .append(Doc::space())
                    .append(scrutinee.to_doc())
                    .append(Doc::space())
                    .append("{")
                    .append(Doc::space())
                    .append(clauses)
                    .append(Doc::space())
                    .append("}")
            },
            Term::LiteralIntro(_, literal) => literal.to_doc(),
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
            Term::Universe(_, Some(level)) => Doc::text("Type^").append(level.to_doc()),
        }
    }
}
