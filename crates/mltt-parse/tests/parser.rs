use language_reporting::termcolor::{ColorChoice, StandardStream};
use mltt_concrete::{
    Arg, Definition, IntroParam, Item, Literal, LiteralKind, Pattern, RecordIntroField,
    RecordTypeField, SpannedString, Term, TypeParam,
};
use mltt_parse::lexer::Lexer;
use mltt_parse::parser::parse_term;
use mltt_span::FileSpan;
use mltt_span::Files;
use pretty_assertions::assert_eq;

macro_rules! test_term {
    ($src:expr, |$file_id:ident| $expected_term:expr,) => {{
        test_term!($src, |$file_id| $expected_term);
    }};
    ($src:expr, |$file_id:ident| $expected_term:expr) => {{
        let _ = pretty_env_logger::try_init();

        let mut files = Files::new();
        let $file_id = files.add("test", $src);
        let term = match parse_term(Lexer::new(&files[$file_id])) {
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
    test_term!("var", |file_id| Term::Var(SpannedString::new(
        file_id, 0, "var",
    )));
}

#[test]
fn hole() {
    test_term!("?", |file_id| Term::Hole(FileSpan::new(file_id, 0, 1)));
}

#[test]
fn string_literal() {
    test_term!("\"value\"", |file_id| Term::Literal(Literal {
        kind: LiteralKind::String,
        src: SpannedString::new(file_id, 0, "\"value\""),
    }));
}

#[test]
fn char_literal() {
    test_term!("'\\n'", |file_id| Term::Literal(Literal {
        kind: LiteralKind::Char,
        src: SpannedString::new(file_id, 0, "'\\n'"),
    }));
}

#[test]
fn int_literal() {
    test_term!("0xA_F00", |file_id| Term::Literal(Literal {
        kind: LiteralKind::Int,
        src: SpannedString::new(file_id, 0, "0xA_F00"),
    }));
}

#[test]
fn float_literal() {
    test_term!("0.3_46e_23", |file_id| Term::Literal(Literal {
        kind: LiteralKind::Float,
        src: SpannedString::new(file_id, 0, "0.3_46e_23"),
    }));
}

#[test]
fn let_expr() {
    test_term!("let var = Type; in var", |file_id| Term::Let(
        FileSpan::new(file_id, 0, 22),
        vec![Item::Definition(Definition {
            docs: Vec::new(),
            label: SpannedString::new(file_id, 4, "var"),
            params: Vec::new(),
            body_ty: None,
            body: Term::Universe(FileSpan::new(file_id, 10, 14), None),
        })],
        Box::new(Term::Var(SpannedString::new(file_id, 19, "var"))),
    ),);
}

#[test]
fn if_expr() {
    test_term!("if foo then bar else baz", |file_id| Term::If(
        FileSpan::new(file_id, 0, 24),
        Box::new(Term::Var(SpannedString::new(file_id, 3, "foo"))),
        Box::new(Term::Var(SpannedString::new(file_id, 12, "bar"))),
        Box::new(Term::Var(SpannedString::new(file_id, 21, "baz"))),
    ),);
}

#[test]
fn parens() {
    test_term!("(foo)", |file_id| Term::Parens(
        FileSpan::new(file_id, 0, 5),
        Box::new(Term::Var(SpannedString::new(file_id, 1, "foo"))),
    ));
}

#[test]
fn fun_ty() {
    test_term!(
        r"Fun (x y : Type) (z : Type) -> x",
        |file_id| Term::FunType(
            FileSpan::new(file_id, 0, 32),
            vec![
                TypeParam::Explicit(
                    FileSpan::new(file_id, 4, 16),
                    vec![
                        SpannedString::new(file_id, 5, "x"),
                        SpannedString::new(file_id, 7, "y"),
                    ],
                    Term::Universe(FileSpan::new(file_id, 11, 15), None),
                ),
                TypeParam::Explicit(
                    FileSpan::new(file_id, 17, 27),
                    vec![SpannedString::new(file_id, 18, "z")],
                    Term::Universe(FileSpan::new(file_id, 22, 26), None),
                ),
            ],
            Box::new(Term::Var(SpannedString::new(file_id, 31, "x"))),
        ),
    );
}

#[test]
fn fun_ty_implicit() {
    test_term!(r"Fun {x y : Type} {z} -> x", |file_id| Term::FunType(
        FileSpan::new(file_id, 0, 25),
        vec![
            TypeParam::Implicit(
                FileSpan::new(file_id, 4, 16),
                vec![
                    SpannedString::new(file_id, 5, "x"),
                    SpannedString::new(file_id, 7, "y"),
                ],
                Some(Term::Universe(FileSpan::new(file_id, 11, 15), None)),
            ),
            TypeParam::Implicit(
                FileSpan::new(file_id, 17, 20),
                vec![SpannedString::new(file_id, 18, "z")],
                None,
            ),
        ],
        Box::new(Term::Var(SpannedString::new(file_id, 24, "x"))),
    ));
}

#[test]
fn fun_ty_instance() {
    test_term!(r"Fun {{A : Foo}} -> A", |file_id| Term::FunType(
        FileSpan::new(file_id, 0, 20),
        vec![TypeParam::Instance(
            FileSpan::new(file_id, 4, 15),
            SpannedString::new(file_id, 6, "A"),
            Term::Var(SpannedString::new(file_id, 10, "Foo")),
        )],
        Box::new(Term::Var(SpannedString::new(file_id, 19, "A"))),
    ));
}

#[test]
fn fun_arrow_type() {
    test_term!("Foo -> Bar", |file_id| Term::FunArrowType(
        Box::new(Term::Var(SpannedString::new(file_id, 0, "Foo"))),
        Box::new(Term::Var(SpannedString::new(file_id, 7, "Bar"))),
    ));
}

#[test]
fn fun_arrow_type_nested() {
    test_term!("Foo -> Bar -> Baz", |file_id| Term::FunArrowType(
        Box::new(Term::Var(SpannedString::new(file_id, 0, "Foo"))),
        Box::new(Term::FunArrowType(
            Box::new(Term::Var(SpannedString::new(file_id, 7, "Bar"))),
            Box::new(Term::Var(SpannedString::new(file_id, 14, "Baz"))),
        )),
    ));
}

#[test]
fn fun_arrow_type_fun_app() {
    test_term!("Option A -> Option B -> Option C", |file_id| {
        Term::FunArrowType(
            Box::new(Term::FunElim(
                Box::new(Term::Var(SpannedString::new(file_id, 0, "Option"))),
                vec![Arg::Explicit(Term::Var(SpannedString::new(
                    file_id, 7, "A",
                )))],
            )),
            Box::new(Term::FunArrowType(
                Box::new(Term::FunElim(
                    Box::new(Term::Var(SpannedString::new(file_id, 12, "Option"))),
                    vec![Arg::Explicit(Term::Var(SpannedString::new(
                        file_id, 19, "B",
                    )))],
                )),
                Box::new(Term::FunElim(
                    Box::new(Term::Var(SpannedString::new(file_id, 24, "Option"))),
                    vec![Arg::Explicit(Term::Var(SpannedString::new(
                        file_id, 31, "C",
                    )))],
                )),
            )),
        )
    });
}

#[test]
fn fun_intro() {
    test_term!(r"fun x => x", |file_id| Term::FunIntro(
        FileSpan::new(file_id, 0, 10),
        vec![IntroParam::Explicit(Pattern::Var(SpannedString::new(
            file_id, 4, "x",
        )))],
        Box::new(Term::Var(SpannedString::new(file_id, 9, "x"))),
    ));
}

#[test]
fn fun_intro_multi_params() {
    test_term!(r"fun x y z => x", |file_id| Term::FunIntro(
        FileSpan::new(file_id, 0, 14),
        vec![
            IntroParam::Explicit(Pattern::Var(SpannedString::new(file_id, 4, "x"))),
            IntroParam::Explicit(Pattern::Var(SpannedString::new(file_id, 6, "y"))),
            IntroParam::Explicit(Pattern::Var(SpannedString::new(file_id, 8, "z"))),
        ],
        Box::new(Term::Var(SpannedString::new(file_id, 13, "x"))),
    ));
}

#[test]
fn fun_intro_multi_params_implicit() {
    test_term!(r"fun x {y} {z = zz} => x", |file_id| Term::FunIntro(
        FileSpan::new(file_id, 0, 23),
        vec![
            IntroParam::Explicit(Pattern::Var(SpannedString::new(file_id, 4, "x"))),
            IntroParam::Implicit(
                FileSpan::new(file_id, 6, 9),
                SpannedString::new(file_id, 7, "y"),
                None,
            ),
            IntroParam::Implicit(
                FileSpan::new(file_id, 10, 18),
                SpannedString::new(file_id, 11, "z"),
                Some(Pattern::Var(SpannedString::new(file_id, 15, "zz")))
            ),
        ],
        Box::new(Term::Var(SpannedString::new(file_id, 22, "x"))),
    ));
}

#[test]
fn fun_intro_multi_params_instance() {
    test_term!(r"fun x {{y}} {{z = zz}} => x", |file_id| Term::FunIntro(
        FileSpan::new(file_id, 0, 27),
        vec![
            IntroParam::Explicit(Pattern::Var(SpannedString::new(file_id, 4, "x"))),
            IntroParam::Instance(
                FileSpan::new(file_id, 6, 11),
                SpannedString::new(file_id, 8, "y"),
                None,
            ),
            IntroParam::Instance(
                FileSpan::new(file_id, 12, 22),
                SpannedString::new(file_id, 14, "z"),
                Some(Pattern::Var(SpannedString::new(file_id, 18, "zz")))
            ),
        ],
        Box::new(Term::Var(SpannedString::new(file_id, 26, "x"))),
    ));
}

#[test]
fn fun_app_1() {
    test_term!(r"foo arg", |file_id| Term::FunElim(
        Box::new(Term::Var(SpannedString::new(file_id, 0, "foo"))),
        vec![Arg::Explicit(Term::Var(SpannedString::new(
            file_id, 4, "arg",
        )))],
    ));
}

#[test]
fn fun_app_2a() {
    test_term!(r"foo arg1 arg2", |file_id| Term::FunElim(
        Box::new(Term::Var(SpannedString::new(file_id, 0, "foo"))),
        vec![
            Arg::Explicit(Term::Var(SpannedString::new(file_id, 4, "arg1"))),
            Arg::Explicit(Term::Var(SpannedString::new(file_id, 9, "arg2"))),
        ],
    ));
}

#[test]
fn fun_app_2b() {
    test_term!(r"foo (arg1) arg2.foo.bar arg3", |file_id| Term::FunElim(
        Box::new(Term::Var(SpannedString::new(file_id, 0, "foo"))),
        vec![
            Arg::Explicit(Term::Parens(
                FileSpan::new(file_id, 4, 10),
                Box::new(Term::Var(SpannedString::new(file_id, 5, "arg1")))
            )),
            Arg::Explicit(Term::RecordElim(
                Box::new(Term::RecordElim(
                    Box::new(Term::Var(SpannedString::new(file_id, 11, "arg2"))),
                    SpannedString::new(file_id, 16, "foo"),
                )),
                SpannedString::new(file_id, 20, "bar"),
            )),
            Arg::Explicit(Term::Var(SpannedString::new(file_id, 24, "arg3"))),
        ],
    ));
}

#[test]
fn fun_app_implicit() {
    test_term!(r"foo {arg1} {arg2 = arg2}", |file_id| Term::FunElim(
        Box::new(Term::Var(SpannedString::new(file_id, 0, "foo"))),
        vec![
            Arg::Implicit(
                FileSpan::new(file_id, 4, 10),
                SpannedString::new(file_id, 5, "arg1"),
                None,
            ),
            Arg::Implicit(
                FileSpan::new(file_id, 11, 24),
                SpannedString::new(file_id, 12, "arg2"),
                Some(Term::Var(SpannedString::new(file_id, 19, "arg2"))),
            ),
        ],
    ));
}

#[test]
fn fun_app_instance() {
    test_term!(r"foo {{arg1}} {{arg2 = arg2}}", |file_id| Term::FunElim(
        Box::new(Term::Var(SpannedString::new(file_id, 0, "foo"))),
        vec![
            Arg::Instance(
                FileSpan::new(file_id, 4, 12),
                SpannedString::new(file_id, 6, "arg1"),
                None,
            ),
            Arg::Instance(
                FileSpan::new(file_id, 13, 28),
                SpannedString::new(file_id, 15, "arg2"),
                Some(Term::Var(SpannedString::new(file_id, 22, "arg2"))),
            ),
        ],
    ));
}

#[test]
fn record_type() {
    test_term!("Record { x : Type; y : Type }", |file_id| Term::RecordType(
        FileSpan::new(file_id, 0, 29),
        vec![
            RecordTypeField {
                docs: Vec::new(),
                label: SpannedString::new(file_id, 9, "x"),
                ann: Term::Universe(FileSpan::new(file_id, 13, 17), None),
            },
            RecordTypeField {
                docs: Vec::new(),
                label: SpannedString::new(file_id, 19, "y"),
                ann: Term::Universe(FileSpan::new(file_id, 23, 27), None),
            },
        ]
    ));
}

#[test]
fn record_type_trailing_semicolon() {
    test_term!(
        "Record { x : Type; y : Type; }",
        |file_id| Term::RecordType(
            FileSpan::new(file_id, 0, 30),
            vec![
                RecordTypeField {
                    docs: Vec::new(),
                    label: SpannedString::new(file_id, 9, "x"),
                    ann: Term::Universe(FileSpan::new(file_id, 13, 17), None),
                },
                RecordTypeField {
                    docs: Vec::new(),
                    label: SpannedString::new(file_id, 19, "y"),
                    ann: Term::Universe(FileSpan::new(file_id, 23, 27), None),
                },
            ]
        ),
    );
}

#[test]
fn record_intro() {
    test_term!("record { x = x; y = y }", |file_id| Term::RecordIntro(
        FileSpan::new(file_id, 0, 23),
        vec![
            RecordIntroField::Explicit {
                label: SpannedString::new(file_id, 9, "x"),
                params: Vec::new(),
                body_ty: None,
                body: Term::Var(SpannedString::new(file_id, 13, "x")),
            },
            RecordIntroField::Explicit {
                label: SpannedString::new(file_id, 16, "y"),
                params: Vec::new(),
                body_ty: None,
                body: Term::Var(SpannedString::new(file_id, 20, "y")),
            },
        ]
    ));
}

#[test]
fn record_intro_fun_sugar() {
    test_term!("record { f x y = x; g x y : Type = x }", |file_id| {
        Term::RecordIntro(
            FileSpan::new(file_id, 0, 38),
            vec![
                RecordIntroField::Explicit {
                    label: SpannedString::new(file_id, 9, "f"),
                    params: vec![
                        IntroParam::Explicit(Pattern::Var(SpannedString::new(file_id, 11, "x"))),
                        IntroParam::Explicit(Pattern::Var(SpannedString::new(file_id, 13, "y"))),
                    ],
                    body_ty: None,
                    body: Term::Var(SpannedString::new(file_id, 17, "x")),
                },
                RecordIntroField::Explicit {
                    label: SpannedString::new(file_id, 20, "g"),
                    params: vec![
                        IntroParam::Explicit(Pattern::Var(SpannedString::new(file_id, 22, "x"))),
                        IntroParam::Explicit(Pattern::Var(SpannedString::new(file_id, 24, "y"))),
                    ],
                    body_ty: Some(Term::Universe(FileSpan::new(file_id, 28, 32), None)),
                    body: Term::Var(SpannedString::new(file_id, 35, "x")),
                },
            ],
        )
    });
}

#[test]
fn record_intro_trailing_semicolon() {
    test_term!("record { x = x; y : Type = y; }", |file_id| {
        Term::RecordIntro(
            FileSpan::new(file_id, 0, 31),
            vec![
                RecordIntroField::Explicit {
                    label: SpannedString::new(file_id, 9, "x"),
                    params: Vec::new(),
                    body_ty: None,
                    body: Term::Var(SpannedString::new(file_id, 13, "x")),
                },
                RecordIntroField::Explicit {
                    label: SpannedString::new(file_id, 16, "y"),
                    params: Vec::new(),
                    body_ty: Some(Term::Universe(FileSpan::new(file_id, 20, 24), None)),
                    body: Term::Var(SpannedString::new(file_id, 27, "y")),
                },
            ],
        )
    });
}

#[test]
fn record_proj() {
    test_term!("foo.bar", |file_id| Term::RecordElim(
        Box::new(Term::Var(SpannedString::new(file_id, 0, "foo"))),
        SpannedString::new(file_id, 4, "bar"),
    ));
}

#[test]
fn record_proj_proj() {
    test_term!("foo.bar.baz", |file_id| Term::RecordElim(
        Box::new(Term::RecordElim(
            Box::new(Term::Var(SpannedString::new(file_id, 0, "foo"))),
            SpannedString::new(file_id, 4, "bar"),
        )),
        SpannedString::new(file_id, 8, "baz"),
    ));
}

#[test]
fn record_proj_fun_app() {
    test_term!("foo.bar baz foo.bar", |file_id| Term::FunElim(
        Box::new(Term::RecordElim(
            Box::new(Term::Var(SpannedString::new(file_id, 0, "foo"))),
            SpannedString::new(file_id, 4, "bar"),
        )),
        vec![
            Arg::Explicit(Term::Var(SpannedString::new(file_id, 8, "baz"))),
            Arg::Explicit(Term::RecordElim(
                Box::new(Term::Var(SpannedString::new(file_id, 12, "foo"))),
                SpannedString::new(file_id, 16, "bar"),
            )),
        ],
    ));
}

#[test]
fn ann() {
    test_term!("foo : Bar : Baz", |file_id| Term::Ann(
        Box::new(Term::Var(SpannedString::new(file_id, 0, "foo"))),
        Box::new(Term::Ann(
            Box::new(Term::Var(SpannedString::new(file_id, 6, "Bar"))),
            Box::new(Term::Var(SpannedString::new(file_id, 12, "Baz"))),
        )),
    ));
}

#[test]
fn universe() {
    test_term!("Type", |file_id| Term::Universe(
        FileSpan::new(file_id, 0, 4),
        None
    ));
}

#[test]
fn universe_level_0() {
    test_term!("Type^0", |file_id| Term::Universe(
        FileSpan::new(file_id, 0, 6),
        Some(SpannedString::new(file_id, 5, "0")),
    ));
}

#[test]
fn universe_level_23() {
    test_term!("Type^23", |file_id| Term::Universe(
        FileSpan::new(file_id, 0, 7),
        Some(SpannedString::new(file_id, 5, "23")),
    ));
}
