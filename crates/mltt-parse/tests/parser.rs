use language_reporting::termcolor::{ColorChoice, StandardStream};
use mltt_concrete::{
    Arg, Definition, IntroParam, Item, LiteralKind, Pattern, RecordIntroField, RecordTypeField,
    SpannedString, Term, TypeParam,
};
use mltt_parse::lexer::Lexer;
use mltt_parse::parser::parse_term;
use mltt_span::Files;
use mltt_span::Span;
use pretty_assertions::assert_eq;

macro_rules! test_term {
    ($src:expr, $expected_term:expr,) => {{
        test_term!($src, $expected_term);
    }};
    ($src:expr, $expected_term:expr) => {{
        let _ = pretty_env_logger::try_init();

        let mut files = Files::new();
        let file_id = files.add("test", $src);
        let term = match parse_term(file_id, Lexer::new(&files[file_id])) {
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
    test_term!("var", Term::Var(SpannedString::new(0, "var",)));
}

#[test]
fn hole() {
    test_term!("?", Term::Hole(Span::new(0, 1)));
}

#[test]
fn string_literal() {
    test_term!(
        "\"value\"",
        Term::LiteralIntro(LiteralKind::String, SpannedString::new(0, "\"value\""),),
    );
}

#[test]
fn char_literal() {
    test_term!(
        "'\\n'",
        Term::LiteralIntro(LiteralKind::Char, SpannedString::new(0, "'\\n'"),),
    );
}

#[test]
fn int_literal() {
    test_term!(
        "0xA_F00",
        Term::LiteralIntro(LiteralKind::Int, SpannedString::new(0, "0xA_F00"),),
    );
}

#[test]
fn float_literal() {
    test_term!(
        "0.3_46e_23",
        Term::LiteralIntro(LiteralKind::Float, SpannedString::new(0, "0.3_46e_23"),),
    );
}

#[test]
fn let_expr() {
    test_term!(
        "let var = Type; in var",
        Term::Let(
            Span::new(0, 22),
            vec![Item::Definition(Definition {
                docs: Vec::new(),
                label: SpannedString::new(4, "var"),
                params: Vec::new(),
                body_ty: None,
                body: Term::Universe(Span::new(10, 14), None),
            })],
            Box::new(Term::Var(SpannedString::new(19, "var"))),
        ),
    );
}

#[test]
fn if_expr() {
    test_term!(
        "if foo then bar else baz",
        Term::If(
            Span::new(0, 24),
            Box::new(Term::Var(SpannedString::new(3, "foo"))),
            Box::new(Term::Var(SpannedString::new(12, "bar"))),
            Box::new(Term::Var(SpannedString::new(21, "baz"))),
        ),
    );
}

#[test]
fn parens() {
    test_term!(
        "(foo)",
        Term::Parens(
            Span::new(0, 5),
            Box::new(Term::Var(SpannedString::new(1, "foo"))),
        ),
    );
}

#[test]
fn fun_ty() {
    test_term!(
        r"Fun (x y : Type) (z : Type) -> x",
        Term::FunType(
            Span::new(0, 32),
            vec![
                TypeParam::Explicit(
                    Span::new(4, 16),
                    vec![SpannedString::new(5, "x"), SpannedString::new(7, "y"),],
                    Term::Universe(Span::new(11, 15), None),
                ),
                TypeParam::Explicit(
                    Span::new(17, 27),
                    vec![SpannedString::new(18, "z")],
                    Term::Universe(Span::new(22, 26), None),
                ),
            ],
            Box::new(Term::Var(SpannedString::new(31, "x"))),
        ),
    );
}

#[test]
fn fun_ty_implicit() {
    test_term!(
        r"Fun {x y : Type} {z} -> x",
        Term::FunType(
            Span::new(0, 25),
            vec![
                TypeParam::Implicit(
                    Span::new(4, 16),
                    vec![SpannedString::new(5, "x"), SpannedString::new(7, "y"),],
                    Some(Term::Universe(Span::new(11, 15), None)),
                ),
                TypeParam::Implicit(Span::new(17, 20), vec![SpannedString::new(18, "z")], None,),
            ],
            Box::new(Term::Var(SpannedString::new(24, "x"))),
        ),
    );
}

#[test]
fn fun_ty_instance() {
    test_term!(
        r"Fun {{A : Foo}} -> A",
        Term::FunType(
            Span::new(0, 20),
            vec![TypeParam::Instance(
                Span::new(4, 15),
                SpannedString::new(6, "A"),
                Term::Var(SpannedString::new(10, "Foo")),
            )],
            Box::new(Term::Var(SpannedString::new(19, "A"))),
        ),
    );
}

#[test]
fn fun_arrow_type() {
    test_term!(
        "Foo -> Bar",
        Term::FunArrowType(
            Box::new(Term::Var(SpannedString::new(0, "Foo"))),
            Box::new(Term::Var(SpannedString::new(7, "Bar"))),
        ),
    );
}

#[test]
fn fun_arrow_type_nested() {
    test_term!(
        "Foo -> Bar -> Baz",
        Term::FunArrowType(
            Box::new(Term::Var(SpannedString::new(0, "Foo"))),
            Box::new(Term::FunArrowType(
                Box::new(Term::Var(SpannedString::new(7, "Bar"))),
                Box::new(Term::Var(SpannedString::new(14, "Baz"))),
            )),
        ),
    );
}

#[test]
fn fun_arrow_type_fun_app() {
    test_term!("Option A -> Option B -> Option C", {
        Term::FunArrowType(
            Box::new(Term::FunElim(
                Box::new(Term::Var(SpannedString::new(0, "Option"))),
                vec![Arg::Explicit(Term::Var(SpannedString::new(7, "A")))],
            )),
            Box::new(Term::FunArrowType(
                Box::new(Term::FunElim(
                    Box::new(Term::Var(SpannedString::new(12, "Option"))),
                    vec![Arg::Explicit(Term::Var(SpannedString::new(19, "B")))],
                )),
                Box::new(Term::FunElim(
                    Box::new(Term::Var(SpannedString::new(24, "Option"))),
                    vec![Arg::Explicit(Term::Var(SpannedString::new(31, "C")))],
                )),
            )),
        )
    });
}

#[test]
fn fun_intro() {
    test_term!(
        r"fun x => x",
        Term::FunIntro(
            Span::new(0, 10),
            vec![IntroParam::Explicit(Pattern::Var(SpannedString::new(
                4, "x",
            )))],
            Box::new(Term::Var(SpannedString::new(9, "x"))),
        ),
    );
}

#[test]
fn fun_intro_multi_params() {
    test_term!(
        r"fun x y z => x",
        Term::FunIntro(
            Span::new(0, 14),
            vec![
                IntroParam::Explicit(Pattern::Var(SpannedString::new(4, "x"))),
                IntroParam::Explicit(Pattern::Var(SpannedString::new(6, "y"))),
                IntroParam::Explicit(Pattern::Var(SpannedString::new(8, "z"))),
            ],
            Box::new(Term::Var(SpannedString::new(13, "x"))),
        ),
    );
}

#[test]
fn fun_intro_multi_params_implicit() {
    test_term!(
        r"fun x {y} {z = zz} => x",
        Term::FunIntro(
            Span::new(0, 23),
            vec![
                IntroParam::Explicit(Pattern::Var(SpannedString::new(4, "x"))),
                IntroParam::Implicit(Span::new(6, 9), SpannedString::new(7, "y"), None,),
                IntroParam::Implicit(
                    Span::new(10, 18),
                    SpannedString::new(11, "z"),
                    Some(Pattern::Var(SpannedString::new(15, "zz")))
                ),
            ],
            Box::new(Term::Var(SpannedString::new(22, "x"))),
        ),
    );
}

#[test]
fn fun_intro_multi_params_instance() {
    test_term!(
        r"fun x {{y}} {{z = zz}} => x",
        Term::FunIntro(
            Span::new(0, 27),
            vec![
                IntroParam::Explicit(Pattern::Var(SpannedString::new(4, "x"))),
                IntroParam::Instance(Span::new(6, 11), SpannedString::new(8, "y"), None,),
                IntroParam::Instance(
                    Span::new(12, 22),
                    SpannedString::new(14, "z"),
                    Some(Pattern::Var(SpannedString::new(18, "zz")))
                ),
            ],
            Box::new(Term::Var(SpannedString::new(26, "x"))),
        ),
    );
}

#[test]
fn fun_app_1() {
    test_term!(
        r"foo arg",
        Term::FunElim(
            Box::new(Term::Var(SpannedString::new(0, "foo"))),
            vec![Arg::Explicit(Term::Var(SpannedString::new(4, "arg",)))],
        ),
    );
}

#[test]
fn fun_app_2a() {
    test_term!(
        r"foo arg1 arg2",
        Term::FunElim(
            Box::new(Term::Var(SpannedString::new(0, "foo"))),
            vec![
                Arg::Explicit(Term::Var(SpannedString::new(4, "arg1"))),
                Arg::Explicit(Term::Var(SpannedString::new(9, "arg2"))),
            ],
        ),
    );
}

#[test]
fn fun_app_2b() {
    test_term!(
        r"foo (arg1) arg2.foo.bar arg3",
        Term::FunElim(
            Box::new(Term::Var(SpannedString::new(0, "foo"))),
            vec![
                Arg::Explicit(Term::Parens(
                    Span::new(4, 10),
                    Box::new(Term::Var(SpannedString::new(5, "arg1")))
                )),
                Arg::Explicit(Term::RecordElim(
                    Box::new(Term::RecordElim(
                        Box::new(Term::Var(SpannedString::new(11, "arg2"))),
                        SpannedString::new(16, "foo"),
                    )),
                    SpannedString::new(20, "bar"),
                )),
                Arg::Explicit(Term::Var(SpannedString::new(24, "arg3"))),
            ],
        ),
    );
}

#[test]
fn fun_app_implicit() {
    test_term!(
        r"foo {arg1} {arg2 = arg2}",
        Term::FunElim(
            Box::new(Term::Var(SpannedString::new(0, "foo"))),
            vec![
                Arg::Implicit(Span::new(4, 10), SpannedString::new(5, "arg1"), None,),
                Arg::Implicit(
                    Span::new(11, 24),
                    SpannedString::new(12, "arg2"),
                    Some(Term::Var(SpannedString::new(19, "arg2"))),
                ),
            ],
        ),
    );
}

#[test]
fn fun_app_instance() {
    test_term!(
        r"foo {{arg1}} {{arg2 = arg2}}",
        Term::FunElim(
            Box::new(Term::Var(SpannedString::new(0, "foo"))),
            vec![
                Arg::Instance(Span::new(4, 12), SpannedString::new(6, "arg1"), None,),
                Arg::Instance(
                    Span::new(13, 28),
                    SpannedString::new(15, "arg2"),
                    Some(Term::Var(SpannedString::new(22, "arg2"))),
                ),
            ],
        ),
    );
}

#[test]
fn record_type() {
    test_term!(
        "Record { x : Type; y : Type }",
        Term::RecordType(
            Span::new(0, 29),
            vec![
                RecordTypeField {
                    docs: Vec::new(),
                    label: SpannedString::new(9, "x"),
                    ann: Term::Universe(Span::new(13, 17), None),
                },
                RecordTypeField {
                    docs: Vec::new(),
                    label: SpannedString::new(19, "y"),
                    ann: Term::Universe(Span::new(23, 27), None),
                },
            ]
        ),
    );
}

#[test]
fn record_type_trailing_semicolon() {
    test_term!(
        "Record { x : Type; y : Type; }",
        Term::RecordType(
            Span::new(0, 30),
            vec![
                RecordTypeField {
                    docs: Vec::new(),
                    label: SpannedString::new(9, "x"),
                    ann: Term::Universe(Span::new(13, 17), None),
                },
                RecordTypeField {
                    docs: Vec::new(),
                    label: SpannedString::new(19, "y"),
                    ann: Term::Universe(Span::new(23, 27), None),
                },
            ]
        ),
    );
}

#[test]
fn record_intro() {
    test_term!(
        "record { x = x; y = y }",
        Term::RecordIntro(
            Span::new(0, 23),
            vec![
                RecordIntroField::Explicit {
                    label: SpannedString::new(9, "x"),
                    params: Vec::new(),
                    body_ty: None,
                    body: Term::Var(SpannedString::new(13, "x")),
                },
                RecordIntroField::Explicit {
                    label: SpannedString::new(16, "y"),
                    params: Vec::new(),
                    body_ty: None,
                    body: Term::Var(SpannedString::new(20, "y")),
                },
            ]
        ),
    );
}

#[test]
fn record_intro_fun_sugar() {
    test_term!("record { f x y = x; g x y : Type = x }", {
        Term::RecordIntro(
            Span::new(0, 38),
            vec![
                RecordIntroField::Explicit {
                    label: SpannedString::new(9, "f"),
                    params: vec![
                        IntroParam::Explicit(Pattern::Var(SpannedString::new(11, "x"))),
                        IntroParam::Explicit(Pattern::Var(SpannedString::new(13, "y"))),
                    ],
                    body_ty: None,
                    body: Term::Var(SpannedString::new(17, "x")),
                },
                RecordIntroField::Explicit {
                    label: SpannedString::new(20, "g"),
                    params: vec![
                        IntroParam::Explicit(Pattern::Var(SpannedString::new(22, "x"))),
                        IntroParam::Explicit(Pattern::Var(SpannedString::new(24, "y"))),
                    ],
                    body_ty: Some(Term::Universe(Span::new(28, 32), None)),
                    body: Term::Var(SpannedString::new(35, "x")),
                },
            ],
        )
    });
}

#[test]
fn record_intro_trailing_semicolon() {
    test_term!("record { x = x; y : Type = y; }", {
        Term::RecordIntro(
            Span::new(0, 31),
            vec![
                RecordIntroField::Explicit {
                    label: SpannedString::new(9, "x"),
                    params: Vec::new(),
                    body_ty: None,
                    body: Term::Var(SpannedString::new(13, "x")),
                },
                RecordIntroField::Explicit {
                    label: SpannedString::new(16, "y"),
                    params: Vec::new(),
                    body_ty: Some(Term::Universe(Span::new(20, 24), None)),
                    body: Term::Var(SpannedString::new(27, "y")),
                },
            ],
        )
    });
}

#[test]
fn record_proj() {
    test_term!(
        "foo.bar",
        Term::RecordElim(
            Box::new(Term::Var(SpannedString::new(0, "foo"))),
            SpannedString::new(4, "bar"),
        ),
    );
}

#[test]
fn record_proj_proj() {
    test_term!(
        "foo.bar.baz",
        Term::RecordElim(
            Box::new(Term::RecordElim(
                Box::new(Term::Var(SpannedString::new(0, "foo"))),
                SpannedString::new(4, "bar"),
            )),
            SpannedString::new(8, "baz"),
        ),
    );
}

#[test]
fn record_proj_fun_app() {
    test_term!(
        "foo.bar baz foo.bar",
        Term::FunElim(
            Box::new(Term::RecordElim(
                Box::new(Term::Var(SpannedString::new(0, "foo"))),
                SpannedString::new(4, "bar"),
            )),
            vec![
                Arg::Explicit(Term::Var(SpannedString::new(8, "baz"))),
                Arg::Explicit(Term::RecordElim(
                    Box::new(Term::Var(SpannedString::new(12, "foo"))),
                    SpannedString::new(16, "bar"),
                )),
            ],
        ),
    );
}

#[test]
fn ann() {
    test_term!(
        "foo : Bar : Baz",
        Term::Ann(
            Box::new(Term::Var(SpannedString::new(0, "foo"))),
            Box::new(Term::Ann(
                Box::new(Term::Var(SpannedString::new(6, "Bar"))),
                Box::new(Term::Var(SpannedString::new(12, "Baz"))),
            )),
        ),
    );
}

#[test]
fn universe() {
    test_term!("Type", Term::Universe(Span::new(0, 4), None));
}

#[test]
fn universe_level_0() {
    test_term!(
        "Type^0",
        Term::Universe(Span::new(0, 6), Some(SpannedString::new(5, "0")),),
    );
}

#[test]
fn universe_level_23() {
    test_term!(
        "Type^23",
        Term::Universe(Span::new(0, 7), Some(SpannedString::new(5, "23")),),
    );
}
