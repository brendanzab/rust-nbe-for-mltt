//! Integration tests for the MLTT language.

use language_reporting::termcolor::{ColorChoice, StandardStream};
use mltt_core::{nbe, validate};
use mltt_elaborate::MetaInsertion;
use mltt_parse::lexer::Lexer;
use mltt_parse::parser;
use mltt_span::Files;
use std::fs;

const TESTS_DIR: &'static str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests");
const REPORTING_CONFIG: language_reporting::DefaultConfig = language_reporting::DefaultConfig;

pub fn run_sample(name: &str) {
    let _ = pretty_env_logger::try_init();
    let writer = StandardStream::stdout(ColorChoice::Always);

    let mut files = Files::new();
    let mut metas = mltt_core::meta::Env::new();
    let context = mltt_elaborate::Context::default();
    let validation_context = context.validation_context();

    let file_id = {
        let path = format!("{}/samples/{}.mltt", TESTS_DIR, name);
        let src = fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}", error));
        files.add(path, src)
    };

    let module = {
        let lexer = Lexer::new(&files[file_id]);
        let concrete_module = parser::parse_module(lexer).unwrap_or_else(|diagnostic| {
            let writer = &mut writer.lock();
            language_reporting::emit(writer, &files, &diagnostic, &REPORTING_CONFIG).unwrap();
            panic!("error encountered");
        });
        // FIXME: check lexer for errors

        mltt_elaborate::check_module(&context, &mut metas, &concrete_module).unwrap_or_else(
            |diagnostic| {
                let writer = &mut writer.lock();
                language_reporting::emit(writer, &files, &diagnostic, &REPORTING_CONFIG).unwrap();
                panic!("error encountered");
            },
        )
    };

    validate::check_module(&validation_context, &metas, &module)
        .unwrap_or_else(|error| panic!("{}", error));
}

pub fn run_elaborate_pass(name: &str) {
    let _ = pretty_env_logger::try_init();
    let writer = StandardStream::stdout(ColorChoice::Always);

    let mut files = Files::new();
    let mut metas = mltt_core::meta::Env::new();
    let context = mltt_elaborate::Context::default();
    let validation_context = context.validation_context();

    let term_file_id = {
        let path = format!("{}/elaborate/pass/{}.term.mltt", TESTS_DIR, name);
        let src = fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}", error));
        files.add(path, src)
    };

    let (term, term_ty) = {
        let lexer = Lexer::new(&files[term_file_id]);
        let concrete_term = parser::parse_term(lexer).unwrap_or_else(|diagnostic| {
            let writer = &mut writer.lock();
            language_reporting::emit(writer, &files, &diagnostic, &REPORTING_CONFIG).unwrap();
            panic!("error encountered");
        });
        // FIXME: check lexer for errors

        mltt_elaborate::synth_term(MetaInsertion::Yes, &context, &mut metas, &concrete_term)
            .unwrap_or_else(|diagnostic| {
                let writer = &mut writer.lock();
                language_reporting::emit(writer, &files, &diagnostic, &REPORTING_CONFIG).unwrap();
                panic!("error encountered");
            })
    };

    validate::synth_term(&validation_context, &metas, &term)
        .unwrap_or_else(|error| panic!("{}", error));

    let ty_file_id = {
        let path = format!("{}/elaborate/pass/{}.type.mltt", TESTS_DIR, name);
        let src = fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}", error));
        files.add(path, src)
    };

    let (expected_ty, _level) = {
        let lexer = Lexer::new(&files[ty_file_id]);
        let concrete_ty = parser::parse_term(lexer).unwrap_or_else(|diagnostic| {
            let writer = &mut writer.lock();
            language_reporting::emit(writer, &files, &diagnostic, &REPORTING_CONFIG).unwrap();
            panic!("error encountered");
        });
        // FIXME: check lexer for errors

        mltt_elaborate::synth_universe(&context, &mut metas, &concrete_ty).unwrap_or_else(
            |diagnostic| {
                let writer = &mut writer.lock();
                language_reporting::emit(writer, &files, &diagnostic, &REPORTING_CONFIG).unwrap();
                panic!("error encountered");
            },
        )
    };

    validate::synth_universe(&validation_context, &metas, &expected_ty)
        .unwrap_or_else(|error| panic!("{}", error));

    let expected_ty = nbe::eval_term(context.prims(), &metas, context.values(), &expected_ty)
        .unwrap_or_else(|error| panic!("{}", error));

    if !nbe::check_ty(
        context.prims(),
        &metas,
        context.values().size(),
        false,
        &term_ty,
        &expected_ty,
    )
    .unwrap_or_else(|error| panic!("{}", error))
    {
        panic!("unequal types");
    }
}

#[cfg(test)]
macro_rules! test_sample {
    ($test_name:ident, $file_name:literal) => {
        #[test]
        fn $test_name() {
            $crate::run_sample($file_name);
        }
    };
}

#[cfg(test)]
macro_rules! test_elaborate_pass {
    ($test_name:ident, $file_name:literal) => {
        #[test]
        fn $test_name() {
            $crate::run_elaborate_pass($file_name);
        }
    };
}

#[cfg(test)]
mod samples {
    test_sample!(case_expressions, "case-expressions");
    test_sample!(categories, "categories");
    test_sample!(combinators, "combinators");
    test_sample!(connectives, "connectives");
    test_sample!(cumulativity, "cumulativity");
    test_sample!(empty, "empty");
    test_sample!(forward_declarations, "forward-declarations");
    test_sample!(if_expressions, "if-expressions");
    test_sample!(literals, "literals");
    test_sample!(let_expressions, "let-expressions");
    test_sample!(primitives, "primitives");
    test_sample!(records, "records");
}

#[cfg(test)]
mod elaborate {
    mod pass {
        test_elaborate_pass!(fun_elim_implicit, "fun-elim-implicit");
        test_elaborate_pass!(fun_elim, "fun-elim");
        test_elaborate_pass!(fun_intro_implicit, "fun-intro-implicit");
        test_elaborate_pass!(fun_intro, "fun-intro");
        test_elaborate_pass!(fun_type_param_group_1, "fun-type-param-group-1");
        test_elaborate_pass!(fun_type_param_group_2, "fun-type-param-group-2");
        test_elaborate_pass!(fun_type_term_term, "fun-type-term-term");
        test_elaborate_pass!(fun_type_term_type, "fun-type-term-type");
        test_elaborate_pass!(fun_type_term_type1, "fun-type-term-type1");
        test_elaborate_pass!(fun_type_type_term, "fun-type-type-term");
        test_elaborate_pass!(fun_type_type_type, "fun-type-type-type");
        test_elaborate_pass!(fun_type_type1_term, "fun-type-type1-term");
        test_elaborate_pass!(if_, "if");
        test_elaborate_pass!(literal_intro_bool_false, "literal-intro-bool-false");
        test_elaborate_pass!(literal_intro_bool_true, "literal-intro-bool-true");
        test_elaborate_pass!(literal_intro_string, "literal-intro-string");
        test_elaborate_pass!(literal_intro_u8_dec_min, "literal-intro-u8-dec-min");
        test_elaborate_pass!(literal_intro_u8_dec_max, "literal-intro-u8-dec-max");
        test_elaborate_pass!(literal_type_bool, "literal-type-bool");
        test_elaborate_pass!(literal_type_char, "literal-type-char");
        test_elaborate_pass!(literal_type_f32, "literal-type-f32");
        test_elaborate_pass!(literal_type_f64, "literal-type-f64");
        test_elaborate_pass!(literal_type_s8, "literal-type-s8");
        test_elaborate_pass!(literal_type_s16, "literal-type-s16");
        test_elaborate_pass!(literal_type_s32, "literal-type-s32");
        test_elaborate_pass!(literal_type_s64, "literal-type-s64");
        test_elaborate_pass!(literal_type_string, "literal-type-string");
        test_elaborate_pass!(literal_type_u8, "literal-type-u8");
        test_elaborate_pass!(literal_type_u16, "literal-type-u16");
        test_elaborate_pass!(literal_type_u32, "literal-type-u32");
        test_elaborate_pass!(literal_type_u64, "literal-type-u64");
        test_elaborate_pass!(parens, "parens");
        test_elaborate_pass!(prim, "prim");
        test_elaborate_pass!(record_elim_dependent, "record-elim-dependent");
        test_elaborate_pass!(record_elim_singleton, "record-elim-singleton");
        test_elaborate_pass!(record_intro_empty, "record-intro-empty");
        test_elaborate_pass!(record_intro_singleton, "record-intro-singleton");
        test_elaborate_pass!(record_intro_singleton1, "record-intro-singleton1");
        test_elaborate_pass!(record_dependent, "record-type-dependent");
        test_elaborate_pass!(record_type_empty, "record-type-empty");
        test_elaborate_pass!(record_type_singleton, "record-type-singleton");
        test_elaborate_pass!(record_type_singleton1, "record-type-singleton1");
        test_elaborate_pass!(type_, "type");
        test_elaborate_pass!(type0, "type0");
        test_elaborate_pass!(type1, "type1");
    }
}
