use language_reporting::termcolor::{ColorChoice, StandardStream};
use mltt_core::{nbe, validate};
use mltt_elaborate::MetaInsertion;
use mltt_parse::lexer::Lexer;
use mltt_parse::parser;
use mltt_span::{FileId, Files};
use std::fs;

const TESTS_DIR: &'static str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests");
const REPORTING_CONFIG: language_reporting::DefaultConfig = language_reporting::DefaultConfig;

fn setup() -> (Files, mltt_core::meta::Env, mltt_elaborate::Context) {
    let files = Files::new();
    let metas = mltt_core::meta::Env::new();
    let context = mltt_elaborate::Context::default();
    (files, metas, context)
}

fn load_file(files: &mut Files, path: String) -> FileId {
    let src = fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}", error));
    files.add(path, src)
}

pub fn run_sample(name: &str) {
    let _ = pretty_env_logger::try_init();
    let writer = StandardStream::stdout(ColorChoice::Always);

    let (mut files, mut metas, context) = setup();

    let module_path = format!("{}/samples/{}.mltt", TESTS_DIR, name);
    let module_file_id = load_file(&mut files, module_path);

    let module = {
        let lexer = Lexer::new(&files[module_file_id]);
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

    validate::check_module(&context.validation_context(), &metas, &module)
        .unwrap_or_else(|error| panic!("{}", error));
}

pub fn run_elaborate_check_pass(name: &str) {
    let _ = pretty_env_logger::try_init();
    let writer = StandardStream::stdout(ColorChoice::Always);

    let (mut files, mut metas, context) = setup();

    let term_path = format!("{}/elaborate/check-pass/{}.term.mltt", TESTS_DIR, name);
    let ty_path = format!("{}/elaborate/check-pass/{}.type.mltt", TESTS_DIR, name);
    let term_file_id = load_file(&mut files, term_path);
    let ty_file_id = load_file(&mut files, ty_path);

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

    validate::synth_universe(&context.validation_context(), &metas, &expected_ty)
        .unwrap_or_else(|error| panic!("{}", error));

    let expected_ty = nbe::eval_term(context.prims(), &metas, context.values(), &expected_ty)
        .unwrap_or_else(|error| panic!("{}", error));

    let term = {
        let lexer = Lexer::new(&files[term_file_id]);
        let concrete_term = parser::parse_term(lexer).unwrap_or_else(|diagnostic| {
            let writer = &mut writer.lock();
            language_reporting::emit(writer, &files, &diagnostic, &REPORTING_CONFIG).unwrap();
            panic!("error encountered");
        });
        // FIXME: check lexer for errors

        mltt_elaborate::check_term(&context, &mut metas, &concrete_term, &expected_ty)
            .unwrap_or_else(|diagnostic| {
                let writer = &mut writer.lock();
                language_reporting::emit(writer, &files, &diagnostic, &REPORTING_CONFIG).unwrap();
                panic!("error encountered");
            })
    };

    validate::check_term(&context.validation_context(), &metas, &term, &expected_ty)
        .unwrap_or_else(|error| panic!("{}", error));
}

pub fn run_elaborate_synth_pass(name: &str) {
    let _ = pretty_env_logger::try_init();
    let writer = StandardStream::stdout(ColorChoice::Always);

    let (mut files, mut metas, context) = setup();

    let term_path = format!("{}/elaborate/synth-pass/{}.term.mltt", TESTS_DIR, name);
    let ty_path = format!("{}/elaborate/synth-pass/{}.type.mltt", TESTS_DIR, name);
    let term_file_id = load_file(&mut files, term_path);
    let ty_file_id = load_file(&mut files, ty_path);

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

    validate::synth_term(&context.validation_context(), &metas, &term)
        .unwrap_or_else(|error| panic!("{}", error));

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

    validate::synth_universe(&context.validation_context(), &metas, &expected_ty)
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
