use language_reporting::termcolor::{ColorChoice, StandardStream};
use language_reporting::Diagnostic;
use mltt_core::{domain, nbe, syntax, validate};
use mltt_elaborate::MetaInsertion;
use mltt_parse::lexer::Lexer;
use mltt_parse::parser;
use mltt_span::{File, FileId, FileSpan, Files};
use std::fs;
use std::rc::Rc;

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

fn emit_diagnostic<'a, T>(
    writer: &'a StandardStream,
    files: &'a Files,
) -> impl FnOnce(Diagnostic<FileSpan>) -> T + 'a {
    move |diagnostic| {
        let writer = &mut writer.lock();
        language_reporting::emit(writer, files, &diagnostic, &REPORTING_CONFIG).unwrap();
        panic!("error encountered");
    }
}

fn synth_universe(
    context: &mltt_elaborate::Context,
    metas: &mut mltt_core::meta::Env,
    concrete_ty_file: &File,
) -> Result<Rc<domain::Type>, Diagnostic<FileSpan>> {
    let lexer = Lexer::new(&concrete_ty_file);
    let concrete_ty = parser::parse_term(lexer)?;
    // FIXME: check lexer for errors

    let (ty, level1) = mltt_elaborate::synth_universe(context, metas, &concrete_ty)?;
    let level2 = validate::synth_universe(&context.validation_context(), metas, &ty)
        .unwrap_or_else(|error| panic!("validation error: {}", error));

    assert_eq!(level1, level2);

    context.eval_term(metas, concrete_ty.span(), &ty)
}

fn check_term(
    context: &mltt_elaborate::Context,
    metas: &mut mltt_core::meta::Env,
    concrete_term_file: &File,
    expected_ty: &Rc<domain::Type>,
) -> Result<Rc<syntax::Term>, Diagnostic<FileSpan>> {
    let lexer = Lexer::new(&concrete_term_file);
    let concrete_term = parser::parse_term(lexer)?;
    // FIXME: check lexer for errors

    let term = mltt_elaborate::check_term(context, metas, &concrete_term, &expected_ty)?;
    validate::check_term(&context.validation_context(), &metas, &term, &expected_ty)
        .unwrap_or_else(|error| panic!("{}", error));

    Ok(term)
}

fn synth_term(
    context: &mltt_elaborate::Context,
    metas: &mut mltt_core::meta::Env,
    concrete_term_file: &File,
    expected_ty: &Rc<domain::Type>,
) -> Result<(Rc<syntax::Term>, Rc<domain::Type>), Diagnostic<FileSpan>> {
    let lexer = Lexer::new(&concrete_term_file);
    let concrete_term = parser::parse_term(lexer)?;
    // FIXME: check lexer for errors

    let (term, term_ty) =
        mltt_elaborate::synth_term(MetaInsertion::Yes, context, metas, &concrete_term)?;
    validate::synth_term(&context.validation_context(), &metas, &term)
        .unwrap_or_else(|error| panic!("{}", error));

    let prims = context.prims();
    let size = context.values().size();
    if !nbe::check_ty(&prims, &metas, size, false, &term_ty, &expected_ty)
        .unwrap_or_else(|error| panic!("{}", error))
    {
        panic!("unequal types");
    }

    Ok((term, term_ty))
}

pub fn run_sample(name: &str) {
    let _ = pretty_env_logger::try_init();
    let writer = StandardStream::stdout(ColorChoice::Always);

    let (mut files, mut metas, context) = setup();

    let module_path = format!("{}/samples/{}.mltt", TESTS_DIR, name);
    let module_file_id = load_file(&mut files, module_path);

    let lexer = Lexer::new(&files[module_file_id]);
    let concrete_module =
        parser::parse_module(lexer).unwrap_or_else(emit_diagnostic(&writer, &files));
    // FIXME: check lexer for errors

    let module = mltt_elaborate::check_module(&context, &mut metas, &concrete_module)
        .unwrap_or_else(emit_diagnostic(&writer, &files));
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

    let expected_ty = synth_universe(&context, &mut metas, &files[ty_file_id])
        .unwrap_or_else(emit_diagnostic(&writer, &files));
    check_term(&context, &mut metas, &files[term_file_id], &expected_ty)
        .unwrap_or_else(emit_diagnostic(&writer, &files));
}

pub fn run_elaborate_check_fail(name: &str) {
    let _ = pretty_env_logger::try_init();
    let writer = StandardStream::stdout(ColorChoice::Always);

    let (mut files, mut metas, context) = setup();

    let term_path = format!("{}/elaborate/check-fail/{}.term.mltt", TESTS_DIR, name);
    let ty_path = format!("{}/elaborate/check-fail/{}.type.mltt", TESTS_DIR, name);
    let term_file_id = load_file(&mut files, term_path);
    let ty_file_id = load_file(&mut files, ty_path);

    let lexer = Lexer::new(&files[term_file_id]);
    let _concrete_term = parser::parse_term(lexer).unwrap_or_else(emit_diagnostic(&writer, &files));

    let _expected_ty = synth_universe(&context, &mut metas, &files[ty_file_id])
        .unwrap_or_else(emit_diagnostic(&writer, &files));
    // TODO: Check failures
}

pub fn run_elaborate_synth_pass(name: &str) {
    let _ = pretty_env_logger::try_init();
    let writer = StandardStream::stdout(ColorChoice::Always);

    let (mut files, mut metas, context) = setup();

    let term_path = format!("{}/elaborate/synth-pass/{}.term.mltt", TESTS_DIR, name);
    let ty_path = format!("{}/elaborate/synth-pass/{}.type.mltt", TESTS_DIR, name);
    let term_file_id = load_file(&mut files, term_path);
    let ty_file_id = load_file(&mut files, ty_path);

    let expected_ty = synth_universe(&context, &mut metas, &files[ty_file_id])
        .unwrap_or_else(emit_diagnostic(&writer, &files));
    synth_term(&context, &mut metas, &files[term_file_id], &expected_ty)
        .unwrap_or_else(emit_diagnostic(&writer, &files));
}

pub fn run_elaborate_synth_fail(name: &str) {
    let _ = pretty_env_logger::try_init();
    let writer = StandardStream::stdout(ColorChoice::Always);

    let (mut files, mut _metas, _context) = setup();

    let term_path = format!("{}/elaborate/synth-fail/{}.term.mltt", TESTS_DIR, name);
    let term_file_id = load_file(&mut files, term_path);

    let lexer = Lexer::new(&files[term_file_id]);
    let _concrete_term = parser::parse_term(lexer).unwrap_or_else(emit_diagnostic(&writer, &files));

    // TODO: Check failures
}
