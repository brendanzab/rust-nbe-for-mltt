//! Integration tests for the MLTT language.

macro_rules! test_sample {
    ($name:ident, $path:literal) => {
        #[test]
        fn $name() {
            use language_reporting::termcolor::{ColorChoice, StandardStream};
            use mltt_core::validate;
            use mltt_parse::lexer::Lexer;
            use mltt_parse::parser;
            use mltt_span::Files;

            let _ = pretty_env_logger::try_init();

            let mut files = Files::new();
            let writer = StandardStream::stdout(ColorChoice::Always);
            let reporting_config = language_reporting::DefaultConfig;

            let path = concat!("tests/samples/", $path, ".mltt");
            let src = include_str!(concat!("../../../tests/samples/", $path, ".mltt"));
            let file_id = files.add(path, src);

            let lexer = Lexer::new(&files[file_id]);
            let module = parser::parse_module(lexer).unwrap_or_else(|diagnostic| {
                let writer = &mut writer.lock();
                language_reporting::emit(writer, &files, &diagnostic, &reporting_config).unwrap();
                panic!("error encountered");
            });
            // FIXME: check lexer for errors

            let mut metas = mltt_core::meta::Env::new();
            let context = mltt_elaborate::Context::default();
            let module = mltt_elaborate::check_module(&context, &mut metas, &module)
                .unwrap_or_else(|diagnostic| {
                    let writer = &mut writer.lock();
                    language_reporting::emit(writer, &files, &diagnostic, &reporting_config)
                        .unwrap();
                    panic!("error encountered");
                });

            validate::check_module(&context.validation_context(), &metas, &module).unwrap_or_else(
                |error| {
                    panic!("failed validation: {}\n\n{:#?}", error, error);
                },
            );
        }
    };
}

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
