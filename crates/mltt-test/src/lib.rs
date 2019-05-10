//! Integration tests for the MLTT language.

macro_rules! run_test {
    ($name:ident, $path:literal) => {
        #[test]
        fn $name() {
            use goldenfile::Mint;
            use language_reporting::termcolor::{ColorChoice, StandardStream};
            use mltt_core::validate;
            use mltt_parse::lexer::Lexer;
            use mltt_parse::parser;
            use mltt_span::Files;
            use std::io::Write;

            let _ = pretty_env_logger::try_init();

            let mut files = Files::new();
            let writer = StandardStream::stdout(ColorChoice::Always);
            let reporting_config = language_reporting::DefaultConfig;

            let mut mint = Mint::new("../../tests/goldenfiles");
            let mut concrete_out = mint
                .new_goldenfile(concat!(stringify!($name), ".concrete"))
                .unwrap();
            let mut core_out = mint
                .new_goldenfile(concat!(stringify!($name), ".core"))
                .unwrap();

            let src = include_str!(concat!("../../../tests/", $path));
            let file_id = files.add($path, src);

            let lexer = Lexer::new(&files[file_id]);
            let concrete_module = parser::parse_module(lexer).unwrap_or_else(|diagnostic| {
                let writer = &mut writer.lock();
                language_reporting::emit(writer, &files, &diagnostic, &reporting_config).unwrap();
                panic!("error encountered");
            });
            // FIXME: check lexer for errors

            write!(concrete_out, "{:#?}", concrete_module).unwrap();

            let context = mltt_elaborate::Context::default();
            let mut metas = mltt_core::meta::Env::new();
            let core_module = mltt_elaborate::check_module(&context, &mut metas, &concrete_module)
                .unwrap_or_else(|diagnostic| {
                    let writer = &mut writer.lock();
                    language_reporting::emit(writer, &files, &diagnostic, &reporting_config)
                        .unwrap();
                    panic!("error encountered");
                });

            validate::check_module(&context.validation_context(), &metas, &core_module)
                .unwrap_or_else(|error| {
                    panic!("failed validation: {}\n\n{:#?}", error, error);
                });

            let core_module_doc = core_module.to_display_doc(&context.pretty_env());
            write!(core_out, "{}", core_module_doc.group().pretty(100)).unwrap();
        }
    };
}

run_test!(case_expressions, "case-expressions.mltt");
run_test!(categories, "categories.mltt");
run_test!(combinators, "combinators.mltt");
run_test!(connectives, "connectives.mltt");
run_test!(cumulativity, "cumulativity.mltt");
run_test!(empty, "empty.mltt");
run_test!(forward_declarations, "forward-declarations.mltt");
run_test!(if_expressions, "if-expressions.mltt");
run_test!(literals, "literals.mltt");
run_test!(let_expressions, "let-expressions.mltt");
run_test!(primitives, "primitives.mltt");
run_test!(records, "records.mltt");
