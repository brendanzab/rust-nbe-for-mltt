// use mltt_concrete::desugar;
// use mltt_concrete::elaborate;
// use mltt_core::validate;
use mltt_parse::lexer::Lexer;
// use mltt_parse::parser;
use mltt_span::Files;
use std::fs;
use std::path::Path;

pub fn run(_test_name: &str, test_path: impl AsRef<Path>) {
    let test_path = test_path.as_ref();
    let src = fs::read_to_string(&test_path)
        .unwrap_or_else(|err| panic!("error reading `{}`: {}", test_path.display(), err));

    let mut files = Files::new();
    let file_id = files.add("test", src);

    let mut lexer = Lexer::new(&files[file_id]);
    for token in &mut lexer {
        println!("{:?}", token);
    }
    assert!(lexer.diagnostics().is_empty());

    // TODO:

    // let (concrete_module, errors) = parser::parse_module(Lexer::new(&files[file_id]));
    // assert_eq!(errors, vec![]);

    // let raw_module = desugar::desugar_module(&raw_module);
    // let (core_module, errors) = elaborate::elaborate_module(&raw_module);
    // assert_eq!(errors, vec![]);

    // let result = validate::validate_module(&core_module);
    // assert_eq!(result, Ok(()));
}
