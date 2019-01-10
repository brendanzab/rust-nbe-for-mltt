use mltt_concrete::lexer::Lexer;
use std::fs;
use std::path::Path;

pub fn run(_test_name: &str, test_path: impl AsRef<Path>) {
    let test_path = test_path.as_ref();
    let src = fs::read_to_string(&test_path)
        .unwrap_or_else(|err| panic!("error reading `{}`: {}", test_path.display(), err));

    Lexer::new(&src).for_each(|token| println!("{}", token.unwrap().1));

    // TODO: parse
    // TODO: elaborate
    // TODO: validate
}
