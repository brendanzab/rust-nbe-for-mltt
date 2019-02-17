use language_reporting::termcolor::{ColorChoice, StandardStream};
use mltt_parse::lexer::Lexer;
use mltt_parse::parser;
use mltt_span::Files;
use rustyline::error::ReadlineError;
use rustyline::{Config, Editor};
use std::path::PathBuf;

#[derive(structopt::StructOpt)]
pub struct Options {
    /// The file to save the command history to
    #[structopt(long = "history-file", default_value = "repl-history")]
    pub history_file: PathBuf,
    /// The prompt to display before expressions
    #[structopt(long = "prompt", default_value = "> ")]
    pub prompt: String,
}

pub fn run(options: Options) {
    let mut editor = {
        let config = Config::builder()
            .history_ignore_space(true)
            .history_ignore_dups(true)
            .build();

        Editor::<()>::with_config(config)
    };

    if editor.load_history(&options.history_file).is_err() {
        // No previous REPL history!
    }

    let mut files = Files::new();
    let context = mltt_elaborate::Context::new();

    let writer = StandardStream::stdout(ColorChoice::Always);

    loop {
        let line = editor.readline(&options.prompt);
        match line {
            Ok(line) => {
                use mltt_concrete::resugar;
                use mltt_core::syntax::core;

                let file_id = files.add("repl", line);

                editor.add_history_entry(files[file_id].contents());

                let lexer = Lexer::new(&files[file_id]);
                let term = match parser::parse_term(lexer) {
                    Ok(term) => term,
                    Err(diagnostic) => {
                        language_reporting::emit(
                            &mut writer.lock(),
                            &files,
                            &diagnostic,
                            &language_reporting::DefaultConfig,
                        )
                        .unwrap();
                        continue;
                    },
                };

                let (core_term, ty) = match mltt_elaborate::synth_term(&context, &term) {
                    Ok((core_term, ty)) => (core_term, ty),
                    Err(error) => {
                        println!("{}", error);
                        continue;
                    },
                };

                let term_nf = context.normalize(&core_term).unwrap();
                let term = resugar::resugar(&core::RcTerm::from(&term_nf));

                let ty_nf = context.read_back(&ty).unwrap();
                let ty = resugar::resugar(&core::RcTerm::from(&ty_nf));

                println!("{} : {}", term, ty);
            },
            Err(error) => {
                match error {
                    ReadlineError::Interrupted => println!("CTRL-C"),
                    ReadlineError::Eof => println!("CTRL-D"),
                    err => println!("Error: {:?}", err),
                }
                break;
            },
        }
    }

    editor.save_history(&options.history_file).unwrap();
}
