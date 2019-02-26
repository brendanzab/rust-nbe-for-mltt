use language_reporting::termcolor::{ColorChoice, StandardStream};
use mltt_parse::lexer::Lexer;
use mltt_parse::parser;
use mltt_span::Files;
use rustyline::error::ReadlineError;
use rustyline::{Config, Editor};
use std::error::Error;
use std::path::PathBuf;

/// The MLTT REPL/interactive mode
#[derive(structopt::StructOpt)]
pub struct Options {
    /// The file to save the command history to
    #[structopt(long = "history-file", default_value = "repl-history")]
    pub history_file: PathBuf,
    /// The prompt to display before expressions
    #[structopt(long = "prompt", default_value = "> ")]
    pub prompt: String,
}

/// Run the REPL with the given options
pub fn run(options: Options) -> Result<(), Box<dyn Error>> {
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

                let file_id = files.add("repl", line);

                editor.add_history_entry(files[file_id].contents());

                let lexer = Lexer::new(&files[file_id]);
                let term = match parser::parse_term(lexer) {
                    Ok(term) => term,
                    Err(diagnostic) => {
                        let config = language_reporting::DefaultConfig;
                        language_reporting::emit(&mut writer.lock(), &files, &diagnostic, &config)?;
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
                let term = resugar::resugar(&term_nf);

                let ty_nf = context.read_back(&ty).unwrap();
                let ty = resugar::resugar(&ty_nf);

                println!("{} : {}", term, ty);
            },
            Err(ReadlineError::Interrupted) => println!("Interrupted!"),
            Err(ReadlineError::Eof) => break,
            Err(error) => return Err(error.into()),
        }
    }

    editor.save_history(&options.history_file)?;

    println!("Bye bye");

    Ok(())
}
