use language_reporting::termcolor::{ColorChoice, StandardStream};
use mltt_parse::lexer::Lexer;
use mltt_parse::parser;
use mltt_span::Files;
use rustyline::error::ReadlineError;
use rustyline::{Config, Editor};
use std::error::Error;
use std::path::PathBuf;

/// The MLTT REPL/interactive mode.
#[derive(structopt::StructOpt)]
pub struct Options {
    /// The file to save the command history to.
    #[structopt(long = "history-file", default_value = "repl-history")]
    pub history_file: PathBuf,
    /// The prompt to display before expressions.
    #[structopt(long = "prompt", default_value = "> ")]
    pub prompt: String,
}

/// Run the REPL with the given options/
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
    let mut metas = mltt_core::syntax::MetaEnv::new();
    let context = mltt_elaborate::Context::default();

    let writer = StandardStream::stdout(ColorChoice::Always);

    loop {
        let line = editor.readline(&options.prompt);
        match line {
            Ok(line) => {
                let file_id = files.add("repl", line);

                editor.add_history_entry(files[file_id].contents());

                let lexer = Lexer::new(&files[file_id]);
                let concrete_term = match parser::parse_term(lexer) {
                    Ok(concrete_term) => concrete_term,
                    Err(diagnostic) => {
                        let config = language_reporting::DefaultConfig;
                        let writer = &mut writer.lock();
                        language_reporting::emit(writer, &files, &diagnostic, &config)?;
                        continue;
                    },
                };

                let (core_term, ty) =
                    match mltt_elaborate::synth_term(&context, &mut metas, &concrete_term) {
                        Ok((core_term, ty)) => (core_term, ty),
                        Err(diagnostic) => {
                            let config = language_reporting::DefaultConfig;
                            let writer = &mut writer.lock();
                            language_reporting::emit(writer, &files, &diagnostic, &config)?;
                            continue;
                        },
                    };

                let term_span = concrete_term.span();
                let term = context
                    .normalize_term(&metas, term_span, &core_term)
                    .unwrap();
                let ty = context.read_back_value(&metas, None, &ty).unwrap();

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
