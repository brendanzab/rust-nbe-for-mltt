use language_reporting::termcolor::{ColorChoice, StandardStream};
use language_reporting::Diagnostic;
use mltt_core::{meta, syntax};
use mltt_elaborate::{Context, MetaInsertion};
use mltt_parse::lexer::Lexer;
use mltt_parse::parser;
use mltt_span::{File, FileSpan, Files};
use rustyline::error::ReadlineError;
use rustyline::{Config, Editor};
use std::error::Error;
use std::io::Write;
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

/// Run the REPL with the given options.
pub fn run(options: Options) -> Result<(), Box<dyn Error>> {
    let mut writer = StandardStream::stdout(ColorChoice::Always);
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
    let context = Context::default();
    let mut metas = meta::Env::new();

    loop {
        match editor.readline(&options.prompt) {
            Ok(line) => {
                let file_id = files.add("repl", line);
                let file = &files[file_id];
                editor.add_history_entry(file.contents());

                match read_eval(&context, &mut metas, file) {
                    Ok((term, ty)) => write!(writer, "{} : {}", term, ty)?,
                    Err(diagnostic) => {
                        let config = language_reporting::DefaultConfig;
                        language_reporting::emit(&mut writer.lock(), &files, &diagnostic, &config)?;
                    },
                }
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

/// Read and evaluate the given file.
fn read_eval(
    context: &Context,
    metas: &mut meta::Env,
    file: &File,
) -> Result<(syntax::RcTerm, syntax::RcTerm), Diagnostic<FileSpan>> {
    let lexer = Lexer::new(&file);
    let concrete_term = parser::parse_term(lexer)?;;

    let (core_term, ty) =
        mltt_elaborate::synth_term(MetaInsertion::Yes, &context, metas, &concrete_term)?;

    let term_span = concrete_term.span();
    let term = context.normalize_term(metas, term_span, &core_term)?;
    let ty = context.read_back_value(metas, None, &ty)?;

    Ok((term, ty))
}
