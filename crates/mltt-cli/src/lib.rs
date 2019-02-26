#![warn(rust_2018_idioms)]

use std::error::Error;

pub mod repl;

/// The MLTT command line interface
#[derive(structopt::StructOpt)]
#[structopt(name = "mltt")]
pub enum Options {
    /// Runs the REPL/interactive mode
    #[structopt(name = "repl")]
    Repl(repl::Options),
}

/// Run the CLI with the given options
pub fn run(options: Options) -> Result<(), Box<dyn Error>> {
    match options {
        Options::Repl(options) => repl::run(options),
    }
}
