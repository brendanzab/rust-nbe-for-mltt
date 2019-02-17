#![warn(rust_2018_idioms)]

use std::error::Error;

pub mod repl;

#[derive(structopt::StructOpt)]
#[structopt(name = "mltt", about = "mltt cli")]
pub enum Options {
    /// Run the REPL
    #[structopt(name = "repl")]
    Repl(repl::Options),
}

pub fn run(options: Options) -> Result<(), Box<dyn Error>> {
    match options {
        Options::Repl(options) => repl::run(options),
    }
}
