#![warn(rust_2018_idioms)]

use mltt_cli::Options;
use std::error::Error;
use structopt::StructOpt;

fn main() -> Result<(), Box<dyn Error>> {
    pretty_env_logger::init();

    mltt_cli::run(Options::from_args())
}
