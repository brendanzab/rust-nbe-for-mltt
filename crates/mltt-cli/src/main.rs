#![warn(rust_2018_idioms)]

use mltt_cli::Options;
use structopt::StructOpt;

fn main() {
    pretty_env_logger::init();

    mltt_cli::run(Options::from_args())
}
