extern crate clap;
#[macro_use]
extern crate failure;
extern crate github_rs;
extern crate serde_json;

use clap::Arg;
use clap::App;
use clap::SubCommand;
use failure::Error;

fn main() {
    let matches = App::new("hubcap")
        .version("0.1")
        .arg(Arg::with_name("v")
            .short("v")
            .multiple(true)
            .help("Sets the level of verbosity"))
        .subcommand(SubCommand::with_name("status")
            .about("print current branch and PR statuses"))
        .get_matches();



    if let Err(ref e) = run() {
        use std::io::Write; // for write_fmt()
        let stderr = &mut ::std::io::stderr();

        writeln!(stderr, "{}", e).unwrap();

        ::std::process::exit(1);
    }
}

fn run() -> Result<(), Error> {
    return Err(format_err!("not yet implemented"))
}
