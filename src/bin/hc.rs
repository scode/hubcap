extern crate clap;
extern crate serde_json;

use anyhow::anyhow;
use anyhow::Error;
use clap::App;
use clap::Arg;
use clap::SubCommand;

fn main() {
    if let Err(ref e) = run() {
        use std::io::Write; // for write_fmt()
        let stderr = &mut ::std::io::stderr();

        writeln!(stderr, "{}", e).unwrap();

        ::std::process::exit(1);
    }
}

fn run() -> Result<(), Error> {
    let matches = App::new("hubcap")
        .version("0.1")
        .arg(
            Arg::with_name("v")
                .short("v")
                .multiple(true)
                .help("Sets the level of verbosity"),
        )
        .subcommand(SubCommand::with_name("status").about("Print branch and PR status"))
        .get_matches();

    if let Some(_matches) = matches.subcommand_matches("status") {
        Err(anyhow!("not yet implemented"))
    } else {
        // TODO(scode): Print help when no args given.
        Err(anyhow!("no cmd given"))
    }
}
