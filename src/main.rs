// `error_chain!` can recurse deeply
#![recursion_limit = "1024"]

extern crate github_rs;
extern crate serde_json;

#[macro_use]
extern crate error_chain;

mod errors {
    error_chain!{}
}

use errors::*;

fn main() {
    if let Err(ref e) = run() {
        use std::io::Write; // for write_fmt()
        use error_chain::ChainedError; // for display_chain()
        let stderr = &mut ::std::io::stderr();

        writeln!(stderr, "{}", e.display_chain()).unwrap();

        ::std::process::exit(1);
    }
}

fn run() -> Result<String> {
    return Err("not yet implemented".into())
}
