#[macro_use]
extern crate failure;
extern crate github_rs;
extern crate serde_json;

use failure::Error;

fn main() {
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
