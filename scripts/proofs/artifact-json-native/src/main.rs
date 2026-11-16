//! Independent serde_json agreement samples, not a proof of the Rust parser.
use std::{env, fs, io::{self, Write}, process};

fn main() {
    let mut output = io::BufWriter::new(io::stdout().lock());
    for filename in env::args().skip(1) {
        let bytes = fs::read(&filename).expect("read public JSON sample");
        match serde_json::from_slice::<serde_json::Value>(&bytes) {
            Ok(value) => writeln!(output, "{}", value).expect("write JSON result"),
            Err(error) => {
                eprintln!("{}: {}", filename, error);
                process::exit(1);
            }
        }
    }
}
