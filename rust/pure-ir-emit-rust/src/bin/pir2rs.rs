//! `pir2rs` — turn a Pure-IR JSON dump into a Rust source file.
//!
//! Usage:
//!     pir2rs path/to/foo.pure.json [-o path/to/out.rs]
//!
//! With no `-o`, the emitted Rust is written to stdout.

use pure_ir_emit_rust::{emit_crate, EmitOptions};
use std::env;
use std::fs;
use std::io::{self, Write};
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();
    let mut input: Option<String> = None;
    let mut output: Option<String> = None;
    let mut banner = false;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "-o" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("error: -o requires an argument");
                    return ExitCode::from(2);
                }
                output = Some(args[i].clone());
            }
            "--banner" => banner = true,
            "-h" | "--help" => {
                println!("Usage: pir2rs <input.pure.json> [-o <output.rs>] [--banner]");
                return ExitCode::SUCCESS;
            }
            s if s.starts_with('-') => {
                eprintln!("error: unknown flag {s}");
                return ExitCode::from(2);
            }
            s => {
                if input.is_some() {
                    eprintln!("error: unexpected positional arg {s}");
                    return ExitCode::from(2);
                }
                input = Some(s.to_string());
            }
        }
        i += 1;
    }

    let input = match input {
        Some(p) => p,
        None => {
            eprintln!("error: missing input file");
            return ExitCode::from(2);
        }
    };

    let src = match fs::read_to_string(&input) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {input}: {e}");
            return ExitCode::from(1);
        }
    };

    let krate = match pure_ir::parse(&src) {
        Ok(k) => k,
        Err(e) => {
            eprintln!("error: parse failed: {e}");
            return ExitCode::from(1);
        }
    };

    let opts = EmitOptions {
        include_banner: banner,
    };
    let out_src = emit_crate(&krate, &opts);

    match output {
        Some(p) => {
            if let Err(e) = fs::write(&p, out_src) {
                eprintln!("error: cannot write {p}: {e}");
                return ExitCode::from(1);
            }
        }
        None => {
            let stdout = io::stdout();
            let mut h = stdout.lock();
            if let Err(e) = h.write_all(out_src.as_bytes()) {
                eprintln!("error: write stdout: {e}");
                return ExitCode::from(1);
            }
        }
    }

    ExitCode::SUCCESS
}
