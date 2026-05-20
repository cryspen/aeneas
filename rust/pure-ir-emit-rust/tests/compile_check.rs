//! Broader compile-check: for each fixture in the working
//! whitelist, emit Rust from each pipeline stage and shell out to
//! `rustc --edition 2021 --crate-type lib --emit metadata`. A
//! fixture passes if every stage's emit is rustc-accepted.
//!
//! The whitelist below is conservative: it deliberately omits
//! fixtures that exercise IR shapes we don't yet emit cleanly
//! (e.g. raw `Loop` nodes only present in `post-s2p`, builtin
//! array intrinsics from `arrays_defs`, etc.). The goal is to
//! demonstrate parseable output for representative IR shapes, not
//! 100% coverage.

use std::path::PathBuf;
use std::process::Command;

use pure_ir_emit_rust::{emit_crate, EmitOptions};

const FIXTURES: &[(&str, &[&str])] = &[
    // (fixture-name, stages-to-check)
    ("incr_cert", &["post-s2p", "post-micro", "pre-extract"]),
    ("enums_basic", &["post-s2p", "post-micro", "pre-extract"]),
    ("traits_basic", &["post-s2p", "post-micro", "pre-extract"]),
    // loops_simple/post-s2p still ships a raw `Loop` node we render
    // as a typed `unimplemented!`. It parses + typechecks (because
    // `unimplemented!` is `!`), so keep all three.
    ("loops_simple", &["post-s2p", "post-micro", "pre-extract"]),
];

fn golden(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("pure-ir")
        .join("tests")
        .join("golden")
        .join(name)
}

fn emit(fixture: &str, stage: &str) -> String {
    let path = golden(&format!("{fixture}.{stage}.pure.json"));
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!("read {}: {e}", path.display())
    });
    let krate = pure_ir::parse(&src).expect("parse JSON");
    emit_crate(&krate, &EmitOptions::default())
}

fn rustc_check(src: &str, label: &str) -> Result<(), String> {
    let dir = std::env::temp_dir().join(format!(
        "pir-compile-check-{label}-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let rs = dir.join("out.rs");
    let meta = dir.join("out.rmeta");
    std::fs::write(&rs, src).map_err(|e| e.to_string())?;
    let output = Command::new("rustc")
        .args([
            "--edition",
            "2021",
            "--crate-type",
            "lib",
            rs.to_str().unwrap(),
            "--emit",
            "metadata",
            "-o",
            meta.to_str().unwrap(),
        ])
        .output()
        .map_err(|e| format!("spawn rustc: {e}"))?;
    if output.status.success() {
        Ok(())
    } else {
        Err(format!(
            "rustc failed for {label}\nstderr:\n{}\nfile: {}",
            String::from_utf8_lossy(&output.stderr),
            rs.display()
        ))
    }
}

#[test]
fn whitelist_fixtures_compile() {
    let mut failures = Vec::new();
    for (fixture, stages) in FIXTURES {
        for stage in *stages {
            let out = emit(fixture, stage);
            let label = format!("{fixture}_{}", stage.replace('-', "_"));
            if let Err(e) = rustc_check(&out, &label) {
                failures.push(format!("[{fixture}/{stage}] {e}"));
            }
        }
    }
    if !failures.is_empty() {
        panic!(
            "{} fixture-stage(s) failed to compile:\n{}",
            failures.len(),
            failures.join("\n\n")
        );
    }
}
