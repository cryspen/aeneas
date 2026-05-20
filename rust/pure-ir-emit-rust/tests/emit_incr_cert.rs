//! Focused integration test for the canonical fixture, `incr_cert`.
//!
//! Parses the committed `post-s2p` golden, emits Rust, and checks the
//! output is rustc-parseable and contains both of the original Rust
//! function names (`incr` and `incr_local`).

use std::path::PathBuf;
use std::process::Command;

use pure_ir_emit_rust::{emit_crate, EmitOptions};

fn golden(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("pure-ir")
        .join("tests")
        .join("golden")
        .join(name)
}

fn emit_for(stage: &str) -> String {
    let path = golden(&format!("incr_cert.{stage}.pure.json"));
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!("read {}: {e}", path.display())
    });
    let krate = pure_ir::parse(&src).expect("parse JSON");
    emit_crate(&krate, &EmitOptions::default())
}

#[test]
fn incr_cert_emits_both_functions() {
    let out = emit_for("post-s2p");
    // The two original Rust fns should appear in the emitted source.
    // Naming is `flat_path_ident`: short for 2-segment paths, otherwise
    // disambiguated by def_id.
    assert!(out.contains("pub fn incr("), "missing fn incr:\n{out}");
    assert!(
        out.contains("pub fn incr_local("),
        "missing fn incr_local:\n{out}"
    );
}

#[test]
fn incr_cert_rustc_parses_post_s2p() {
    let out = emit_for("post-s2p");
    rustc_check(&out, "incr_cert_post_s2p");
}

#[test]
fn incr_cert_rustc_parses_post_micro() {
    let out = emit_for("post-micro");
    rustc_check(&out, "incr_cert_post_micro");
}

#[test]
fn incr_cert_rustc_parses_pre_extract() {
    let out = emit_for("pre-extract");
    rustc_check(&out, "incr_cert_pre_extract");
}

fn rustc_check(src: &str, label: &str) {
    let dir = std::env::temp_dir().join(format!("pir-emit-{label}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let rs = dir.join("out.rs");
    let meta = dir.join("out.rmeta");
    std::fs::write(&rs, src).unwrap();
    let status = Command::new("rustc")
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
        .status()
        .expect("spawn rustc");
    assert!(
        status.success(),
        "rustc rejected emitted source for {label} (see {})",
        rs.display()
    );
}
