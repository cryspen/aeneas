//! C_lean gate: does the L₁ Lean emit typecheck against the Aeneas
//! `RuntimeShim`? Runs `aeneas-check --out <tmp>/<fixture>.lean`,
//! then `lake env lean <tmp>/<fixture>.lean` inside
//! `tests/lean-checker/lean-diff/` (which provides the shim's
//! `Aeneas` import).
//!
//! Reports per-decl `pass` for every decl in the cert if the
//! whole-file typecheck succeeds, `fail` otherwise. Without per-
//! decl emit support (Phase C `--only-decl` on mainline) we can't
//! reliably attribute typecheck failures to individual decls; the
//! gate is "whole-fixture pass-or-fail" until that lands.

use anyhow::{Context, Result};
use std::path::{Path, PathBuf};
use std::process::Command;
use tempfile::TempDir;

use crate::cert::Cert;
use crate::manifest::Manifest;
use crate::report::{GateOutcome, Report};

const GATE: &str = "c_lean";

pub fn run(
    cert: &Cert,
    cert_path: &Path,
    aeneas_check: &Path,
    lean_diff_dir: &Path,
    _manifest: &Manifest,
    report: &mut Report,
) -> Result<()> {
    let tmp = TempDir::new()?;
    let out_lean = tmp.path().join("emit.lean");
    let emit_status = Command::new(aeneas_check)
        .arg(cert_path)
        .arg("--out")
        .arg(&out_lean)
        .output()
        .with_context(|| format!("running aeneas-check at {}", aeneas_check.display()))?;
    if !emit_status.status.success() {
        let reason = format!("aeneas-check emit failed: {}",
            String::from_utf8_lossy(&emit_status.stderr).lines().next().unwrap_or(""));
        for decl in &cert.decls {
            report.record(&decl.path, GATE, GateOutcome::fail(reason.clone()));
        }
        return Ok(());
    }

    // `lake env lean <file>` typechecks the file with the
    // lean-diff project's RuntimeShim import path.
    let lake_status = Command::new("lake")
        .current_dir(lean_diff_dir)
        .arg("env")
        .arg("lean")
        .arg(&out_lean)
        .output()
        .with_context(|| format!("running lake env lean in {}", lean_diff_dir.display()))?;
    let outcome = if lake_status.status.success() {
        GateOutcome::pass()
    } else {
        let stderr = String::from_utf8_lossy(&lake_status.stderr);
        let first_err = stderr.lines().find(|l| l.contains("error:")).unwrap_or("typecheck failed");
        let trimmed: String = first_err.chars().take(120).collect();
        GateOutcome::fail(trimmed)
    };
    for decl in &cert.decls {
        report.record(&decl.path, GATE, outcome.clone());
    }
    Ok(())
}

/// Resolve the lean-diff project directory. Defaults to
/// `tests/lean-checker/lean-diff` relative to the repo root.
pub fn default_lean_diff_dir() -> PathBuf {
    let mut cur = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    loop {
        let cand = cur.join("tests/lean-checker/lean-diff");
        if cand.is_dir() {
            return cand;
        }
        if !cur.pop() {
            return PathBuf::from("tests/lean-checker/lean-diff");
        }
    }
}
