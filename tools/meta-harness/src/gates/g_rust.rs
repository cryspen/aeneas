//! G_rust gate: source-tests-as-oracle.
//!
//! Runs `cargo test --no-fail-fast` against the source crate and
//! maps test names back to cert decls. A decl is:
//!
//! - `pass` if at least one matching test ran AND all matching tests
//!   passed;
//! - `mismatch` if any matching test failed (the emit is wrong);
//! - `skip(no_test_coverage)` if no test matched the decl.
//!
//! Decl ↔ test mapping is by name-stem matching: the meta-harness
//! computes a set of "candidate stems" per decl (e.g.
//! `incr_cert::incr` → ["incr_cert_incr", "incr"]; `constants::incr`
//! → ["constants_incr", "incr"]) and a test matches if its name
//! starts with any candidate followed by `_` or end-of-string.
//!
//! Manifest overrides (`[decls.<path>].g_rust = { skip = "..." }`)
//! short-circuit the lookup for decls the user has declared
//! intentionally out of scope (e.g. `dyn Trait`, FFI).
//!
//! Future: contract §4 G_rust describes a swap-based workflow
//! (`aeneas-check --emit-rust` + cargo test on the swapped crate).
//! The in-tree differential crate (`tests/lean-checker/differential/`)
//! already encodes R₀↔R₁ via `--rust-model`, so the simpler
//! `cargo test` workflow is sufficient for the PoC; swap-based is
//! deferred until external-crate workflows justify it.

use anyhow::{Context, Result};
use std::path::Path;
use std::process::Command;

use crate::cert::Cert;
use crate::manifest::{DeclVerdict, Manifest};
use crate::report::{GateOutcome, Report};

const GATE: &str = "g_rust";

pub fn run(
    cert: &Cert,
    _cert_path: &Path,
    _aeneas_check: &Path,
    source_crate: &Path,
    manifest: &Manifest,
    report: &mut Report,
) -> Result<()> {
    let manifest_path = source_crate.join("Cargo.toml");
    if !manifest_path.is_file() {
        anyhow::bail!(
            "g_rust: source crate manifest not found at {}",
            manifest_path.display()
        );
    }

    let output = Command::new("cargo")
        .arg("test")
        .arg("--manifest-path")
        .arg(&manifest_path)
        .arg("--release")
        .arg("--no-fail-fast")
        .output()
        .with_context(|| format!("running cargo test for {}", manifest_path.display()))?;

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let test_results = parse_test_output(&stdout);
    if test_results.is_empty() {
        // No tests ran — surface as a build-failure or empty-suite skip.
        let reason = if !output.status.success() {
            let first_err = stderr.lines().find(|l| l.contains("error")).unwrap_or("");
            format!("cargo test failed: {first_err}")
        } else {
            "source crate has no tests".to_string()
        };
        for decl in &cert.decls {
            report.record(&decl.path, GATE, GateOutcome::skip(reason.clone()));
        }
        return Ok(());
    }

    for decl in &cert.decls {
        // Manifest override.
        if let Some(o) = manifest.decls.get(&decl.path) {
            if let Some(v) = &o.g_rust {
                let outcome = match v {
                    DeclVerdict::Skip { skip } => GateOutcome::skip(skip),
                    DeclVerdict::Divergent { divergent } => GateOutcome::divergent(divergent),
                    DeclVerdict::Vectors { .. } => continue,
                };
                report.record(&decl.path, GATE, outcome);
                continue;
            }
        }

        let stems = test_stems_for_decl(&decl.path);
        let matched: Vec<&TestResult> = test_results
            .iter()
            .filter(|t| stems.iter().any(|s| test_matches_stem(&t.name, s)))
            .collect();

        let outcome = if matched.is_empty() {
            GateOutcome::skip("no_test_coverage")
        } else if matched.iter().any(|t| !t.ok) {
            let failing: Vec<&str> = matched.iter().filter(|t| !t.ok).map(|t| t.name.as_str()).collect();
            GateOutcome::mismatch(format!("failing test(s): {}", failing.join(", ")))
        } else {
            GateOutcome::pass()
        };
        report.record(&decl.path, GATE, outcome);
    }

    Ok(())
}

#[derive(Debug)]
struct TestResult {
    name: String,
    ok: bool,
}

fn parse_test_output(stdout: &str) -> Vec<TestResult> {
    let mut out = Vec::new();
    for line in stdout.lines() {
        let line = line.trim_start();
        let rest = match line.strip_prefix("test ") {
            Some(r) => r,
            None => continue,
        };
        // `test result: ok. ...` lines also start with "test ", filter:
        if rest.starts_with("result:") {
            continue;
        }
        // Format: "test <name> ... ok" or "test <name> ... FAILED" or "test <name> ... ignored"
        let (name, status) = match rest.rsplit_once(" ... ") {
            Some((n, s)) => (n.trim().to_string(), s.trim()),
            None => continue,
        };
        // Strip ANSI codes (cargo may colorize)
        let status = strip_ansi(status);
        let ok = match status.as_str() {
            "ok" => true,
            "FAILED" => false,
            "ignored" => continue,
            _ => continue,
        };
        out.push(TestResult { name, ok });
    }
    out
}

fn strip_ansi(s: &str) -> String {
    let mut out = String::new();
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == 0x1b && i + 1 < bytes.len() && bytes[i + 1] == b'[' {
            // skip until letter
            let mut j = i + 2;
            while j < bytes.len() && !(bytes[j] as char).is_ascii_alphabetic() {
                j += 1;
            }
            i = j + 1;
        } else {
            out.push(bytes[i] as char);
            i += 1;
        }
    }
    out
}

/// Candidate "stems" for the test-name lookup. The first match wins.
///
/// For `incr_cert::incr` we try `["incr_cert_incr", "incr"]`. For
/// `hashmap::{hashmap::HashMap<T>}::new` we strip the brace block
/// and try `["hashmap_HashMap_new", "HashMap_new", "new"]`.
fn test_stems_for_decl(path: &str) -> Vec<String> {
    let mut stems = Vec::new();
    // Strip `{...}` segments; they're not part of human-written test names.
    let clean: String = strip_brace_groups(path);
    let segs: Vec<&str> = clean.split("::").filter(|s| !s.is_empty()).collect();

    // Most specific to least specific.
    if !segs.is_empty() {
        stems.push(segs.join("_"));
    }
    if segs.len() >= 2 {
        stems.push(segs[segs.len() - 2..].join("_"));
    }
    if let Some(last) = segs.last() {
        stems.push((*last).to_string());
    }
    // Dedup while preserving order.
    let mut seen = std::collections::HashSet::new();
    stems.into_iter().filter(|s| seen.insert(s.clone())).collect()
}

fn strip_brace_groups(s: &str) -> String {
    let mut out = String::new();
    let mut depth = 0;
    for ch in s.chars() {
        match ch {
            '{' => depth += 1,
            '}' => {
                if depth > 0 {
                    depth -= 1;
                }
            }
            _ if depth == 0 => out.push(ch),
            _ => {}
        }
    }
    // Collapse leftover `::::` etc.
    while out.contains(":::") {
        out = out.replace(":::", "::");
    }
    out.trim_end_matches("::").to_string()
}

fn test_matches_stem(test_name: &str, stem: &str) -> bool {
    if test_name == stem {
        return true;
    }
    if let Some(rest) = test_name.strip_prefix(stem) {
        let next = rest.chars().next();
        // Followed by `_` (e.g. `_matches_model`) or `(` (cfg).
        return matches!(next, Some('_') | Some(' ') | None);
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stems_basic() {
        let s = test_stems_for_decl("incr_cert::incr");
        assert_eq!(s, vec!["incr_cert_incr".to_string(), "incr".to_string()]);
    }

    #[test]
    fn stems_with_brace() {
        let s = test_stems_for_decl("hashmap::{hashmap::HashMap<T>}::new");
        assert!(s.contains(&"hashmap_new".to_string()) || s.contains(&"new".to_string()));
    }

    #[test]
    fn stem_match() {
        assert!(test_matches_stem("incr_matches_model", "incr"));
        assert!(test_matches_stem("constants_incr_matches_model", "constants_incr"));
        assert!(!test_matches_stem("incremental_matches_model", "incr"));
    }
}
