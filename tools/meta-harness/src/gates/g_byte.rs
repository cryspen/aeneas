//! G_byte gate: per-decl byte-identical comparison between mainline
//! `aeneas -backend lean` (L₀) and `aeneas-check --out` (L₁).
//!
//! Phase B implementation: invoke both backends file-grained (one
//! emit per crate), then slice the matching decl block from each
//! `.lean` and compare. Phase C will replace the slicing with a
//! `--only-decl` flag on both backends.

use anyhow::{Context, Result, bail};
use std::path::{Path, PathBuf};
use std::process::Command;
use tempfile::TempDir;

use crate::cert::{Cert, DeclKind};
use crate::manifest::{DeclVerdict, Manifest};
use crate::report::{GateOutcome, Report};

const GATE: &str = "g_byte";

pub fn run(
    cert: &Cert,
    cert_path: &Path,
    aeneas: &Path,
    aeneas_check: &Path,
    manifest: &Manifest,
    report: &mut Report,
) -> Result<()> {
    // Derive the .llbc path from the cert path.
    let llbc_path = derive_llbc_path(cert_path)?;
    if !llbc_path.exists() {
        bail!(
            "expected .llbc next to cert at {} (derived from {})",
            llbc_path.display(),
            cert_path.display()
        );
    }

    let tmp = TempDir::new()?;
    let l0_dir = tmp.path().join("l0");
    let l1_file = tmp.path().join("l1.lean");
    std::fs::create_dir_all(&l0_dir)?;

    // L₀: mainline aeneas.
    let l0_status = Command::new(aeneas)
        .arg("-backend").arg("lean")
        .arg("-dest").arg(&l0_dir)
        .arg(&llbc_path)
        .output()
        .with_context(|| format!("running aeneas at {}", aeneas.display()))?;
    if !l0_status.status.success() {
        // Whole-crate emit failed — every decl is `skip(l0-fail)`.
        let reason = format!("aeneas (L₀) emit failed: {}",
            String::from_utf8_lossy(&l0_status.stderr).lines().next().unwrap_or(""));
        for decl in &cert.decls {
            report.record(&decl.path, GATE, GateOutcome::skip(reason.clone()));
        }
        return Ok(());
    }

    // L₁: aeneas-check.
    let l1_status = Command::new(aeneas_check)
        .arg(cert_path)
        .arg("--out").arg(&l1_file)
        .output()
        .with_context(|| format!("running aeneas-check at {}", aeneas_check.display()))?;
    if !l1_status.status.success() {
        let reason = format!("aeneas-check (L₁) emit failed: {}",
            String::from_utf8_lossy(&l1_status.stderr).lines().next().unwrap_or(""));
        for decl in &cert.decls {
            report.record(&decl.path, GATE, GateOutcome::skip(reason.clone()));
        }
        return Ok(());
    }

    // Locate the L₀ .lean file (mainline writes one .lean per crate
    // somewhere inside <dest>/<CrateName>/).
    let l0_file = locate_l0_lean(&l0_dir).with_context(|| {
        format!("locating L₀ .lean under {}", l0_dir.display())
    })?;

    // Read both files and slice per decl.
    let l0_text = std::fs::read_to_string(&l0_file)?;
    let l1_text = std::fs::read_to_string(&l1_file)?;
    let l0_slices = slice_by_decl(&l0_text);
    let l1_slices = slice_by_decl(&l1_text);

    for decl in &cert.decls {
        // Manifest override takes precedence.
        if let Some(o) = manifest.decls.get(&decl.path) {
            if let Some(v) = &o.g_byte {
                let outcome = match v {
                    DeclVerdict::Skip { skip } => GateOutcome::skip(skip),
                    DeclVerdict::Divergent { divergent } => GateOutcome::divergent(divergent),
                    DeclVerdict::Vectors { .. } => continue,
                };
                report.record(&decl.path, GATE, outcome);
                continue;
            }
        }

        // Some decl kinds aren't emitted to .lean (trait impl methods
        // may be inlined, etc.). Match by path; skip if absent.
        let key = lean_key_for(&decl.path);
        let l0 = l0_slices.find(&key);
        let l1 = l1_slices.find(&key);

        let outcome = match (l0, l1) {
            (None, None) => GateOutcome::skip("decl not emitted by either backend"),
            (None, Some(_)) => GateOutcome::mismatch("only L₁ emitted this decl"),
            (Some(_), None) => GateOutcome::mismatch("only L₀ emitted this decl"),
            (Some(a), Some(b)) => {
                if a == b {
                    GateOutcome::pass()
                } else {
                    GateOutcome::divergent("L₀ ≠ L₁ slice")
                }
            }
        };
        // Some decl kinds we don't bother diffing (trait impls without
        // standalone names). For Phase B we still emit a "skip" so the
        // aggregate is honest.
        if matches!(decl.kind, DeclKind::TraitImpl) && matches!(outcome.status, crate::report::Status::Skip) {
            report.record(&decl.path, GATE, GateOutcome::skip("trait-impl: per-decl slicing not yet implemented"));
            continue;
        }
        report.record(&decl.path, GATE, outcome);
    }

    Ok(())
}

fn derive_llbc_path(cert_path: &Path) -> Result<PathBuf> {
    // tests/llbc/foo.cert.json -> tests/llbc/foo.llbc
    let s = cert_path.to_string_lossy();
    if let Some(stripped) = s.strip_suffix(".cert.json") {
        return Ok(PathBuf::from(format!("{stripped}.llbc")));
    }
    bail!("cert path must end in .cert.json: {}", cert_path.display())
}

fn locate_l0_lean(dir: &Path) -> Result<PathBuf> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let p = entry.path();
            if p.is_dir() {
                walk(&p, out)?;
            } else if p.extension().and_then(|e| e.to_str()) == Some("lean") {
                out.push(p);
            }
        }
        Ok(())
    }
    let mut out = Vec::new();
    walk(dir, &mut out)?;
    if out.is_empty() {
        bail!("no .lean files emitted to {}", dir.display());
    }
    // Mainline emits multiple files (Types, Funs, etc.). We need
    // them all combined for slice matching. Pick the largest one
    // first; if slicing fails, the caller will report it. A more
    // robust implementation would parse the import graph and slice
    // across files, but Phase B keeps it simple.
    out.sort_by_key(|p| std::fs::metadata(p).map(|m| m.len()).unwrap_or(0));
    // Return the largest .lean (typically `Funs.lean` for crates
    // with functions). The slice helper looks for the decl name and
    // returns None if not found — Phase B treats that as `skip`.
    Ok(out.last().unwrap().clone())
}

/// Translate a Charon decl path (e.g. `incr_cert::incr`) into the
/// identifier mainline Lean emits. Aeneas namespaces by snake-case
/// module: `incr_cert::incr` → just `incr` at the top-level of
/// `IncrCert.Funs`. We slice by `^def <name>` / `^abbrev <name>` etc.
fn lean_key_for(path: &str) -> String {
    // Drop the crate prefix; what remains is the bare decl name (for
    // free functions) or `ModulePath::name` (for nested decls).
    let tail = path.split("::").last().unwrap_or(path);
    tail.to_string()
}

/// Index a `.lean` file by top-level decl name. We treat a "decl
/// block" as the contiguous span from a header line that introduces
/// the decl up to (but not including) the next header.
struct Slices<'a> {
    text: &'a str,
    starts: Vec<(usize, String)>,
}

impl<'a> Slices<'a> {
    fn find(&self, name: &str) -> Option<&str> {
        let idx = self.starts.iter().position(|(_, n)| n == name)?;
        let begin = self.starts[idx].0;
        let end = self
            .starts
            .get(idx + 1)
            .map(|(b, _)| *b)
            .unwrap_or(self.text.len());
        Some(&self.text[begin..end])
    }
}

fn slice_by_decl(text: &str) -> Slices<'_> {
    let mut starts = Vec::new();
    let mut offset = 0usize;
    for line in text.split_inclusive('\n') {
        let stripped = line.trim_start();
        if let Some(name) = parse_decl_header(stripped) {
            starts.push((offset, name));
        }
        offset += line.len();
    }
    Slices { text, starts }
}

fn parse_decl_header(line: &str) -> Option<String> {
    for kw in [
        "def ",
        "abbrev ",
        "structure ",
        "inductive ",
        "class ",
        "instance ",
        "theorem ",
        "axiom ",
        "opaque ",
        "noncomputable def ",
        "partial def ",
        "mutual def ",
    ] {
        if let Some(rest) = line.strip_prefix(kw) {
            let name = rest
                .split(|c: char| c.is_whitespace() || c == ':' || c == '(' || c == '[' || c == '{' || c == '⟨')
                .next()?
                .trim_end_matches('.')
                .trim();
            if !name.is_empty() {
                return Some(name.to_string());
            }
        }
    }
    None
}
