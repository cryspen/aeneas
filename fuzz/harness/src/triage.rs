//! Triage: fingerprint dedup against a findings DB, and repro-dir emission.
//!
//! Fingerprint matching tolerates line drift (default +/-30 lines) within the
//! same (error_class, file-basename), because raise-site line numbers differ
//! across fork/upstream builds. Exact per-target lines are recorded as observed.

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use crate::config::{substitute, TargetConfig};
use crate::oracle::{ErrorClass, Fingerprint};

/// Default line-drift tolerance for fingerprint matching.
pub const DEFAULT_TOLERANCE: u32 = 30;

/// The stored fingerprint key.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FpKey {
    pub error_class: ErrorClass,
    /// File as observed (may carry a dir prefix); matched by basename.
    pub file: String,
    pub line: u32,
}

impl FpKey {
    pub fn basename(&self) -> &str {
        self.file.rsplit(['/', '\\']).next().unwrap_or(&self.file)
    }
    pub fn from_fingerprint(fp: &Fingerprint) -> FpKey {
        FpKey {
            error_class: fp.error_class,
            file: fp.file.clone(),
            line: fp.line,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Status {
    /// Surfaced by the fuzzer, not yet triaged.
    New,
    /// Matches a previously-recorded bug (deduped).
    Known,
    /// Filed as an issue by us (F4/F5/F6 -> cryspen #22/#23/#24).
    Filed,
    /// Verified genuinely-new bug, repro + issue draft ready, not yet filed.
    ConfirmedNew,
    /// Duplicate of an existing (e.g. upstream) issue — not filable by us.
    Duplicate,
    /// An intended feature-gate rejection, not a bug (recorded so it dedups).
    ExpectedReject,
    /// Harness false positive / not actually a crash (recorded so it dedups).
    Invalid,
}

/// One deduped finding.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Finding {
    pub id: String,
    /// None for latent findings (e.g. F5) that have no crash fingerprint.
    #[serde(default)]
    pub fingerprint: Option<FpKey>,
    pub first_seen: String,
    /// target name -> exact observed raise line.
    #[serde(default)]
    pub targets_reproducing: BTreeMap<String, u32>,
    pub status: Status,
    #[serde(default)]
    pub issue_ref: Option<String>,
    #[serde(default)]
    pub repro_dir: Option<String>,
    #[serde(default)]
    pub min_source: Option<String>,
    #[serde(default)]
    pub notes: Option<String>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct FindingsDb {
    pub findings: Vec<Finding>,
}

/// True if `observed` matches `target` within `tol` lines (same class + file).
pub fn fingerprint_matches(observed: &Fingerprint, target: &Fingerprint, tol: u32) -> bool {
    observed.error_class == target.error_class
        && observed.file_basename().eq_ignore_ascii_case(target.file_basename())
        && observed.line.abs_diff(target.line) <= tol
}

fn key_matches(key: &FpKey, observed: &Fingerprint, tol: u32) -> bool {
    key.error_class == observed.error_class
        && key.basename().eq_ignore_ascii_case(observed.file_basename())
        && key.line.abs_diff(observed.line) <= tol
}

impl FindingsDb {
    /// The pre-seeded known-bug set (F4 #22, F5 #23 latent, F6 #24).
    pub fn seeded() -> FindingsDb {
        FindingsDb {
            findings: vec![
                Finding {
                    id: "F4".into(),
                    fingerprint: Some(FpKey {
                        error_class: ErrorClass::InternalError,
                        file: "pure/PureMicroPassesLoops.ml".into(),
                        line: 1818,
                    }),
                    first_seen: "2026-07-25".into(),
                    targets_reproducing: BTreeMap::new(),
                    status: Status::Filed,
                    issue_ref: Some("cryspen/aeneas#22".into()),
                    repro_dir: Some(
                        "documentation/translation-study/upstream-repros/f4-return-in-loop".into(),
                    ),
                    min_source: None,
                    notes: Some(
                        "return-in-loop crash: SymbolicToPure emits `ok (v, v)`; \
                         compute_outputs_indices_if_followed_by_ok assumes a permutation."
                            .into(),
                    ),
                },
                Finding {
                    id: "F5".into(),
                    fingerprint: None, // latent; no crash fingerprint today
                    first_seen: "2026-07-25".into(),
                    targets_reproducing: BTreeMap::new(),
                    status: Status::Filed,
                    issue_ref: Some("cryspen/aeneas#23".into()),
                    repro_dir: Some(
                        "documentation/translation-study/upstream-repros/f5-let-branching-scope"
                            .into(),
                    ),
                    min_source: None,
                    notes: Some(
                        "simplify_let_branching scope escape (latent): outputs not filtered \
                         against bound_fvars. PureMicroPassesGeneral.ml:1244-1544."
                            .into(),
                    ),
                },
                Finding {
                    id: "F6".into(),
                    fingerprint: Some(FpKey {
                        error_class: ErrorClass::Unreachable,
                        file: "interp/InterpAbs.ml".into(),
                        line: 1671,
                    }),
                    first_seen: "2026-07-25".into(),
                    targets_reproducing: BTreeMap::new(),
                    status: Status::Filed,
                    issue_ref: Some("cryspen/aeneas#24".into()),
                    repro_dir: Some(
                        "documentation/translation-study/upstream-repros/f6-inverted-guard".into(),
                    ),
                    min_source: None,
                    notes: Some(
                        "inverted can_end guard in eliminate_shared_loans \
                         (InterpReduceCollapse.ml:44-46) rejects valid programs."
                            .into(),
                    ),
                },
            ],
        }
    }

    pub fn load(path: &Path) -> FindingsDb {
        match std::fs::read_to_string(path) {
            Ok(t) => serde_json::from_str(&t).unwrap_or_else(|e| {
                eprintln!("[triage] {} parse error ({e}); using seeded db", path.display());
                FindingsDb::seeded()
            }),
            Err(_) => FindingsDb::seeded(),
        }
    }

    pub fn save(&self, path: &Path) -> Result<()> {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let json = serde_json::to_string_pretty(self)?;
        std::fs::write(path, json).with_context(|| format!("writing {}", path.display()))?;
        Ok(())
    }

    /// Find the index of a finding matching `observed` within `tol`.
    pub fn matching(&self, observed: &Fingerprint, tol: u32) -> Option<usize> {
        self.findings.iter().position(|f| {
            f.fingerprint
                .as_ref()
                .map(|k| key_matches(k, observed, tol))
                .unwrap_or(false)
        })
    }
}

/// Everything needed to record/emit a finding.
pub struct TriageInput<'a> {
    pub fingerprint: &'a Fingerprint,
    pub target_name: &'a str,
    pub cfg: &'a TargetConfig,
    /// Minimized reproducer source (`.rs`).
    pub min_source: &'a str,
    /// Combined aeneas stdout+stderr from the reproducing run.
    pub observed_output: &'a str,
    /// Provenance / oracle / classification notes.
    pub notes: &'a str,
}

#[derive(Debug)]
pub enum TriageOutcome {
    /// Matched a known/filed finding (deduped). Carries the finding id.
    Known { id: String },
    /// A brand-new finding; carries id + emitted repro dir.
    New { id: String, repro_dir: PathBuf },
}

/// Triage one crash: dedup against the DB, recording the observed line for this
/// target; emit a repro dir for genuinely new fingerprints. `findings_root` is
/// e.g. `fuzz/findings`.
pub fn triage(
    db: &mut FindingsDb,
    findings_root: &Path,
    input: &TriageInput,
    tol: u32,
) -> Result<TriageOutcome> {
    if let Some(idx) = db.matching(input.fingerprint, tol) {
        let f = &mut db.findings[idx];
        f.targets_reproducing
            .insert(input.target_name.to_string(), input.fingerprint.line);
        return Ok(TriageOutcome::Known { id: f.id.clone() });
    }

    // New finding.
    let slug = slug_for(input.fingerprint);
    let repro_dir = findings_root.join(&slug);
    emit_repro_dir(&repro_dir, input)?;

    let mut targets = BTreeMap::new();
    targets.insert(input.target_name.to_string(), input.fingerprint.line);
    let finding = Finding {
        id: slug.clone(),
        fingerprint: Some(FpKey::from_fingerprint(input.fingerprint)),
        first_seen: today(),
        targets_reproducing: targets,
        status: Status::New,
        issue_ref: None,
        repro_dir: Some(repro_dir.to_string_lossy().into_owned()),
        min_source: Some(repro_dir.join("min.rs").to_string_lossy().into_owned()),
        notes: Some(input.notes.to_string()),
    };
    db.findings.push(finding);
    Ok(TriageOutcome::New {
        id: slug,
        repro_dir,
    })
}

fn slug_for(fp: &Fingerprint) -> String {
    let file = fp
        .file_basename()
        .trim_end_matches(".ml")
        .to_ascii_lowercase();
    let class = fp.error_class.as_str().to_ascii_lowercase();
    format!("{}-{}-{}", class, sanitize(&file), fp.line)
}

fn sanitize(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_alphanumeric() { c } else { '-' })
        .collect()
}

fn emit_repro_dir(dir: &Path, input: &TriageInput) -> Result<()> {
    std::fs::create_dir_all(dir)?;
    std::fs::write(dir.join("min.rs"), input.min_source)?;
    std::fs::write(dir.join("observed-output.txt"), input.observed_output)?;

    // repro.sh built from the target config command templates.
    let charon = substitute(
        &input.cfg.charon_cmd,
        &[("input", "min.rs"), ("output", "min.llbc")],
    );
    let mut aeneas = input.cfg.aeneas_cmd.clone();
    aeneas.extend(substitute(
        &input.cfg.translate_flags,
        &[("llbc", "min.llbc"), ("dest", "out")],
    ));
    let repro = format!(
        "#!/bin/sh\n# Auto-generated reproducer for target `{}`.\n# Fingerprint: {} {}:{}\nset -e\n{}\n{}\n",
        input.target_name,
        input.fingerprint.error_class.as_str(),
        input.fingerprint.file,
        input.fingerprint.line,
        shell_join(&charon),
        shell_join(&aeneas),
    );
    let sh = dir.join("repro.sh");
    std::fs::write(&sh, repro)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perm = std::fs::metadata(&sh)?.permissions();
        perm.set_mode(0o755);
        std::fs::set_permissions(&sh, perm)?;
    }

    let notes = format!(
        "# {slug}\n\n## Fingerprint\n\n- class: {class}\n- site: {file}:{line}\n- message: {msg}\n- top frame: {frame}\n\n## Provenance / oracle\n\n{notes}\n",
        slug = slug_for(input.fingerprint),
        class = input.fingerprint.error_class.as_str(),
        file = input.fingerprint.file,
        line = input.fingerprint.line,
        msg = input.fingerprint.message,
        frame = input.fingerprint.top_frame.clone().unwrap_or_else(|| "n/a".into()),
        notes = input.notes,
    );
    std::fs::write(dir.join("notes.md"), notes)?;
    Ok(())
}

fn shell_join(argv: &[String]) -> String {
    argv.iter()
        .map(|a| {
            if a.chars().any(|c| c.is_whitespace()) {
                format!("'{}'", a.replace('\'', "'\\''"))
            } else {
                a.clone()
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// Human-readable listing of the findings DB.
pub fn format_listing(db: &FindingsDb) -> String {
    let mut out = String::new();
    out.push_str(&format!("{} finding(s):\n", db.findings.len()));
    for f in &db.findings {
        let fp = match &f.fingerprint {
            Some(k) => format!("{} {}:{}", k.error_class.as_str(), k.file, k.line),
            None => "latent (no fingerprint)".into(),
        };
        let targets: Vec<String> = f
            .targets_reproducing
            .iter()
            .map(|(t, l)| format!("{t}@{l}"))
            .collect();
        out.push_str(&format!(
            "  [{:?}] {:<28} {}  issue={}  targets=[{}]\n",
            f.status,
            f.id,
            fp,
            f.issue_ref.clone().unwrap_or_else(|| "-".into()),
            targets.join(", ")
        ));
    }
    out
}

// -- date helper (no external deps) --

fn today() -> String {
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);
    let days = secs.div_euclid(86400);
    let (y, m, d) = civil_from_days(days);
    format!("{:04}-{:02}-{:02}", y, m, d)
}

/// Howard Hinnant's days-from-civil inverse.
fn civil_from_days(z: i64) -> (i64, u32, u32) {
    let z = z + 719468;
    let era = if z >= 0 { z } else { z - 146096 } / 146097;
    let doe = z - era * 146097; // [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365; // [0, 399]
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // [0, 365]
    let mp = (5 * doy + 2) / 153; // [0, 11]
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32; // [1, 31]
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as i64; // [1, 12]
    (y + if m <= 2 { 1 } else { 0 }, m as u32, d)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fp(class: ErrorClass, file: &str, line: u32) -> Fingerprint {
        Fingerprint {
            error_class: class,
            file: file.into(),
            line,
            message: "msg".into(),
            top_frame: None,
        }
    }

    #[test]
    fn f4_dedup_within_tolerance() {
        let mut db = FindingsDb::seeded();
        // observed on a different build: line drifted by 20, dir prefix stripped.
        let observed = fp(ErrorClass::InternalError, "PureMicroPassesLoops.ml", 1838);
        let idx = db.matching(&observed, DEFAULT_TOLERANCE);
        assert_eq!(idx, Some(0));
        // record exact line
        db.findings[0]
            .targets_reproducing
            .insert("fork".into(), observed.line);
        assert_eq!(db.findings[0].targets_reproducing["fork"], 1838);
    }

    #[test]
    fn out_of_tolerance_is_new() {
        let db = FindingsDb::seeded();
        let observed = fp(ErrorClass::InternalError, "PureMicroPassesLoops.ml", 1900);
        assert_eq!(db.matching(&observed, DEFAULT_TOLERANCE), None);
    }

    #[test]
    fn class_mismatch_is_not_dedup() {
        let db = FindingsDb::seeded();
        let observed = fp(ErrorClass::Unreachable, "PureMicroPassesLoops.ml", 1818);
        assert_eq!(db.matching(&observed, DEFAULT_TOLERANCE), None);
    }

    #[test]
    fn f6_dedup() {
        let db = FindingsDb::seeded();
        let observed = fp(ErrorClass::Unreachable, "interp/InterpAbs.ml", 1665);
        assert_eq!(db.matching(&observed, DEFAULT_TOLERANCE), Some(2));
    }

    #[test]
    fn latent_finding_never_matches() {
        let db = FindingsDb::seeded();
        // F5 has no fingerprint; ensure nothing spuriously matches it.
        let observed = fp(ErrorClass::Other, "PureMicroPassesGeneral.ml", 1300);
        assert_eq!(db.matching(&observed, DEFAULT_TOLERANCE), None);
    }

    #[test]
    fn triage_emits_new_repro_dir() {
        let tmp = std::env::temp_dir().join(format!("fuzz-triage-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&tmp);
        let cfg = TargetConfig::from_str(
            "name=\"t\"\ncharon_cmd=[\"charon\",\"--dest-file\",\"{output}\",\"{input}\"]\naeneas_cmd=[\"aeneas\"]\ntranslate_flags=[\"-backend\",\"lean\",\"{llbc}\",\"-dest\",\"{dest}\"]\n",
        )
        .unwrap();
        let mut db = FindingsDb::seeded();
        let observed = fp(ErrorClass::Other, "pure/NewPass.ml", 42);
        let input = TriageInput {
            fingerprint: &observed,
            target_name: "t",
            cfg: &cfg,
            min_source: "pub fn f() {}\n",
            observed_output: "[Error] boom\n",
            notes: "provenance: seed=x",
        };
        let outcome = triage(&mut db, &tmp, &input, DEFAULT_TOLERANCE).unwrap();
        match outcome {
            TriageOutcome::New { id, repro_dir } => {
                assert!(id.contains("newpass"));
                assert!(repro_dir.join("min.rs").exists());
                assert!(repro_dir.join("repro.sh").exists());
                assert!(repro_dir.join("observed-output.txt").exists());
                assert!(repro_dir.join("notes.md").exists());
            }
            other => panic!("expected New, got {other:?}"),
        }
        assert_eq!(db.findings.len(), 4);
        let _ = std::fs::remove_dir_all(&tmp);
    }

    #[test]
    fn date_helper_sane() {
        // epoch day 0 -> 1970-01-01
        assert_eq!(civil_from_days(0), (1970, 1, 1));
        // a known date: 2000-01-01 is day 10957
        assert_eq!(civil_from_days(10957), (2000, 1, 1));
    }
}
