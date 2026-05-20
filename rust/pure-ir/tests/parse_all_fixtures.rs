//! Phase-3 acceptance test: for every fixture under `tests/llbc/*.llbc`
//! and for every dump stage (`post-s2p`, `post-micro`, `pre-extract`),
//! spawn `bin/aeneas`, dump the Pure-IR JSON, and assert that
//!   1. the dump file exists,
//!   2. it contains no `"UNSUPPORTED"` substring (string-level grep),
//!   3. `pure_ir::parse` accepts it,
//!   4. the envelope reports `pure_ir_fmt_version == 2` and the
//!      correct `stage` field.
//!
//! 89 fixtures × 3 stages = 267 aeneas invocations. Wall time is
//! roughly 3× the Phase-2 single-stage sweep (~90s vs ~30s).
//!
//! Some fixtures are intentionally `known-failure` / `[!lean] skip`
//! in the test harness (e.g. `closures.llbc`, `raw_pointers.llbc`,
//! `issue-804-closure-return-ref.llbc`). For those, `bin/aeneas` exits
//! non-zero after partial translation; the Pure-IR dump is still
//! written and we verify it parses cleanly. We never fail the test on
//! a non-zero exit code — only on a malformed or missing dump.

use std::path::PathBuf;
use std::process::Command;

const STAGES: &[&str] = &["post-s2p", "post-micro", "pre-extract"];

fn repo_root() -> PathBuf {
    if let Ok(p) = std::env::var("AENEAS_REPO") {
        return PathBuf::from(p);
    }
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest
        .ancestors()
        .nth(2)
        .expect("CARGO_MANIFEST_DIR has no grandparent")
        .to_path_buf()
}

fn fixtures(repo: &std::path::Path) -> Vec<PathBuf> {
    let llbc_dir = repo.join("tests").join("llbc");
    let mut out: Vec<PathBuf> = std::fs::read_dir(&llbc_dir)
        .unwrap_or_else(|e| panic!("read_dir {}: {e}", llbc_dir.display()))
        .filter_map(|e| {
            let e = e.ok()?;
            let p = e.path();
            (p.extension().and_then(|s| s.to_str()) == Some("llbc")).then_some(p)
        })
        .collect();
    out.sort();
    out
}

#[test]
fn sweep_all_fixtures_all_stages() {
    let repo = repo_root();
    let aeneas_bin = repo.join("bin").join("aeneas");
    assert!(
        aeneas_bin.exists(),
        "expected {} to exist - did you run `gmake build-bin-dir`?",
        aeneas_bin.display()
    );

    let fixtures = fixtures(&repo);
    assert!(
        !fixtures.is_empty(),
        "no .llbc fixtures found under {}/tests/llbc/",
        repo.display()
    );

    let mut failures: Vec<String> = Vec::new();
    let mut parsed = 0usize;
    let expected = fixtures.len() * STAGES.len();

    for fixture in &fixtures {
        let name = fixture
            .file_stem()
            .and_then(|s| s.to_str())
            .expect("fixture has no stem");

        for stage in STAGES {
            let tmp = tempfile::tempdir().expect("tempdir");
            let dest = tmp.path().to_string_lossy().into_owned();

            let output = Command::new(&aeneas_bin)
                .args([
                    "-backend",
                    "lean",
                    "-dest",
                    &dest,
                    "-dump-pure-ir",
                    &format!("{stage}:{dest}"),
                    fixture.to_str().unwrap(),
                ])
                .stderr(std::process::Stdio::null())
                .stdout(std::process::Stdio::null())
                .output()
                .expect("spawn aeneas");
            // Non-zero exit is fine: some fixtures are intentionally
            // known-failure for Lean. We only care about the dump file.
            let _ = output;

            let dump_path = tmp.path().join(format!("{}.pure.json", name));
            let src = match std::fs::read_to_string(&dump_path) {
                Ok(s) => s,
                Err(e) => {
                    failures.push(format!("{name} [{stage}]: dump missing ({e})"));
                    continue;
                }
            };

            if src.contains("\"UNSUPPORTED\"") {
                let idx = src.find("\"UNSUPPORTED\"").unwrap();
                let start = idx.saturating_sub(80);
                let end = (idx + 120).min(src.len());
                failures.push(format!(
                    "{name} [{stage}]: UNSUPPORTED present near byte {idx}: …{}…",
                    &src[start..end].replace('\n', " ")
                ));
                continue;
            }

            match pure_ir::parse(&src) {
                Ok(crate_ir) => {
                    if crate_ir.pure_ir_fmt_version != 2 {
                        failures.push(format!(
                            "{name} [{stage}]: pure_ir_fmt_version != 2: got {}",
                            crate_ir.pure_ir_fmt_version
                        ));
                        continue;
                    }
                    if crate_ir.stage != *stage {
                        failures.push(format!(
                            "{name} [{stage}]: stage field != {stage:?}: got {:?}",
                            crate_ir.stage
                        ));
                        continue;
                    }
                    parsed += 1;
                }
                Err(e) => {
                    failures.push(format!("{name} [{stage}]: parse failed: {e}"));
                }
            }
        }
    }

    if !failures.is_empty() {
        panic!(
            "{} of {} fixture×stage combinations failed:\n{}",
            failures.len(),
            expected,
            failures.join("\n")
        );
    }
    assert_eq!(
        parsed, expected,
        "expected all {expected} fixture×stage combinations to parse, got {parsed}",
    );
}
