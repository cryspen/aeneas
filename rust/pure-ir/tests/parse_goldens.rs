//! Phase-3 golden test: for a small representative subset of fixtures
//! (5 fixtures × 3 stages = 15 JSON files), regenerate the dump via
//! `bin/aeneas`, normalise it (strip absolute paths from `span.file`
//! and re-serialise through `serde_json::Value` to canonicalise field
//! order), and assert byte-for-byte equality with the committed copy
//! under `tests/golden/`.
//!
//! Goldens regenerate with:
//!     PURE_IR_BLESS=1 cargo test --test parse_goldens
//! That env var causes the test to overwrite the committed file
//! instead of comparing.
//!
//! Why golden? The 89×3 sweep catches schema drift broadly but only
//! checks "does it parse". Goldens lock the exact shape of a few
//! IR-shape-representative fixtures so any unintended change to the
//! emitter shows up as a diff in CI.

use std::path::{Path, PathBuf};
use std::process::Command;

const FIXTURES: &[&str] = &[
    "incr_cert",
    "loops_simple",
    "traits_basic",
    "enums_basic",
    "arrays_defs",
];

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

/// Walk a `serde_json::Value` and strip everything up to and including
/// `tests/src/` from any string value living under a `"file"` key.
/// Aeneas emits absolute on-disk paths in `item_meta.span.file`; goldens
/// would diff per machine without this normalisation.
fn normalise(v: &mut serde_json::Value) {
    match v {
        serde_json::Value::Object(map) => {
            for (k, val) in map.iter_mut() {
                if k == "file" {
                    if let serde_json::Value::String(s) = val {
                        if let Some(idx) = s.find("tests/src/") {
                            *s = s[idx + "tests/src/".len()..].to_string();
                        } else if let Some(idx) = s.find("tests/llbc/") {
                            *s = s[idx + "tests/llbc/".len()..].to_string();
                        }
                    }
                } else {
                    normalise(val);
                }
            }
        }
        serde_json::Value::Array(items) => {
            for it in items {
                normalise(it);
            }
        }
        _ => {}
    }
}

fn dump_and_normalise(
    aeneas_bin: &Path,
    repo: &Path,
    fixture: &str,
    stage: &str,
) -> String {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dest = tmp.path().to_string_lossy().into_owned();

    let llbc = repo
        .join("tests")
        .join("llbc")
        .join(format!("{fixture}.llbc"));

    let _ = Command::new(aeneas_bin)
        .args([
            "-backend",
            "lean",
            "-dest",
            &dest,
            "-dump-pure-ir",
            &format!("{stage}:{dest}"),
            llbc.to_str().unwrap(),
        ])
        .stderr(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .output()
        .expect("spawn aeneas");

    let dump_path = tmp.path().join(format!("{fixture}.pure.json"));
    let src = std::fs::read_to_string(&dump_path)
        .unwrap_or_else(|e| panic!("read {}: {e}", dump_path.display()));

    let mut v: serde_json::Value = serde_json::from_str(&src)
        .unwrap_or_else(|e| panic!("parse {fixture}/{stage}: {e}"));
    normalise(&mut v);
    // Pretty-print so diffs are line-oriented and human-readable.
    let mut out = serde_json::to_string_pretty(&v).expect("serialize");
    out.push('\n');
    out
}

#[test]
fn golden_fixtures_three_stages() {
    let repo = repo_root();
    let aeneas_bin = repo.join("bin").join("aeneas");
    assert!(
        aeneas_bin.exists(),
        "expected {} - did you run `gmake build-bin-dir`?",
        aeneas_bin.display()
    );

    let golden_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("golden");
    let bless = std::env::var("PURE_IR_BLESS").is_ok();

    let mut failures: Vec<String> = Vec::new();

    for fixture in FIXTURES {
        for stage in STAGES {
            let actual = dump_and_normalise(&aeneas_bin, &repo, fixture, stage);
            let golden_path =
                golden_dir.join(format!("{fixture}.{stage}.pure.json"));

            if bless {
                std::fs::write(&golden_path, &actual).unwrap_or_else(|e| {
                    panic!("write {}: {e}", golden_path.display())
                });
                eprintln!("blessed {}", golden_path.display());
                continue;
            }

            let expected = match std::fs::read_to_string(&golden_path) {
                Ok(s) => s,
                Err(e) => {
                    failures.push(format!(
                        "{fixture} [{stage}]: golden missing at {}: {e} \
                         (regenerate with PURE_IR_BLESS=1 cargo test \
                         --test parse_goldens)",
                        golden_path.display()
                    ));
                    continue;
                }
            };

            if expected != actual {
                // Surface a short head/length summary so CI logs aren't drowned.
                failures.push(format!(
                    "{fixture} [{stage}]: golden diff (expected {} bytes, \
                     got {} bytes). Regenerate with PURE_IR_BLESS=1 cargo \
                     test --test parse_goldens",
                    expected.len(),
                    actual.len()
                ));
            }
        }
    }

    if !failures.is_empty() {
        panic!(
            "{} of {} golden(s) failed:\n{}",
            failures.len(),
            FIXTURES.len() * STAGES.len(),
            failures.join("\n")
        );
    }
}
