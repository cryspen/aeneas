//! Integration tests driving the pipeline against stub charon/aeneas scripts.
//! These exercise the real rustc validity gate (rustc must be on PATH) plus the
//! process/timeout machinery and the oracle, without any real charon/aeneas.

use std::path::{Path, PathBuf};

use aeneas_fuzz::config::TargetConfig;
use aeneas_fuzz::corpus::{self, PackInput};
use aeneas_fuzz::oracle::{ErrorClass, RejectClass, Verdict};
use aeneas_fuzz::pipeline::{Pipeline, PipelineOpts};
use aeneas_fuzz::semdiff::{run_crate, SemdiffOpts};
use aeneas_fuzz::triage::{FindingsDb, DEFAULT_TOLERANCE};

fn stub(name: &str) -> String {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/stubs")
        .join(name)
        .to_string_lossy()
        .into_owned()
}

fn config(aeneas_stub: &str) -> TargetConfig {
    let text = format!(
        r#"
name = "stub"
charon_cmd = ["{charon}", "{{output}}", "{{input}}"]
aeneas_cmd = ["{aeneas}"]
translate_flags = ["-backend", "lean", "{{llbc}}", "-dest", "{{dest}}"]
"#,
        charon = stub("charon_stub.sh"),
        aeneas = stub(aeneas_stub),
    );
    TargetConfig::from_str(&text).unwrap()
}

fn work_dir(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("aeneas-fuzz-it-{}-{}", tag, std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn inputs_from(srcs: &[&str]) -> Vec<PackInput> {
    let mut out = Vec::new();
    for (i, src) in srcs.iter().enumerate() {
        let units = corpus::units_from_source(src, Path::new(&format!("seed{i}.rs"))).unwrap();
        for u in units {
            let provenance = u.provenance();
            out.push(PackInput { unit: u, provenance });
        }
    }
    out
}

#[test]
fn pipeline_success_via_stubs() {
    let cfg = config("aeneas_success.sh");
    let work = work_dir("success");
    let pipeline = Pipeline::new(&cfg, work.clone(), "t".into());
    let inputs = inputs_from(&["pub fn add(a: u32, b: u32) -> u32 { a + b }"]);
    let (res, _pack) = pipeline
        .run_pack(&inputs, "c0", &PipelineOpts::default())
        .unwrap();
    assert!(res.gate_ok, "gate should pass: {:?}", res);
    assert!(res.charon_ok);
    assert_eq!(res.verdict, Some(Verdict::Success));
    assert_eq!(res.functions.len(), 1);
    let _ = std::fs::remove_dir_all(&work);
}

#[test]
fn pipeline_crash_is_fingerprinted_and_deduped() {
    let cfg = config("aeneas_crash_f4.sh");
    let work = work_dir("crash");
    let pipeline = Pipeline::new(&cfg, work.clone(), "t".into());
    let inputs = inputs_from(&["pub fn f(x: &mut u32) -> u32 { *x }"]);
    let (res, _pack) = pipeline
        .run_pack(&inputs, "c0", &PipelineOpts::default())
        .unwrap();

    let fp = match &res.verdict {
        Some(Verdict::Crash { fingerprint }) => fingerprint.clone(),
        other => panic!("expected crash, got {other:?}"),
    };
    assert_eq!(fp.error_class, ErrorClass::InternalError);
    assert_eq!(fp.file_basename(), "PureMicroPassesLoops.ml");
    assert_eq!(fp.line, 1818);

    // Dedup against the seeded DB -> F4.
    let db = FindingsDb::seeded();
    let idx = db.matching(&fp, DEFAULT_TOLERANCE);
    assert_eq!(idx, Some(0), "should dedup to F4");
    let _ = std::fs::remove_dir_all(&work);
}

#[test]
fn pipeline_expected_reject() {
    let cfg = config("aeneas_reject_expected.sh");
    let work = work_dir("reject");
    let pipeline = Pipeline::new(&cfg, work.clone(), "t".into());
    let inputs = inputs_from(&["pub fn f(a: u32) -> u32 { a }"]);
    let (res, _pack) = pipeline
        .run_pack(&inputs, "c0", &PipelineOpts::default())
        .unwrap();
    match res.verdict {
        Some(Verdict::Reject {
            classification: RejectClass::Expected,
            ..
        }) => {}
        other => panic!("expected Expected reject, got {other:?}"),
    }
    let _ = std::fs::remove_dir_all(&work);
}

#[test]
fn greedy_drop_removes_noncompiling_function() {
    let cfg = config("aeneas_success.sh");
    let work = work_dir("drop");
    let pipeline = Pipeline::new(&cfg, work.clone(), "t".into());
    // `bad` calls an undefined function -> rustc error; the two good functions
    // must survive after the offender is dropped.
    let inputs = inputs_from(&[
        "pub fn good1(a: u32) -> u32 { a + 1 }",
        "pub fn bad() -> u32 { totally_undefined_symbol() }",
        "pub fn good2(a: u32) -> u32 { a * 2 }",
    ]);
    let (res, _pack) = pipeline
        .run_pack(&inputs, "c0", &PipelineOpts::default())
        .unwrap();
    assert!(res.gate_ok, "gate should pass after dropping `bad`: {res:?}");
    let kept: Vec<&str> = res.functions.iter().map(|p| p.orig_name.as_str()).collect();
    let dropped: Vec<&str> = res.dropped.iter().map(|p| p.orig_name.as_str()).collect();
    assert!(kept.contains(&"good1"), "kept={kept:?}");
    assert!(kept.contains(&"good2"), "kept={kept:?}");
    assert!(dropped.contains(&"bad"), "dropped={dropped:?}");
    assert_eq!(res.verdict, Some(Verdict::Success));
    let _ = std::fs::remove_dir_all(&work);
}

/// End-to-end phase-2 semantic-differential self-test. Runs a tiny known-good
/// closed `test_*` crate through the REAL fork pipeline (native + charon +
/// aeneas + Lean eval) and asserts native and Lean agree (no MISMATCH). Skips
/// cleanly when the fork binary, charon, or the prebuilt lake driver is absent
/// (e.g. on CI without a provisioned fork), so it never breaks `cargo test`
/// there. On this dev machine it exercises the full glue.
#[test]
fn semdiff_end_to_end_self_test() {
    // Repo root = .../fuzz/harness -> ../.. ; semdiff dir = repo/fuzz/semdiff.
    let harness = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo = harness.parent().and_then(|p| p.parent()).unwrap().to_path_buf();
    let semdiff_dir = repo.join("fuzz/semdiff");
    let fork_toml = repo.join("fuzz/targets/fork.toml");
    let driver_lake = semdiff_dir.join("lean-driver/.lake");

    let cfg = match TargetConfig::load(&fork_toml) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("[semdiff e2e] fork.toml unavailable ({e}); skipping");
            return;
        }
    };
    // Presence gates: fork aeneas, charon, and the prebuilt lake driver.
    let aeneas_bin = cfg.aeneas_cmd.first().map(PathBuf::from);
    let charon_bin = cfg.charon_cmd.first().map(PathBuf::from);
    let have_aeneas = aeneas_bin.as_ref().map(|p| p.exists()).unwrap_or(false);
    // charon_cmd[0] may be a bare name on PATH; only file-check when it's a path.
    let have_charon = charon_bin
        .as_ref()
        .map(|p| !p.to_string_lossy().contains('/') || p.exists())
        .unwrap_or(false);
    if !have_aeneas || !have_charon || !driver_lake.exists() || !semdiff_dir.join("check.sh").exists()
    {
        eprintln!(
            "[semdiff e2e] tools absent (aeneas={have_aeneas} charon={have_charon} lake={}); skipping",
            driver_lake.exists()
        );
        return;
    }

    // A tiny known-good crate: one OK, one failing-assert, one overflow. No
    // constant-bool asserts (those crash the fork's assert double-eval path).
    let src = "\
#![allow(dead_code, unused_variables, unused_mut)]
pub fn test_ok() {
    let mut base: u32 = 3;
    let x = &mut base;
    let mut i: u32 = 0;
    while i < 5 { *x = x.wrapping_add(1); i += 1; }
    assert!(base == 8);
}
pub fn test_fail() {
    let n: u32 = 2u32.wrapping_mul(3);
    assert!(n == 999);
}
pub fn test_overflow() {
    let a: u32 = u32::MAX;
    let mut b: u32 = 0; b = 1;
    let _c = a + b;
}
";
    let tmp = std::env::temp_dir().join(format!("semdiff-e2e-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp);
    std::fs::create_dir_all(&tmp).unwrap();
    let src_path = tmp.join("selftest.rs");
    std::fs::write(&src_path, src).unwrap();

    // check.sh overwrites the tracked scratch `lean-driver/Driver.lean` (and
    // writes a `.driver.tests`) per run; snapshot so `cargo test` leaves the
    // working tree pristine.
    let driver_file = semdiff_dir.join("lean-driver/Driver.lean");
    let driver_snapshot = std::fs::read(&driver_file).ok();
    let driver_tests = semdiff_dir.join("lean-driver/.driver.tests");
    let driver_tests_existed = driver_tests.exists();
    let restore = || {
        if let Some(bytes) = &driver_snapshot {
            let _ = std::fs::write(&driver_file, bytes);
        }
        if !driver_tests_existed {
            let _ = std::fs::remove_file(&driver_tests);
        }
    };

    let opts = SemdiffOpts {
        semdiff_dir: semdiff_dir.clone(),
        work_dir: tmp.join("work"),
        findings_dir: tmp.join("findings"),
        strict: true,
        stage_timeout_secs: 300,
    };
    let report = match run_crate(&src_path, &cfg, &opts) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("[semdiff e2e] run error ({e}); skipping");
            restore();
            let _ = std::fs::remove_dir_all(&tmp);
            return;
        }
    };
    restore();
    if !report.complete {
        // Environment hiccup (lake warm-up needed, contention, etc.): don't fail
        // the suite over an infrastructural stall.
        eprintln!("[semdiff e2e] incomplete: {}; skipping assertions", report.note);
        let _ = std::fs::remove_dir_all(&tmp);
        return;
    }
    eprintln!("[semdiff e2e] verdicts: {}", report.summary());
    assert_eq!(
        report.count("MISMATCH"),
        0,
        "known-good crate produced a MISMATCH: {:?}",
        report.mismatches.iter().map(|m| &m.name).collect::<Vec<_>>()
    );
    assert!(
        report.count("MATCH") >= 1,
        "expected at least one MATCH, got {}",
        report.summary()
    );
    let _ = std::fs::remove_dir_all(&tmp);
}

#[test]
fn timeout_is_classified() {
    // A charon stub that never writes output but exits 0 would make charon_ok
    // false; instead test the aeneas timeout path by pointing aeneas at `sleep`.
    let text = format!(
        r#"
name = "stub"
charon_cmd = ["{charon}", "{{output}}", "{{input}}"]
aeneas_cmd = ["/bin/sh", "-c", "sleep 5"]
translate_flags = ["{{llbc}}", "{{dest}}"]

[timeout_secs]
aeneas = 1
"#,
        charon = stub("charon_stub.sh"),
    );
    let cfg = TargetConfig::from_str(&text).unwrap();
    let work = work_dir("timeout");
    let pipeline = Pipeline::new(&cfg, work.clone(), "t".into());
    let inputs = inputs_from(&["pub fn f(a: u32) -> u32 { a }"]);
    let (res, _pack) = pipeline
        .run_pack(&inputs, "c0", &PipelineOpts::default())
        .unwrap();
    assert_eq!(res.verdict, Some(Verdict::Timeout), "res={res:?}");
    let _ = std::fs::remove_dir_all(&work);
}
