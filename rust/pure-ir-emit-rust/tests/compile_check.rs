//! Full-coverage compile-check sweep. For every `.llbc` fixture under
//! `tests/llbc/`, at every Pure-IR pipeline stage (`post-s2p`,
//! `post-micro`, `pre-extract`), emit Rust and verify that
//! `rustc --edition 2021 --crate-type lib --emit metadata` accepts it.
//!
//! Pairs we can't emit cleanly today live in [`KNOWN_GAPS`]; they are
//! skipped but reported in the test output so the residual is visible.
//! Anything not in `KNOWN_GAPS` must compile, or the test fails.
//!
//! Run with:
//! ```bash
//! cargo test -p pure-ir-emit-rust --test compile_check
//! ```
//!
//! The test requires:
//! - `bin/aeneas` built (run `make build-bin-dir` in the repo root).
//! - `rustc` on `PATH`.

use std::path::{Path, PathBuf};
use std::process::Command;

use pure_ir_emit_rust::{emit_crate, EmitOptions};

const STAGES: &[&str] = &["post-s2p", "post-micro", "pre-extract"];

/// Fixtures × stages we don't yet emit faithfully. Each entry is
/// `(fixture_name, stage, reason)`. We aim to keep this list short —
/// the canonical target is ≤15 entries (95%+ pair coverage). Larger
/// gaps point at a structural limitation in the emitter.
///
/// The bulk of remaining gaps are *move-of-FnOnce / Vec / Box
/// backward-fn* cases: Aeneas's IR re-uses backward closures in
/// branch arms, but stable Rust requires single-consumption of
/// `Box<dyn FnOnce>` / non-`Copy` values. Solving these requires
/// closure-reuse rewrites that are outside the mechanical-fix
/// buckets.
const KNOWN_GAPS: &[(&str, &str, &str)] = &[
    // -- Move-of-FnOnce-backward-fn: backward closures called more
    //    than once in branch arms (Aeneas's value-semantics model
    //    doesn't carry single-use constraints).
    ("adt-borrows", "post-micro", "move-of-FnOnce-backward-fn"),
    ("adt-borrows", "post-s2p", "move-of-FnOnce-backward-fn"),
    ("adt-borrows", "pre-extract", "move-of-FnOnce-backward-fn"),
    ("calls", "post-s2p", "move-of-FnOnce-backward-fn"),
    ("dyn", "post-micro", "move-of-FnOnce-backward-fn"),
    ("dyn", "post-s2p", "move-of-FnOnce-backward-fn"),
    ("dyn", "pre-extract", "move-of-FnOnce-backward-fn"),
    ("hashmap", "post-s2p", "move-of-FnOnce-backward-fn"),
    ("iterators", "post-s2p", "move-of-FnOnce-backward-fn"),
    ("joins", "post-s2p", "move-of-FnOnce-backward-fn"),
    // -- loop_op-positional-arg-mismatch: the runtime LoopOp shim
    //    panic-stub still accepts the call site shape, but the
    //    surrounding code uses the loop output via tuple bindings
    //    whose moved values are then re-used (a move-of-Vec
    //    derivative). Listed under the loop-op tag for continuity.
    ("arrays", "post-micro", "loop_op-positional-arg-mismatch"),
    ("arrays", "pre-extract", "loop_op-positional-arg-mismatch"),
    ("drop", "post-micro", "loop_op-positional-arg-mismatch"),
    ("drop", "pre-extract", "loop_op-positional-arg-mismatch"),
    ("hashmap", "post-micro", "loop_op-positional-arg-mismatch"),
    ("hashmap", "pre-extract", "loop_op-positional-arg-mismatch"),
    ("loops-adts", "post-micro", "loop_op-positional-arg-mismatch"),
    ("loops-adts", "pre-extract", "loop_op-positional-arg-mismatch"),
    // -- Move-of-Vec-backward-fn: same family as move-of-FnOnce but
    //    the moved value is a `Vec<T>` returned from a backward fn.
    ("drop_bug", "post-micro", "move-of-Vec-backward-fn"),
    ("drop_bug", "post-s2p", "move-of-Vec-backward-fn"),
    ("drop_bug", "pre-extract", "move-of-Vec-backward-fn"),
    ("loops", "post-s2p", "move-of-Vec-backward-fn"),
    ("loops-rec", "post-s2p", "move-of-Vec-backward-fn"),
    ("mut-borrow-in-shared-borrow", "post-micro", "move-of-Vec-backward-fn"),
    ("mut-borrow-in-shared-borrow", "post-s2p", "move-of-Vec-backward-fn"),
    ("mut-borrow-in-shared-borrow", "pre-extract", "move-of-Vec-backward-fn"),
    // -- Destructure-Box: multi-binder Box patterns (the
    //    `Pat::PAdt` inside `Box<Inner>` reaches a self-recursive
    //    field twice in the same expression — the IR's
    //    value-semantics access doesn't fit Rust's affine drop).
    ("list-borrows", "post-micro", "destructure-Box-LCell-needs-box-pattern"),
    ("list-borrows", "pre-extract", "destructure-Box-LCell-needs-box-pattern"),
    ("nested-borrows", "post-micro", "destructure-Box-LCell-needs-box-pattern"),
    ("nested-borrows", "post-s2p", "destructure-Box-LCell-needs-box-pattern"),
    ("nested-borrows", "pre-extract", "destructure-Box-LCell-needs-box-pattern"),
    // -- FnOnce-coercion-shape-mismatch: closure-typed values flow
    //    through positions that need stricter coercion.
    ("closures", "post-micro", "FnOnce-coercion-shape-mismatch"),
    ("closures", "post-s2p", "FnOnce-coercion-shape-mismatch"),
    ("closures", "pre-extract", "FnOnce-coercion-shape-mismatch"),
    // -- type-changing-array-update: functional updates of arrays
    //    that change the element type's generics.
    ("issue-803-self-in-array", "post-micro", "type-changing-array-update"),
    ("issue-803-self-in-array", "post-s2p", "type-changing-array-update"),
    ("issue-803-self-in-array", "pre-extract", "type-changing-array-update"),
    // -- PartialOrd-via-trait-method-placeholder: binop on a
    //    transparent newtype — the IR encodes `self.0 > 1` as a
    //    binop on the wrapping type, but the surface receiver is
    //    the ADT.
    ("traits", "post-micro", "PartialOrd-via-trait-method-placeholder"),
    ("traits", "pre-extract", "PartialOrd-via-trait-method-placeholder"),
    // -- arg-order-from-recursive-helper: binop applied to a
    //    transparent-newtype `Wrap` receiver (same family as
    //    PartialOrd-via-trait-method-placeholder).
    ("order", "post-micro", "arg-order-from-recursive-helper"),
    ("order", "pre-extract", "arg-order-from-recursive-helper"),
    // -- closure-return-ref-not-IR-faithful: closure returns a
    //    borrow that the IR doesn't carry.
    ("issue-804-closure-return-ref", "post-micro", "closure-return-ref-not-IR-faithful"),
    ("issue-804-closure-return-ref", "pre-extract", "closure-return-ref-not-IR-faithful"),
    // -- destructure-Box-multi-binder: transparent newtype `IdType`
    //    where the body returns `IdType<T>` but the signature wants
    //    `T` — requires a transparent-newtype unwrap rewrite.
    ("no_nested_borrows", "post-micro", "destructure-Box-multi-binder"),
    ("no_nested_borrows", "pre-extract", "destructure-Box-multi-binder"),
    // -- partially-moved-x: ADT field move from a value that is
    //    later still in scope.
    ("issue-440-type-error", "post-micro", "partially-moved-x"),
    ("issue-440-type-error", "pre-extract", "partially-moved-x"),
    // -- Single-fixture residuals (one (fixture, stage) each):
    ("issue-270-loop-list", "post-s2p", "move-of-Box-backward-fn"),
    ("mini_tree", "post-s2p", "move-of-Box-recursive-struct"),
    ("traits", "post-s2p", "move-of-T-generic-backward-fn"),
    ("arrays", "post-s2p", "move-of-Vec-in-backward-fn"),
];

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn aeneas_bin() -> PathBuf {
    repo_root().join("bin").join("aeneas")
}

fn llbc_dir() -> PathBuf {
    repo_root().join("tests").join("llbc")
}

/// Dump the Pure-IR JSON for every fixture at every stage into the
/// returned temp dir. Each stage gets its own subdir to avoid output
/// collisions (`bin/aeneas -dump-pure-ir` writes one file per crate).
fn dump_all_fixtures() -> (PathBuf, Vec<String>) {
    let tmp = std::env::temp_dir().join(format!(
        "pir-sweep-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0),
    ));
    for stage in STAGES {
        std::fs::create_dir_all(tmp.join(stage)).unwrap();
    }
    let mut fixtures = Vec::new();
    let aeneas = aeneas_bin();
    if !aeneas.exists() {
        panic!(
            "aeneas binary not found at {}: run `make build-bin-dir`",
            aeneas.display()
        );
    }
    for entry in std::fs::read_dir(llbc_dir()).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("llbc") {
            continue;
        }
        let name = path.file_stem().unwrap().to_string_lossy().to_string();
        for stage in STAGES {
            let out = tmp.join(stage);
            let dump_arg = format!("{stage}:{}", out.display());
            let _ = Command::new(&aeneas)
                .args([
                    "-backend",
                    "lean",
                    "-dest",
                    &out.display().to_string(),
                    "-dump-pure-ir",
                    &dump_arg,
                ])
                .arg(&path)
                .output()
                .expect("spawn aeneas");
        }
        fixtures.push(name);
    }
    fixtures.sort();
    (tmp, fixtures)
}

fn rustc_check(src: &str, label: &str) -> Result<(), String> {
    let dir = std::env::temp_dir().join(format!(
        "pir-compile-{}-{}",
        std::process::id(),
        label,
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
        // Pick the first `^error` line for compact reporting.
        let stderr = String::from_utf8_lossy(&output.stderr);
        let first = stderr
            .lines()
            .find(|l| l.starts_with("error"))
            .map(|l| l.to_string())
            .unwrap_or_else(|| "<no error line>".to_string());
        Err(format!("rustc rejected emit ({first}); file: {}", rs.display()))
    }
}

fn emit_one(json_path: &Path) -> Result<String, String> {
    let src = std::fs::read_to_string(json_path)
        .map_err(|e| format!("read {}: {e}", json_path.display()))?;
    let krate = pure_ir::parse(&src).map_err(|e| format!("parse JSON: {e}"))?;
    Ok(emit_crate(&krate, &EmitOptions::default()))
}

#[test]
fn all_fixtures_compile() {
    let (tmp, fixtures) = dump_all_fixtures();
    let known_gap = |fx: &str, stage: &str| -> Option<&'static str> {
        KNOWN_GAPS
            .iter()
            .find(|(f, s, _)| *f == fx && *s == stage)
            .map(|(_, _, r)| *r)
    };

    let mut total = 0usize;
    let mut passed = 0usize;
    let mut skipped = Vec::new();
    let mut failures = Vec::new();

    for fixture in &fixtures {
        for stage in STAGES {
            total += 1;
            let json = tmp.join(stage).join(format!("{fixture}.pure.json"));
            if !json.exists() {
                if let Some(reason) = known_gap(fixture, stage) {
                    skipped.push(format!("[{fixture}/{stage}] missing JSON ({reason})"));
                } else {
                    failures.push(format!(
                        "[{fixture}/{stage}] missing JSON (no KNOWN_GAPS entry)"
                    ));
                }
                continue;
            }
            let src = match emit_one(&json) {
                Ok(s) => s,
                Err(e) => {
                    if let Some(reason) = known_gap(fixture, stage) {
                        skipped.push(format!("[{fixture}/{stage}] {e} ({reason})"));
                    } else {
                        failures.push(format!("[{fixture}/{stage}] emit error: {e}"));
                    }
                    continue;
                }
            };
            let label = format!("{fixture}_{}", stage.replace('-', "_"));
            match rustc_check(&src, &label) {
                Ok(()) => {
                    passed += 1;
                }
                Err(e) => {
                    if let Some(reason) = known_gap(fixture, stage) {
                        skipped.push(format!("[{fixture}/{stage}] {e} ({reason})"));
                    } else {
                        failures.push(format!("[{fixture}/{stage}] {e}"));
                    }
                }
            }
        }
    }

    eprintln!(
        "pure-ir-emit-rust sweep: {passed}/{total} pairs PASS, {} skipped via KNOWN_GAPS, {} unexpected failures",
        skipped.len(),
        failures.len()
    );
    for s in &skipped {
        eprintln!("  SKIP {s}");
    }
    if !failures.is_empty() {
        eprintln!("Unexpected failures (extend KNOWN_GAPS or fix the emitter):");
        for f in &failures {
            eprintln!("  FAIL {f}");
        }
        panic!(
            "{} pair(s) failed without a KNOWN_GAPS entry",
            failures.len()
        );
    }
}
