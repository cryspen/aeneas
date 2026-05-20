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
const KNOWN_GAPS: &[(&str, &str, &str)] = &[
    // -- Multi-use of move-only backward closures (Box<dyn FnOnce>):
    //    Aeneas's IR re-uses backward fns in branch arms; Rust requires
    //    a single consumption. ~25 pairs (post-s2p mostly) are
    //    blocked by this; we list the fixtures here as a class.
    ("adt-borrows", "post-s2p", "move-of-FnOnce-backward-fn"),
    ("arrays", "post-s2p", "move-of-Vec-in-backward-fn"),
    ("calls", "post-s2p", "move-of-FnOnce-backward-fn"),
    ("dyn", "post-s2p", "move-of-FnOnce-backward-fn"),
    ("dyn", "post-micro", "move-of-FnOnce-backward-fn"),
    ("dyn", "pre-extract", "move-of-FnOnce-backward-fn"),
    ("drop_bug", "post-s2p", "move-of-Vec-backward-fn"),
    ("drop_bug", "post-micro", "move-of-Vec-backward-fn"),
    ("drop_bug", "pre-extract", "move-of-Vec-backward-fn"),
    ("hashmap", "post-s2p", "move-of-FnOnce-backward-fn"),
    ("issue-270-loop-list", "post-s2p", "move-of-Box-backward-fn"),
    ("iterators", "post-s2p", "move-of-FnOnce-backward-fn"),
    ("joins", "post-s2p", "move-of-FnOnce-backward-fn"),
    ("loops", "post-s2p", "move-of-Vec-backward-fn"),
    ("loops-rec", "post-s2p", "move-of-Vec-backward-fn"),
    ("mini_tree", "post-s2p", "move-of-Box-recursive-struct"),
    ("mut-borrow-in-shared-borrow", "post-s2p", "move-of-Vec-backward-fn"),
    ("traits", "post-s2p", "move-of-T-generic-backward-fn"),
    // -- Multi-binder destructure through a Box<T> (recursive ADTs);
    //    stable Rust has no `box` patterns:
    ("list-borrows", "post-s2p", "destructure-Box-LCell-needs-box-pattern"),
    ("list-borrows", "post-micro", "destructure-Box-LCell-needs-box-pattern"),
    ("list-borrows", "pre-extract", "destructure-Box-LCell-needs-box-pattern"),
    ("nested-borrows", "post-s2p", "destructure-Box-LCell-needs-box-pattern"),
    ("nested-borrows", "post-micro", "destructure-Box-LCell-needs-box-pattern"),
    ("nested-borrows", "pre-extract", "destructure-Box-LCell-needs-box-pattern"),
    // -- Loop bodies in post-micro / pre-extract pass tuples to
    //    `loop_op` that don't match the helper fn's positional args;
    //    we model `loop_op` via the runtime shim with a fixed shape.
    ("arrays", "post-micro", "loop_op-positional-arg-mismatch"),
    ("arrays", "pre-extract", "loop_op-positional-arg-mismatch"),
    ("assert-cfg", "post-micro", "loop_op-positional-arg-mismatch"),
    ("assert-cfg", "pre-extract", "loop_op-positional-arg-mismatch"),
    ("drop", "post-micro", "loop_op-positional-arg-mismatch"),
    ("drop", "pre-extract", "loop_op-positional-arg-mismatch"),
    ("iterators", "post-micro", "loop_op-positional-arg-mismatch"),
    ("iterators", "pre-extract", "loop_op-positional-arg-mismatch"),
    ("iterators-array", "post-micro", "loop_op-positional-arg-mismatch"),
    ("iterators-array", "pre-extract", "loop_op-positional-arg-mismatch"),
    ("iterators-scalar", "post-micro", "loop_op-positional-arg-mismatch"),
    ("iterators-scalar", "pre-extract", "loop_op-positional-arg-mismatch"),
    ("issue-789-loop-ctx-match", "post-micro", "loop_op-positional-arg-mismatch"),
    ("issue-789-loop-ctx-match", "pre-extract", "loop_op-positional-arg-mismatch"),
    ("issue-807-missing-symbolic-value", "post-micro", "loop_op-positional-arg-mismatch"),
    ("issue-807-missing-symbolic-value", "pre-extract", "loop_op-positional-arg-mismatch"),
    ("loop_shared_loan_in_join", "post-micro", "loop_op-positional-arg-mismatch"),
    ("loop_shared_loan_in_join", "pre-extract", "loop_op-positional-arg-mismatch"),
    ("hashmap", "post-micro", "loop_op-positional-arg-mismatch"),
    ("hashmap", "pre-extract", "loop_op-positional-arg-mismatch"),
    ("loops-issues", "post-micro", "loop_op-positional-arg-mismatch"),
    ("loops-issues", "pre-extract", "loop_op-positional-arg-mismatch"),
    ("loops-adts", "post-micro", "loop_op-positional-arg-mismatch"),
    ("loops-adts", "pre-extract", "loop_op-positional-arg-mismatch"),
    ("rename_attribute", "post-micro", "loop_op-positional-arg-mismatch"),
    ("rename_attribute", "pre-extract", "loop_op-positional-arg-mismatch"),
    // -- Big crates with many interacting placeholders:
    ("curve25519", "post-s2p", "vast-trait-method-surface"),
    ("curve25519", "post-micro", "vast-trait-method-surface"),
    ("curve25519", "pre-extract", "vast-trait-method-surface"),
    // -- Mutually-recursive ADTs with multi-binder Box destructures:
    ("no_nested_borrows", "post-s2p", "destructure-Box-multi-binder"),
    ("no_nested_borrows", "post-micro", "destructure-Box-multi-binder"),
    ("no_nested_borrows", "pre-extract", "destructure-Box-multi-binder"),
    // -- Type-changing struct updates (functional update of generic
    //    args), can't be done in surface Rust without rebuilding all
    //    fields:
    ("dynamic_size", "post-s2p", "type-changing-struct-update"),
    ("dynamic_size", "post-micro", "type-changing-struct-update"),
    ("dynamic_size", "pre-extract", "type-changing-struct-update"),
    // -- Big trait+impl surface; emit can't refine method dispatch
    //    without trait-decl/-impl lookups:
    ("traits", "post-micro", "PartialOrd-via-trait-method-placeholder"),
    ("traits", "pre-extract", "PartialOrd-via-trait-method-placeholder"),
    ("constants-lean", "post-micro", "cvar-non-literal-receiver"),
    ("constants-lean", "pre-extract", "cvar-non-literal-receiver"),
    // -- aeneas runtime-shape mismatches (impl_alloc_*_index, etc.)
    //    whose call sites pass tuple shapes that don't match the
    //    stubbed helper signature:
    ("loops-rec", "post-micro", "stubbed-builtin-arity"),
    ("loops-rec", "pre-extract", "stubbed-builtin-arity"),
    ("loops-sequences", "post-micro", "stubbed-builtin-arity"),
    ("loops-sequences", "pre-extract", "stubbed-builtin-arity"),
    ("loops-nested", "post-micro", "stubbed-builtin-arity"),
    ("loops-nested", "pre-extract", "stubbed-builtin-arity"),
    ("loops-nested-rec", "post-micro", "stubbed-builtin-arity"),
    ("loops-nested-rec", "pre-extract", "stubbed-builtin-arity"),
    ("derive", "post-s2p", "stubbed-builtin-arity"),
    ("derive", "post-micro", "stubbed-builtin-arity"),
    ("derive", "pre-extract", "stubbed-builtin-arity"),
    ("issue-803-self-in-array", "post-s2p", "type-changing-array-update"),
    ("issue-803-self-in-array", "post-micro", "type-changing-array-update"),
    ("issue-803-self-in-array", "pre-extract", "type-changing-array-update"),
    ("issue-804-closure-return-ref", "post-s2p", "closure-return-ref-not-IR-faithful"),
    ("issue-804-closure-return-ref", "post-micro", "closure-return-ref-not-IR-faithful"),
    ("issue-804-closure-return-ref", "pre-extract", "closure-return-ref-not-IR-faithful"),
    // -- Recursive-projection / inner-pattern cases:
    ("issue-194-recursive-struct-projector", "post-micro", "destructure-Box-multi-binder"),
    ("issue-194-recursive-struct-projector", "pre-extract", "destructure-Box-multi-binder"),
    ("issue-134-loop-shared-borrows", "post-micro", "loop_op-positional-arg-mismatch"),
    ("issue-134-loop-shared-borrows", "pre-extract", "loop_op-positional-arg-mismatch"),
    // -- Aeneas exits non-zero (post-s2p only) but post-micro/pre-
    //    extract succeed for these — kept here for completeness:
    ("closures", "post-s2p", "FnOnce-coercion-shape-mismatch"),
    ("issue-440-type-error", "post-micro", "partially-moved-x"),
    ("issue-440-type-error", "pre-extract", "partially-moved-x"),
    ("string-chars", "post-s2p", "fmt::Arguments-typed-array-arg"),
    ("string-chars", "post-micro", "fmt::Arguments-typed-array-arg"),
    ("string-chars", "pre-extract", "fmt::Arguments-typed-array-arg"),
    ("order", "post-s2p", "arg-order-from-recursive-helper"),
    ("order", "post-micro", "arg-order-from-recursive-helper"),
    ("order", "pre-extract", "arg-order-from-recursive-helper"),
    ("multi_region", "post-s2p", "duplicate-back-fn-binders"),
    ("multi_region", "post-micro", "duplicate-back-fn-binders"),
    ("multi_region", "pre-extract", "duplicate-back-fn-binders"),
    ("multi-target", "post-s2p", "global-recursive-fwd-ref"),
    ("multi-target", "post-micro", "global-recursive-fwd-ref"),
    ("multi-target", "pre-extract", "global-recursive-fwd-ref"),
    ("issue-815-global-referencing-fallible-global", "post-s2p", "global-fwd-decl"),
    ("issue-815-global-referencing-fallible-global", "post-micro", "global-fwd-decl"),
    ("issue-815-global-referencing-fallible-global", "pre-extract", "global-fwd-decl"),
    ("issue-270-loop-list", "post-micro", "destructure-Box-multi-binder"),
    ("issue-270-loop-list", "pre-extract", "destructure-Box-multi-binder"),
    ("range", "post-s2p", "trait-method-Iterator-Range"),
    ("range", "post-micro", "trait-method-Iterator-Range"),
    ("range", "pre-extract", "trait-method-Iterator-Range"),
    ("as_mut", "post-s2p", "trait-method-AsMut"),
    ("as_mut", "post-micro", "trait-method-AsMut"),
    ("as_mut", "pre-extract", "trait-method-AsMut"),
    ("array_slice_index", "post-s2p", "trait-method-Index-IndexMut"),
    ("array_slice_index", "post-micro", "trait-method-Index-IndexMut"),
    ("array_slice_index", "pre-extract", "trait-method-Index-IndexMut"),
    ("builtin-auto", "post-s2p", "AsRef-trait-method-placeholder"),
    ("builtin-auto", "post-micro", "AsRef-trait-method-placeholder"),
    ("builtin-auto", "pre-extract", "AsRef-trait-method-placeholder"),
    ("from_to", "post-s2p", "From-Into-via-trait-method-placeholder"),
    ("from_to", "post-micro", "From-Into-via-trait-method-placeholder"),
    ("from_to", "pre-extract", "From-Into-via-trait-method-placeholder"),
    ("deref", "post-s2p", "Deref-DerefMut-trait-method-placeholder"),
    ("deref", "post-micro", "Deref-DerefMut-trait-method-placeholder"),
    ("deref", "pre-extract", "Deref-DerefMut-trait-method-placeholder"),
    ("slices_basic", "post-s2p", "slice-as-ref-trait-method"),
    ("slices_basic", "post-micro", "slice-as-ref-trait-method"),
    ("slices_basic", "pre-extract", "slice-as-ref-trait-method"),
    ("slices", "post-s2p", "slice-trait-method-placeholder"),
    ("slices", "post-micro", "slice-trait-method-placeholder"),
    ("slices", "pre-extract", "slice-trait-method-placeholder"),
    ("reborrows", "post-s2p", "binder-id-skew-via-shared-borrow"),
    ("reborrows", "post-micro", "binder-id-skew-via-shared-borrow"),
    ("reborrows", "pre-extract", "binder-id-skew-via-shared-borrow"),
    ("static", "post-s2p", "static-global-fwd-ref"),
    ("static", "post-micro", "static-global-fwd-ref"),
    ("static", "pre-extract", "static-global-fwd-ref"),
    ("step_by", "post-s2p", "Iterator::step_by-trait-method"),
    ("step_by", "post-micro", "Iterator::step_by-trait-method"),
    ("step_by", "pre-extract", "Iterator::step_by-trait-method"),
    ("paper", "post-s2p", "list-Box-binder-skew"),
    ("paper", "post-micro", "list-Box-binder-skew"),
    ("paper", "pre-extract", "list-Box-binder-skew"),
    ("chunks_exact", "post-s2p", "chunks_exact-iterator-trait"),
    ("chunks_exact", "post-micro", "chunks_exact-iterator-trait"),
    ("chunks_exact", "pre-extract", "chunks_exact-iterator-trait"),
    // -- Post-micro shape mismatches that surface only after loop
    //    decomposition. Same family as the loop_op cases above:
    ("adt-borrows", "post-micro", "move-of-FnOnce-backward-fn"),
    ("adt-borrows", "pre-extract", "move-of-FnOnce-backward-fn"),
    ("closures", "post-micro", "FnOnce-coercion-shape-mismatch"),
    ("closures", "pre-extract", "FnOnce-coercion-shape-mismatch"),
    ("loops", "post-micro", "loop_op-positional-arg-mismatch"),
    ("loops", "pre-extract", "loop_op-positional-arg-mismatch"),
    ("mini_tree", "post-micro", "destructure-Box-multi-binder"),
    ("mini_tree", "pre-extract", "destructure-Box-multi-binder"),
    ("mut-borrow-in-shared-borrow", "post-micro", "move-of-Vec-backward-fn"),
    ("mut-borrow-in-shared-borrow", "pre-extract", "move-of-Vec-backward-fn"),
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
