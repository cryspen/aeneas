//! End-to-end smoke test for the Phase-1 Pure-IR pipeline.
//!
//! Spawns `bin/aeneas` to dump `tests/llbc/incr_cert.llbc` as JSON,
//! then parses the output with this crate and checks the shape.

use std::path::PathBuf;
use std::process::Command;

/// Walk up from the crate dir to find the Aeneas repo root (the
/// directory that contains `bin/aeneas` and `tests/llbc/`). The repo
/// can override this with `AENEAS_REPO`.
fn repo_root() -> PathBuf {
    if let Ok(p) = std::env::var("AENEAS_REPO") {
        return PathBuf::from(p);
    }
    // CARGO_MANIFEST_DIR points at rust/pure-ir/; the repo is two
    // directories above.
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest
        .ancestors()
        .nth(2)
        .expect("CARGO_MANIFEST_DIR has no grandparent")
        .to_path_buf()
}

#[test]
fn dump_and_parse_incr_cert() {
    let repo = repo_root();
    let aeneas_bin = repo.join("bin").join("aeneas");
    assert!(
        aeneas_bin.exists(),
        "expected {} to exist — did you run `gmake build`?",
        aeneas_bin.display()
    );
    let llbc = repo.join("tests").join("llbc").join("incr_cert.llbc");
    assert!(llbc.exists(), "missing fixture: {}", llbc.display());

    let tmp = tempfile::tempdir().expect("tempdir");
    let dest = tmp.path().to_string_lossy().into_owned();

    let status = Command::new(&aeneas_bin)
        .args([
            "-backend",
            "lean",
            "-dest",
            &dest,
            "-dump-pure-ir",
            &format!("post-s2p:{}", dest),
            llbc.to_str().unwrap(),
        ])
        .status()
        .expect("spawn aeneas");
    assert!(status.success(), "aeneas exited non-zero: {status:?}");

    let dump_path = tmp.path().join("incr_cert.pure.json");
    let src = std::fs::read_to_string(&dump_path).unwrap_or_else(|e| {
        panic!("reading {}: {e}", dump_path.display());
    });

    let crate_ir = pure_ir::parse(&src).expect("parse failed");

    assert_eq!(crate_ir.pure_ir_fmt_version, 1);
    assert_eq!(crate_ir.stage, "post-s2p");
    assert_eq!(crate_ir.crate_name, "incr_cert");
    assert!(
        !crate_ir.fun_decls.is_empty(),
        "expected at least one fn decl; got {:#?}",
        crate_ir.fun_decls
    );
    let names: Vec<&String> = crate_ir.fun_decls.iter().map(|f| &f.name).collect();
    assert!(
        names.iter().any(|n| n.contains("incr")),
        "expected at least one fn name to mention 'incr'; got {names:?}"
    );
}
