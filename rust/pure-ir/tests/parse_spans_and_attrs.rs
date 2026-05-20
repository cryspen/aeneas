//! v2 acceptance test: every `fun_decl` carries a populated
//! [`ItemMeta`] (real file path + non-zero begin-line) and at least
//! one fixture round-trips a non-empty Charon `attr_info.attributes`
//! list end-to-end.
//!
//! The structural sweep (`parse_all_fixtures.rs`) only proves that
//! every dump parses. This test additionally asserts the v2 payloads
//! contain real data — file paths, line numbers, and at least one
//! attribute survives the OCaml -> JSON -> Rust trip.

use std::path::PathBuf;
use std::process::Command;

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

fn dump_and_parse(repo: &std::path::Path, fixture_stem: &str) -> pure_ir::TranslatedCrate {
    let aeneas_bin = repo.join("bin").join("aeneas");
    assert!(
        aeneas_bin.exists(),
        "expected {} to exist — did you run `gmake build`?",
        aeneas_bin.display()
    );
    let llbc = repo
        .join("tests")
        .join("llbc")
        .join(format!("{fixture_stem}.llbc"));
    assert!(llbc.exists(), "missing fixture: {}", llbc.display());

    let tmp = tempfile::tempdir().expect("tempdir");
    let dest = tmp.path().to_string_lossy().into_owned();

    let _ = Command::new(&aeneas_bin)
        .args([
            "-backend",
            "lean",
            "-dest",
            &dest,
            "-dump-pure-ir",
            &format!("post-s2p:{}", dest),
            llbc.to_str().unwrap(),
        ])
        .stderr(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .output()
        .expect("spawn aeneas");

    let dump_path = tmp.path().join(format!("{fixture_stem}.pure.json"));
    let src = std::fs::read_to_string(&dump_path)
        .unwrap_or_else(|e| panic!("reading {}: {e}", dump_path.display()));
    pure_ir::parse(&src).expect("parse failed")
}

#[test]
fn incr_cert_fun_decls_have_populated_spans() {
    let repo = repo_root();
    let ir = dump_and_parse(&repo, "incr_cert");

    assert_eq!(ir.pure_ir_fmt_version, 2);
    assert!(
        !ir.fun_decls.is_empty(),
        "incr_cert should have at least one fn"
    );

    // Every fun_decl carries a populated span: a non-empty file path
    // and a 1-based begin-line > 0.
    for fd in &ir.fun_decls {
        let span = &fd.item_meta.span;
        assert!(
            !span.file.is_empty(),
            "fun_decl {:?}: empty span.file",
            fd.name
        );
        assert!(
            span.beg_line > 0,
            "fun_decl {:?}: beg_line == 0 in span {:?}",
            fd.name,
            span
        );
    }

    // At least one fn's span points at the incr_cert.rs source file.
    let saw_incr_cert_rs = ir.fun_decls.iter().any(|fd| {
        fd.item_meta.span.file.contains("incr_cert.rs")
    });
    assert!(
        saw_incr_cert_rs,
        "expected at least one fun_decl span to mention incr_cert.rs; \
         got files: {:?}",
        ir.fun_decls
            .iter()
            .map(|fd| &fd.item_meta.span.file)
            .collect::<Vec<_>>()
    );

    // Top-level Rust fn `incr_local` is public and has a non-empty
    // source_text. (Sanity-check that v2 carries item_meta.source_text
    // through.)
    let incr_local = ir
        .fun_decls
        .iter()
        .find(|fd| fd.name.ends_with("incr_local"))
        .expect("expected fn `incr_local` in incr_cert dump");
    assert!(
        incr_local.item_meta.attr_info.public,
        "expected incr_local to be public"
    );
    assert!(
        incr_local
            .item_meta
            .source_text
            .as_deref()
            .map(|s| s.contains("incr_local"))
            .unwrap_or(false),
        "expected incr_local source_text to mention 'incr_local', got {:?}",
        incr_local.item_meta.source_text
    );
}

#[test]
fn derive_fixture_carries_non_empty_attributes() {
    // `derive.rs` uses `#[derive(...)]` heavily and pulls in stdlib
    // trait impls (Clone, PartialEq) whose item_meta carries Charon
    // attribute payloads (doc-comments + `rustc_diagnostic_item`).
    let repo = repo_root();
    let ir = dump_and_parse(&repo, "derive");

    assert_eq!(ir.pure_ir_fmt_version, 2);

    // At least one decl must ship a non-empty attributes list.
    let with_attrs = ir
        .fun_decls
        .iter()
        .filter(|fd| !fd.item_meta.attr_info.attributes.is_empty())
        .count();
    let with_attrs_types = ir
        .type_decls
        .iter()
        .filter(|td| !td.item_meta.attr_info.attributes.is_empty())
        .count();
    let total = with_attrs + with_attrs_types;
    assert!(
        total > 0,
        "expected at least one decl with a non-empty attributes list; \
         got 0 fun_decls + 0 type_decls with attrs"
    );

    // At least one decl must carry a doc-comment attribute (the
    // commonest case from stdlib pulls).
    let saw_doc_comment = ir.fun_decls.iter().any(|fd| {
        fd.item_meta
            .attr_info
            .attributes
            .iter()
            .any(|a| matches!(a, pure_ir::Attribute::AttrDocComment(_)))
    }) || ir.type_decls.iter().any(|td| {
        td.item_meta
            .attr_info
            .attributes
            .iter()
            .any(|a| matches!(a, pure_ir::Attribute::AttrDocComment(_)))
    });
    assert!(
        saw_doc_comment,
        "expected at least one AttrDocComment to survive end-to-end"
    );
}
