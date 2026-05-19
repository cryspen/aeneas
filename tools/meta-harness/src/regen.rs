//! `--regen-models` mode: walk every `*.cert.json` under `--sweep`,
//! invoke `aeneas-check --rust-model`, filter the emitted model fns
//! by signature (must match `generate::parse_simple_sig`) and body
//! (must reference only scalar locals / params / scalar primitive
//! method calls / control-flow / tuple literals / array literals over
//! allowed shapes), prefix names with `<fixture>_`, drop duplicates of
//! fns already in `src/model.rs`, and write a single combined file
//! (typically `src/auto_model.rs`).
//!
//! After each fixture's append, run `cargo check` against the
//! differential crate. If the build breaks, roll back the fns from
//! this fixture one at a time until the bisection finds the
//! offending fn(s), then drop them from the combined file.
//!
//! Productises the workflow described in commit c163314b
//! ("differential: regen model.rs (29 → 91 fns) + generator
//! hardening").

use anyhow::{Context, Result};
use serde::Deserialize;
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::generate::{
    build_struct_registry, parse_model_fns, parse_simple_sig, Shape, StructRegistry,
};

#[derive(Deserialize)]
struct RawCertSig {
    llbc_program: serde_json::Value,
}

#[derive(Debug, Default)]
pub struct RegenSummary {
    pub fns_total: usize,
    pub fns_kept: usize,
    pub skipped_sig: usize,
    pub skipped_body: usize,
    pub skipped_duplicate: usize,
    pub fns_dropped_compile: usize,
    pub fixtures_processed: usize,
    pub fixtures_failed: usize,
}

/// Top-level entry point for `--regen-models`. The `out_path` is
/// where the regenerated combined file lands. Caller is expected to
/// also wire the file into `<diff_crate>/src/lib.rs`'s `mod model`,
/// either by pointing `out_path` at `<diff_crate>/src/auto_model.rs`
/// and letting this fn patch `lib.rs`, or by handling the include
/// manually.
pub fn run(
    cert_dir: &Path,
    out_path: &Path,
    aeneas_check: &Path,
    diff_crate: &Path,
    existing_model: &Path,
) -> Result<RegenSummary> {
    // Best-effort: if `out_path` lives inside `<diff_crate>/src/` and
    // ends in `.rs`, ensure `lib.rs` includes it.
    ensure_lib_include(diff_crate, out_path)?;
    let mut certs: Vec<PathBuf> = Vec::new();
    for entry in fs::read_dir(cert_dir)
        .with_context(|| format!("reading {}", cert_dir.display()))?
    {
        let entry = entry?;
        let p = entry.path();
        if p.is_file() && p.to_string_lossy().ends_with(".cert.json") {
            certs.push(p);
        }
    }
    certs.sort();

    // Existing fns in `src/model.rs` (un-prefixed names). We'll skip
    // emitting auto fns whose `<fixture>_<short>_model` name is
    // already there.
    let existing = parse_model_fns(existing_model)?;

    let mut summary = RegenSummary::default();
    let mut out_buf = String::new();
    out_buf.push_str(HEADER);

    for cert_path in &certs {
        let fixture = fixture_name(cert_path);
        summary.fixtures_processed += 1;

        // 1. Parse cert.json: get struct registry + per-fn sigs.
        let cert_text = fs::read_to_string(cert_path)
            .with_context(|| format!("reading {}", cert_path.display()))?;
        let raw: RawCertSig = match serde_json::from_str(&cert_text) {
            Ok(r) => r,
            Err(_) => continue,
        };
        let registry = build_struct_registry(&fixture, &raw.llbc_program);
        let fn_sigs = collect_fn_sigs(&fixture, &raw.llbc_program, &registry);

        // 2. Run aeneas-check.
        let tmp = std::env::temp_dir().join(format!(
            "meta-harness-regen-{}-{}.rs",
            fixture,
            std::process::id()
        ));
        let status = Command::new(aeneas_check)
            .arg(cert_path)
            .arg("--rust-model")
            .arg(&tmp)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status();
        if !matches!(status, Ok(s) if s.success()) {
            summary.fixtures_failed += 1;
            continue;
        }
        let model_text = match fs::read_to_string(&tmp) {
            Ok(t) => t,
            Err(_) => {
                summary.fixtures_failed += 1;
                continue;
            }
        };
        let _ = fs::remove_file(&tmp);

        // 3. Parse the emitted `pub fn <name>_model(...)` blocks.
        let blocks = split_pub_fns(&model_text);
        summary.fns_total += blocks.len();

        let mut fixture_emit = String::new();
        let mut fixture_kept_fns: Vec<String> = Vec::new();

        for blk in &blocks {
            let short = match block_short_name(blk) {
                Some(s) => s,
                None => {
                    summary.skipped_body += 1;
                    continue;
                }
            };
            // Lookup sig from cert.json.
            let sig = match fn_sigs.get(&short) {
                Some(s) => s,
                None => {
                    summary.skipped_sig += 1;
                    continue;
                }
            };
            if !sig.acceptable_sig {
                summary.skipped_sig += 1;
                continue;
            }
            // Body filter.
            let body = block_body(blk).unwrap_or("");
            if !body_acceptable(body, &registry, &fixture, &sig.args, &sig.ret) {
                summary.skipped_body += 1;
                continue;
            }
            // De-duplicate. `parse_model_fns` returns the bare fn
            // ident (`bitwise_shift_u32_model`), so build the lookup
            // key with the `_model` suffix included.
            let prefixed = format!("{}_{}", fixture, short);
            let lookup = format!("{}_model", prefixed);
            if existing.contains(&lookup) {
                summary.skipped_duplicate += 1;
                continue;
            }
            let renamed = rename_to_prefixed(blk, &short, &prefixed);
            fixture_emit.push_str(&format!("\n// ---- {} ----\n", fixture));
            fixture_emit.push_str(&renamed);
            fixture_emit.push('\n');
            fixture_kept_fns.push(prefixed);
        }

        if fixture_emit.is_empty() {
            continue;
        }

        // Optimistic write: append the whole fixture, run cargo check.
        let snapshot = out_buf.clone();
        out_buf.push_str(&fixture_emit);
        fs::write(out_path, &out_buf)
            .with_context(|| format!("writing {}", out_path.display()))?;

        if cargo_check_ok(diff_crate)? {
            summary.fns_kept += fixture_kept_fns.len();
        } else {
            // Bisect per fn — restore snapshot and try one fn at a
            // time.
            eprintln!(
                "[regen] cargo check failed after appending {} fns from {}; bisecting",
                fixture_kept_fns.len(),
                fixture
            );
            out_buf = snapshot;
            let per_fn_blocks = split_emit_into_per_fn(&fixture_emit);
            for fn_block in per_fn_blocks {
                let trial = format!("{}{}", out_buf, fn_block);
                fs::write(out_path, &trial)?;
                if cargo_check_ok(diff_crate)? {
                    out_buf = trial;
                    summary.fns_kept += 1;
                } else {
                    summary.fns_dropped_compile += 1;
                }
            }
            fs::write(out_path, &out_buf)?;
        }
    }

    fs::write(out_path, &out_buf)
        .with_context(|| format!("writing {}", out_path.display()))?;
    Ok(summary)
}

#[derive(Debug, Clone)]
struct FnSigInfo {
    acceptable_sig: bool,
    args: Vec<Shape>,
    ret: Shape,
}

/// Collect per-fn signature info for fns declared in `<fixture>::`.
fn collect_fn_sigs(
    fixture: &str,
    prog: &serde_json::Value,
    registry: &StructRegistry,
) -> BTreeMap<String, FnSigInfo> {
    let mut out = BTreeMap::new();
    let Some(fns) = prog.get("fun_decls").and_then(|v| v.as_array()) else {
        return out;
    };
    for fd in fns {
        let Some(name) = fd
            .get("item_meta")
            .and_then(|m| m.get("name"))
            .and_then(|n| n.as_str())
        else {
            continue;
        };
        let prefix = format!("{fixture}::");
        if !name.starts_with(&prefix) {
            continue;
        }
        let short = &name[prefix.len()..];
        if short.contains("::") || short.contains('{') {
            continue;
        }
        let attr_pub = fd
            .get("item_meta")
            .and_then(|m| m.get("attr_info"))
            .and_then(|a| a.get("public"))
            .and_then(|b| b.as_bool())
            .unwrap_or(false);
        if !attr_pub {
            continue;
        }
        if matches!(fd.get("body"), Some(serde_json::Value::Null) | None) {
            continue;
        }
        if fd
            .get("is_global_initializer")
            .and_then(|b| b.as_bool())
            == Some(true)
        {
            continue;
        }
        let sig = fd.get("signature").cloned().unwrap_or_default();
        let (acceptable, args, ret) = match parse_simple_sig(&sig, registry) {
            Some((a, r)) => (true, a, r),
            None => (false, Vec::new(), Shape::Unit),
        };
        out.insert(
            short.to_string(),
            FnSigInfo {
                acceptable_sig: acceptable,
                args,
                ret,
            },
        );
    }
    out
}

/// Split a rust-model file into `pub fn <name>_model(...) { ... }`
/// blocks. Returns each block including the `pub fn` line through the
/// matching closing `}` (and the trailing newline).
fn split_pub_fns(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut i = 0;
    let bytes = text.as_bytes();
    while i < bytes.len() {
        // Find next `pub fn `.
        let rem = &text[i..];
        let Some(pos) = rem.find("pub fn ") else { break };
        let abs_start = i + pos;
        // Find the `{` that begins the body.
        let Some(brace_off) = text[abs_start..].find('{') else { break };
        let brace = abs_start + brace_off;
        // Brace-match.
        let Some(end) = match_braces(text, brace) else { break };
        out.push(text[abs_start..=end].to_string());
        i = end + 1;
    }
    out
}

/// Return the index of the matching `}` for the `{` at `open`.
fn match_braces(text: &str, open: usize) -> Option<usize> {
    let bytes = text.as_bytes();
    if bytes.get(open).copied() != Some(b'{') {
        return None;
    }
    let mut depth = 0usize;
    let mut in_string = false;
    let mut in_char = false;
    let mut in_line_comment = false;
    let mut in_block_comment = false;
    let mut prev: u8 = 0;
    for i in open..bytes.len() {
        let c = bytes[i];
        if in_line_comment {
            if c == b'\n' {
                in_line_comment = false;
            }
        } else if in_block_comment {
            if prev == b'*' && c == b'/' {
                in_block_comment = false;
            }
        } else if in_string {
            if c == b'"' && prev != b'\\' {
                in_string = false;
            }
        } else if in_char {
            if c == b'\'' && prev != b'\\' {
                in_char = false;
            }
        } else if c == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
            in_line_comment = true;
        } else if c == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'*' {
            in_block_comment = true;
        } else if c == b'"' {
            in_string = true;
        } else if c == b'\'' {
            in_char = true;
        } else if c == b'{' {
            depth += 1;
        } else if c == b'}' {
            depth -= 1;
            if depth == 0 {
                return Some(i);
            }
        }
        prev = c;
    }
    None
}

/// Extract the short fn name (before `_model`) from a `pub fn
/// <name>_model(...)` block.
fn block_short_name(block: &str) -> Option<String> {
    let after_pubfn = block.strip_prefix("pub fn ")?.trim_start();
    let end = after_pubfn.find(|c: char| !c.is_ascii_alphanumeric() && c != '_')?;
    let name = &after_pubfn[..end];
    let short = name.strip_suffix("_model")?;
    Some(short.to_string())
}

/// Return the inner body (between `{` and matching `}`).
fn block_body(block: &str) -> Option<&str> {
    let open = block.find('{')?;
    let close = block.rfind('}')?;
    if close <= open + 1 {
        return Some("");
    }
    Some(&block[open + 1..close])
}

/// Rename the fn declaration's `<name>_model` to `<fixture>_<name>_model`.
fn rename_to_prefixed(block: &str, short: &str, prefixed: &str) -> String {
    let pat = format!("pub fn {short}_model");
    let rep = format!("pub fn {prefixed}_model");
    block.replacen(&pat, &rep, 1)
}

/// Body filter: identify suspicious tokens that aeneas-check
/// occasionally emits (cert-internal `@`-prefixed paths, undeclared
/// types like `Vec`, `Box`, `Range`, `Slice`, `T`, etc.). The combined
/// auto_model.rs file lives inside `mod model { ... }` of the
/// differential crate; the only identifiers in scope there are the
/// fns from sibling auto_model.rs / model.rs blocks plus scalar
/// primitive types. Struct literals would need their type in scope —
/// since the per-fixture struct decls are NOT replicated into
/// auto_model.rs (the test side already carries them via
/// `<fixture>_src::` and per-fixture lib.rs modules), reject any body
/// that contains a struct literal or unqualified non-scalar path.
fn body_acceptable(
    body: &str,
    registry: &StructRegistry,
    _fixture: &str,
    _args: &[Shape],
    _ret: &Shape,
) -> bool {
    // Heuristic 1: forbid cert-internal `@`-paths.
    if body.contains('@') {
        return false;
    }
    // Heuristic 2: forbid known-bad tokens that the emitter produces
    // when it can't faithfully render a Rust construct.
    let bad_tokens = [
        "Vec<", "Box<", "Range ", "Range{", "Range {",
        "Slice::", "[T]", "[T@", "[T;",
        "dyn Fn", "move |",
        "Default::default", "PhantomData",
        "panic!", "todo!", "unimplemented!",
        "::<", // turbofish, often emitted with `T`-placeholders
        "Array::", "Slice::",
    ];
    for tok in bad_tokens {
        if body.contains(tok) {
            return false;
        }
    }
    // Heuristic 3: every `Ident::...` path-head must be a known
    // scalar primitive (e.g. `u32::wrapping_add`). Reject everything
    // else — including lowercase fixture-qualified calls like
    // `arrays::take_array_t` (which would be undeclared inside
    // `mod model`).
    let scalar_paths: HashSet<&'static str> = [
        "u8", "u16", "u32", "u64", "usize",
        "i8", "i16", "i32", "i64", "isize",
        "bool", "char",
    ]
    .iter()
    .copied()
    .collect();
    let mut struct_names: BTreeSet<String> = BTreeSet::new();
    for s in registry.values() {
        if let Shape::Struct { name, .. } = s {
            struct_names.insert(name.clone());
        }
    }
    for cap in find_path_heads(body) {
        if scalar_paths.contains(cap.as_str()) {
            continue;
        }
        return false;
    }
    // Heuristic 4: reject struct-literal heads entirely. The auto
    // file doesn't carry struct decls, so any `Foo { ... }` won't
    // resolve there. The corresponding model fn must be hand-curated
    // in `src/model.rs` (typically inside a per-fixture submodule
    // that carries its own struct decl).
    let lit_heads = find_struct_lit_heads(body);
    if !lit_heads.is_empty() {
        // Even if all heads happen to be in `struct_names`, we still
        // reject — auto_model.rs doesn't have those structs in scope.
        return false;
    }
    let _ = struct_names; // kept for future use.
    true
}

/// Find tokens `<Ident>` where `<Ident>::` appears in `body`.
fn find_path_heads(body: &str) -> Vec<String> {
    let mut out = Vec::new();
    let bytes = body.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if i + 1 < bytes.len() && bytes[i] == b':' && bytes[i + 1] == b':' {
            // Walk back to find ident start.
            let mut j = i;
            while j > 0 {
                let c = bytes[j - 1];
                if c.is_ascii_alphanumeric() || c == b'_' {
                    j -= 1;
                } else {
                    break;
                }
            }
            if j < i {
                let s = std::str::from_utf8(&bytes[j..i]).unwrap_or("");
                if !s.is_empty() {
                    out.push(s.to_string());
                }
            }
            i += 2;
        } else {
            i += 1;
        }
    }
    out
}

/// Find struct-literal heads: identifiers immediately preceding `{`
/// (with optional whitespace), where the identifier starts with an
/// uppercase letter. Skips trivial cases like control-flow keywords.
fn find_struct_lit_heads(body: &str) -> Vec<String> {
    let mut out = Vec::new();
    let bytes = body.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'{' {
            // Walk back over whitespace.
            let mut j = i;
            while j > 0 && bytes[j - 1].is_ascii_whitespace() {
                j -= 1;
            }
            // Walk back over identifier chars.
            let end = j;
            while j > 0 {
                let c = bytes[j - 1];
                if c.is_ascii_alphanumeric() || c == b'_' {
                    j -= 1;
                } else {
                    break;
                }
            }
            if j < end {
                let s = std::str::from_utf8(&bytes[j..end]).unwrap_or("");
                if !s.is_empty() && s.chars().next().map(|c| c.is_ascii_uppercase()) == Some(true) {
                    // Skip known keywords that may match (none start
                    // with uppercase in Rust except 'Self').
                    if s != "Self" {
                        out.push(s.to_string());
                    }
                }
            }
            i += 1;
        } else {
            i += 1;
        }
    }
    out
}

/// Run `cargo check --release` on the differential crate. Returns
/// `true` on success.
fn cargo_check_ok(diff_crate: &Path) -> Result<bool> {
    let manifest = diff_crate.join("Cargo.toml");
    let status = Command::new("cargo")
        .arg("check")
        .arg("--manifest-path")
        .arg(&manifest)
        .arg("--release")
        .arg("--lib")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .context("invoking cargo check")?;
    Ok(status.success())
}

/// Split the per-fixture emit text back into per-fn chunks (each
/// preceded by its `// ---- fixture ----` header — but for bisection
/// we just want chunk = `// ---- ... ----\npub fn ... { ... }\n`).
fn split_emit_into_per_fn(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    // Split on `pub fn `; the leading lines (comments) belong to the
    // following fn.
    let mut start = 0;
    let mut last_pub_fn: Option<usize> = None;
    let mut depth: i32 = 0;
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        // Detect `pub fn ` outside braces.
        if depth == 0 && text[i..].starts_with("pub fn ") {
            if let Some(_lpf) = last_pub_fn {
                // Flush previous fn block (from start to here).
                out.push(text[start..i].to_string());
                start = i;
            }
            last_pub_fn = Some(i);
        }
        match bytes[i] {
            b'{' => depth += 1,
            b'}' => depth -= 1,
            _ => {}
        }
        i += 1;
    }
    if last_pub_fn.is_some() && start < text.len() {
        out.push(text[start..].to_string());
    }
    out
}

/// If `out_path` is `<diff_crate>/src/<name>.rs`, ensure that
/// `<diff_crate>/src/lib.rs` contains `include!("<name>.rs")` inside
/// `mod model { ... }`. Idempotent.
fn ensure_lib_include(diff_crate: &Path, out_path: &Path) -> Result<()> {
    let src_dir = diff_crate.join("src");
    let lib_path = src_dir.join("lib.rs");
    if !lib_path.is_file() {
        return Ok(());
    }
    // Touch the file so canonicalize succeeds.
    if !out_path.is_file() {
        if let Some(parent) = out_path.parent() {
            let _ = fs::create_dir_all(parent);
        }
        fs::write(out_path, "")?;
    }
    // Compute the include target as a filename if `out_path` lives in
    // `<diff_crate>/src/`. Both paths must be absolute for
    // `strip_prefix` to work reliably.
    let out_canon = out_path
        .canonicalize()
        .unwrap_or_else(|_| out_path.to_path_buf());
    let src_canon = src_dir.canonicalize().unwrap_or_else(|_| src_dir.clone());
    let rel = match out_canon.strip_prefix(&src_canon) {
        Ok(r) => r.to_path_buf(),
        Err(_) => return Ok(()), // out_path is outside the crate; user wires manually.
    };
    let rel_str = rel.to_string_lossy().to_string();
    let needle = format!("include!(\"{}\")", rel_str);
    let lib_text = fs::read_to_string(&lib_path)
        .with_context(|| format!("reading {}", lib_path.display()))?;
    if lib_text.contains(&needle) {
        return Ok(());
    }
    // Locate `pub mod model {` and inject the include before its
    // closing brace.
    let Some(mod_start) = lib_text.find("pub mod model {") else {
        // No `mod model` — skip the patch; user wires by hand.
        return Ok(());
    };
    let after_decl = mod_start + "pub mod model {".len();
    let close = match_braces(&lib_text, lib_text[..after_decl].rfind('{').unwrap_or(0))
        .or_else(|| {
            // Heuristic fallback: find the first standalone `}\n` at
            // column 0 after mod_start.
            let mut i = after_decl;
            let bytes = lib_text.as_bytes();
            let mut depth = 1usize;
            while i < bytes.len() && depth > 0 {
                if bytes[i] == b'{' {
                    depth += 1;
                } else if bytes[i] == b'}' {
                    depth -= 1;
                    if depth == 0 {
                        return Some(i);
                    }
                }
                i += 1;
            }
            None
        });
    let Some(close) = close else { return Ok(()) };
    let inject = format!("    {needle};\n");
    let mut new_text = String::with_capacity(lib_text.len() + inject.len());
    new_text.push_str(&lib_text[..close]);
    new_text.push_str(&inject);
    new_text.push_str(&lib_text[close..]);
    fs::write(&lib_path, new_text)?;
    Ok(())
}

fn fixture_name(cert_path: &Path) -> String {
    cert_path
        .file_name()
        .and_then(|n| n.to_str())
        .map(|s| s.trim_end_matches(".cert.json").to_string())
        .unwrap_or_else(|| cert_path.display().to_string())
}

const HEADER: &str = "// AUTO-GENERATED by `meta-harness --regen-models`. DO NOT EDIT.
// Each fn below was emitted by `aeneas-check --rust-model` for the
// named fixture, filtered through `meta-harness` for scalar-shape sig
// and body, prefixed with the fixture name, and verified via `cargo
// check`. Fns whose bodies failed compilation were dropped.
//
// Re-generate with:
//   meta-harness --regen-models <out-path> --sweep <cert-dir>
//
// This file is `include!()`-d inside `pub mod model { ... }` in
// `src/lib.rs`, so inner attributes are not allowed here. Lints are
// silenced via the outer `pub mod model`'s attrs (in lib.rs).

";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn split_pub_fns_works() {
        let txt = "pub fn a_model(x: u32) -> u32 {\n    (x + 1u32)\n}\n\npub fn b_model() -> u32 {\n    0u32\n}\n";
        let blocks = split_pub_fns(txt);
        assert_eq!(blocks.len(), 2);
        assert!(blocks[0].starts_with("pub fn a_model"));
        assert!(blocks[1].starts_with("pub fn b_model"));
    }

    #[test]
    fn block_short_name_strips_model() {
        let blk = "pub fn foo_model(x: u32) -> u32 { x }";
        assert_eq!(block_short_name(blk).as_deref(), Some("foo"));
    }

    #[test]
    fn body_rejects_at_prefix() {
        let registry = StructRegistry::new();
        let ok = body_acceptable(
            "let x_post = @ArrayIndexShared(x, 0usize); x_post",
            &registry,
            "arrays",
            &[],
            &Shape::Scalar(crate::generate::Scalar::U32),
        );
        assert!(!ok);
    }

    #[test]
    fn body_accepts_pure_scalar() {
        let registry = StructRegistry::new();
        let ok = body_acceptable(
            "u32::wrapping_add(x, 1u32)",
            &registry,
            "incr",
            &[Shape::Scalar(crate::generate::Scalar::U32)],
            &Shape::Scalar(crate::generate::Scalar::U32),
        );
        assert!(ok);
    }
}
