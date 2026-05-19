//! Auto-generate `proptest!` blocks for cert decls whose signatures
//! are simple enough that we can synthesise inputs (all scalar in,
//! scalar / tuple-of-scalars out).
//!
//! Input:  a directory of `.cert.json` files (typically tests/llbc/).
//! Output: a Rust file with one `proptest!` block per candidate decl,
//!         plus a summary count of emitted / skipped (with reasons).
//!
//! The generated proptests assume:
//!   * `tests/src/<fixture>.rs` exists and compiles as a Rust module
//!     (the original fixture source — same one charon reads).
//!   * `tests/lean-checker/differential/src/model.rs` already
//!     contains `<fixture>_<fn>_model` (regen via
//!     `scripts/regen-diff-models.sh` if not).
//!
//! Candidates whose model fn is missing from `model.rs` are still
//! emitted but inside a `#[cfg(all(test, feature = "all_models"))]`
//! gate, so the build doesn't break until the model is regenerated.

use anyhow::{Context, Result};
use serde::Deserialize;
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

/// Subset of cert.json sufficient for signature extraction.
#[derive(Deserialize)]
struct RawCertSig {
    llbc_program: RawProgram,
}
#[derive(Deserialize)]
struct RawProgram {
    #[serde(default)]
    fun_decls: Option<Vec<RawFnDecl>>,
}
#[derive(Deserialize)]
struct RawFnDecl {
    item_meta: RawItemMeta,
    signature: serde_json::Value,
    #[serde(default)]
    body: serde_json::Value,
    #[serde(default)]
    is_global_initializer: serde_json::Value,
}
#[derive(Deserialize)]
struct RawItemMeta {
    name: String,
    #[serde(default)]
    attr_info: Option<serde_json::Value>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scalar {
    U8, U16, U32, U64, USize,
    I8, I16, I32, I64, ISize,
    Bool,
}

impl Scalar {
    fn rust(self) -> &'static str {
        match self {
            Scalar::U8 => "u8", Scalar::U16 => "u16", Scalar::U32 => "u32",
            Scalar::U64 => "u64", Scalar::USize => "usize",
            Scalar::I8 => "i8", Scalar::I16 => "i16", Scalar::I32 => "i32",
            Scalar::I64 => "i64", Scalar::ISize => "isize",
            Scalar::Bool => "bool",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RetTy {
    Unit,
    Scalar(Scalar),
    Tuple(Vec<Scalar>),
}

#[derive(Debug, Clone)]
pub struct Candidate {
    pub fixture: String,
    pub fn_name: String,
    pub charon_path: String,
    pub args: Vec<Scalar>,
    pub ret: RetTy,
    pub is_public: bool,
}

#[derive(Debug, Default)]
pub struct Summary {
    pub emitted: usize,
    pub skipped_signature: usize,
    pub skipped_non_public: usize,
    pub skipped_no_body: usize,
    pub skipped_missing_model: usize,
    pub skipped_missing_source: usize,
    pub skip_reasons: BTreeMap<String, Vec<String>>, // reason → [paths]
}

pub fn generate_for_cert_dir(
    cert_dir: &Path,
    src_dir: &Path,
    model_path: &Path,
    out: &Path,
) -> Result<Summary> {
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

    let model_fns = parse_model_fns(model_path)?;

    let mut candidates: Vec<Candidate> = Vec::new();
    let mut summary = Summary::default();

    for cert_path in &certs {
        let fixture = fixture_name(cert_path);
        let text = fs::read_to_string(cert_path)
            .with_context(|| format!("reading {}", cert_path.display()))?;
        let raw: RawCertSig = match serde_json::from_str(&text) {
            Ok(r) => r,
            Err(e) => {
                summary
                    .skip_reasons
                    .entry(format!("cert parse error: {e}"))
                    .or_default()
                    .push(fixture.clone());
                continue;
            }
        };

        let Some(fns) = raw.llbc_program.fun_decls else { continue };

        for fd in fns {
            let path = fd.item_meta.name.clone();
            // Only fns whose path starts with `<fixture>::` (drop
            // monomorphised stdlib siblings).
            let prefix = format!("{fixture}::");
            if !path.starts_with(&prefix) {
                continue;
            }
            let short = path[prefix.len()..].to_string();
            // Drop impl methods / trait-impl methods (`Type::method`
            // shape). MVP only handles bare free fns.
            if short.contains("::") || short.contains('{') {
                summary
                    .skip_reasons
                    .entry("non-free-fn (impl method or trait impl)".into())
                    .or_default()
                    .push(path.clone());
                continue;
            }

            let is_public = is_public(&fd.item_meta.attr_info);
            if !is_public {
                summary.skipped_non_public += 1;
                continue;
            }
            // Drop fns with no body (extern / unimplemented).
            if matches!(&fd.body, serde_json::Value::Null) {
                summary.skipped_no_body += 1;
                continue;
            }
            // Drop global initialisers — these are constants, not fns;
            // calling them as `<name>()` is a syntax error.
            if fd.is_global_initializer.as_bool() == Some(true) {
                summary
                    .skip_reasons
                    .entry("global initialiser (const, not fn)".into())
                    .or_default()
                    .push(path.clone());
                continue;
            }

            let Some((args, ret)) = parse_simple_sig(&fd.signature) else {
                summary.skipped_signature += 1;
                summary
                    .skip_reasons
                    .entry("non-simple signature".into())
                    .or_default()
                    .push(path.clone());
                continue;
            };

            candidates.push(Candidate {
                fixture: fixture.clone(),
                fn_name: short,
                charon_path: path,
                args,
                ret,
                is_public,
            });
        }
    }

    // Emit. Group by fixture for module declarations.
    let mut by_fixture: BTreeMap<String, Vec<Candidate>> = BTreeMap::new();
    for c in &candidates {
        by_fixture.entry(c.fixture.clone()).or_default().push(c.clone());
    }

    let mut output = String::new();
    output.push_str(HEADER);
    // Pre-scan sources: skip whole fixtures whose source uses
    // tooling we can't safely `#[path]`-include into a generic test
    // crate (custom test attributes registered via
    // `#![register_tool(verify)]`, unstable `#![feature(...)]`, etc.).
    let mut usable_fixtures: BTreeMap<String, PathBuf> = BTreeMap::new();
    for fixture in by_fixture.keys() {
        let src_file = src_dir.join(format!("{fixture}.rs"));
        if !src_file.is_file() {
            for c in &by_fixture[fixture] {
                summary.skipped_missing_source += 1;
                summary
                    .skip_reasons
                    .entry(format!("source missing: {}", src_file.display()))
                    .or_default()
                    .push(c.charon_path.clone());
            }
            continue;
        }
        let src_text = fs::read_to_string(&src_file).unwrap_or_default();
        if src_text.contains("register_tool(verify)")
            || src_text.contains("#[verify::test]")
            || src_text.contains("verify::")
            || src_text.contains("#![feature(")
        {
            for c in &by_fixture[fixture] {
                summary.skipped_missing_source += 1;
                summary
                    .skip_reasons
                    .entry("source uses crate-level attrs (`#![feature]` / `register_tool(verify)`) — can't be `#[path]`-included".into())
                    .or_default()
                    .push(c.charon_path.clone());
            }
            continue;
        }
        usable_fixtures.insert(fixture.clone(), src_file);
    }

    // Source modules (#[path] imports), only for fixtures that survive.
    for (fixture, src_file) in &usable_fixtures {
        let rel = pathdiff_or_default(src_file, out);
        output.push_str(&format!(
            "#[path = {:?}]\n#[allow(unused_variables, dead_code, non_snake_case, unused_parens, unused_mut)]\nmod {fixture}_src;\n",
            rel
        ));
    }
    output.push_str("\nuse aeneas_cert_differential::model;\nuse proptest::prelude::*;\n\n");

    // proptest! blocks per fixture.
    for (fixture, cs) in &by_fixture {
        if !usable_fixtures.contains_key(fixture) {
            continue; // already counted as skipped
        }
        let mut block = String::new();
        block.push_str(&format!(
            "// ====================================================================\n// {} — auto-generated\n// ====================================================================\n",
            fixture
        ));
        for c in cs {
            let model_key = format!("{fixture}_{}_model", c.fn_name);
            let has_model = model_fns.contains(&model_key);
            if !has_model {
                summary.skipped_missing_model += 1;
                summary
                    .skip_reasons
                    .entry(format!("model::{model_key} not in src/model.rs"))
                    .or_default()
                    .push(c.charon_path.clone());
                block.push_str(&format!(
                    "\n// SKIPPED {}: `model::{}` not in src/model.rs (run scripts/regen-diff-models.sh)\n",
                    c.charon_path, model_key,
                ));
                continue;
            }
            block.push_str(&emit_proptest_block(fixture, c));
            summary.emitted += 1;
        }
        output.push_str(&block);
        output.push('\n');
    }

    fs::write(out, output)
        .with_context(|| format!("writing {}", out.display()))?;
    Ok(summary)
}

fn emit_proptest_block(fixture: &str, c: &Candidate) -> String {
    let test_name = format!("{}_{}_auto", fixture, c.fn_name);
    let arg_names: Vec<String> = (0..c.args.len()).map(|i| format!("a{}", i)).collect();
    let call_args = arg_names.join(", ");
    let ret_str = match &c.ret {
        RetTy::Unit => "()".to_string(),
        RetTy::Scalar(s) => s.rust().to_string(),
        RetTy::Tuple(ts) => format!("({})", ts.iter().map(|t| t.rust()).collect::<Vec<_>>().join(", ")),
    };
    let args_str = c.args.iter().map(|a| a.rust()).collect::<Vec<_>>().join(", ");
    // Zero-arg fns can't go through `proptest!` (which requires at
    // least one input strategy). Emit a regular `#[test]` instead —
    // both fns are deterministic so a single comparison is enough.
    if c.args.is_empty() {
        return format!(
            "\n/// Auto-generated from `{}` (signature: () -> {ret_str})\n#[test]\nfn {}() {{\n    let lhs = {}_src::{}();\n    let rhs = model::{}_{}_model();\n    assert_eq!(lhs, rhs);\n}}\n",
            c.charon_path, test_name, fixture, c.fn_name, fixture, c.fn_name,
        );
    }
    let arg_clauses: Vec<String> = c
        .args
        .iter()
        .zip(&arg_names)
        .map(|(ty, n)| format!("{} in any::<{}>()", n, ty.rust()))
        .collect();
    let mut s = String::new();
    s.push_str(&format!(
        "\nproptest! {{\n    /// Auto-generated from `{}` (signature: ({args_str}) -> {ret_str})\n    #[test]\n    fn {}({}) {{\n",
        c.charon_path,
        test_name,
        arg_clauses.join(", "),
    ));
    s.push_str(&format!(
        "        let lhs = {}_src::{}({});\n",
        fixture, c.fn_name, call_args
    ));
    s.push_str(&format!(
        "        let rhs = model::{}_{}_model({});\n",
        fixture, c.fn_name, call_args
    ));
    s.push_str("        prop_assert_eq!(lhs, rhs);\n    }\n}\n");
    s
}

fn parse_simple_sig(sig: &serde_json::Value) -> Option<(Vec<Scalar>, RetTy)> {
    let inputs = sig.get("inputs")?.as_array()?;
    let mut args = Vec::new();
    for inp in inputs {
        let s = scalar_of(inp)?;
        args.push(s);
    }
    let output = sig.get("output")?;
    let ret = ret_of(output)?;
    // Reject generics — easier to skip than support
    if let Some(g) = sig.get("generics") {
        let types = g.get("types").and_then(|v| v.as_array()).map(|a| !a.is_empty()).unwrap_or(false);
        let cgs = g.get("const_generics").and_then(|v| v.as_array()).map(|a| !a.is_empty()).unwrap_or(false);
        let clauses = g.get("trait_clauses").and_then(|v| v.as_array()).map(|a| !a.is_empty()).unwrap_or(false);
        if types || cgs || clauses {
            return None;
        }
    }
    Some((args, ret))
}

fn scalar_of(v: &serde_json::Value) -> Option<Scalar> {
    let lit = v.get("Literal")?;
    if let Some(u) = lit.get("UInt").and_then(|v| v.as_str()) {
        return Some(match u {
            "U8" => Scalar::U8, "U16" => Scalar::U16, "U32" => Scalar::U32,
            "U64" => Scalar::U64, "Usize" | "USize" => Scalar::USize,
            _ => return None,
        });
    }
    if let Some(i) = lit.get("Int").and_then(|v| v.as_str()) {
        return Some(match i {
            "I8" => Scalar::I8, "I16" => Scalar::I16, "I32" => Scalar::I32,
            "I64" => Scalar::I64, "Isize" | "ISize" => Scalar::ISize,
            _ => return None,
        });
    }
    if lit.is_string() && lit.as_str() == Some("Bool") {
        return Some(Scalar::Bool);
    }
    if lit.get("Bool").is_some() {
        return Some(Scalar::Bool);
    }
    None
}

fn ret_of(v: &serde_json::Value) -> Option<RetTy> {
    // Tuple? `{"Adt":{"id":"Tuple","generics":{"types":[...]}}}`
    if let Some(adt) = v.get("Adt") {
        if adt.get("id").and_then(|i| i.as_str()) == Some("Tuple") {
            let tys = adt.get("generics")?.get("types")?.as_array()?;
            if tys.is_empty() {
                return Some(RetTy::Unit);
            }
            let mut scalars = Vec::new();
            for t in tys {
                scalars.push(scalar_of(t)?);
            }
            return Some(RetTy::Tuple(scalars));
        }
        return None;
    }
    scalar_of(v).map(RetTy::Scalar)
}

fn is_public(attr_info: &Option<serde_json::Value>) -> bool {
    attr_info
        .as_ref()
        .and_then(|v| v.get("public"))
        .and_then(|v| v.as_bool())
        .unwrap_or(false)
}

fn fixture_name(cert_path: &Path) -> String {
    cert_path
        .file_name()
        .and_then(|n| n.to_str())
        .map(|s| s.trim_end_matches(".cert.json").to_string())
        .unwrap_or_else(|| cert_path.display().to_string())
}

/// Parse `pub fn <name>_model(` lines out of `src/model.rs` to build
/// a set of names that already exist. Cheap; doesn't need real Rust
/// parsing.
fn parse_model_fns(model_path: &Path) -> Result<std::collections::HashSet<String>> {
    let mut out = std::collections::HashSet::new();
    if !model_path.is_file() {
        return Ok(out);
    }
    let text = fs::read_to_string(model_path)
        .with_context(|| format!("reading {}", model_path.display()))?;
    for line in text.lines() {
        let line = line.trim_start();
        if let Some(rest) = line.strip_prefix("pub fn ") {
            if let Some(end) = rest.find(|c: char| c == '(' || c == '<' || c.is_whitespace()) {
                out.insert(rest[..end].to_string());
            }
        }
    }
    Ok(out)
}

/// Best-effort relative path. Falls back to absolute if computation fails.
fn pathdiff_or_default(target: &Path, from_file: &Path) -> String {
    let from_dir = from_file.parent().unwrap_or_else(|| Path::new("."));
    let target_abs = target.canonicalize().unwrap_or_else(|_| target.to_path_buf());
    let from_abs = from_dir.canonicalize().unwrap_or_else(|_| from_dir.to_path_buf());
    if let Some(rel) = relative_from(&target_abs, &from_abs) {
        rel
    } else {
        target_abs.display().to_string()
    }
}

fn relative_from(target: &Path, from: &Path) -> Option<String> {
    let t: Vec<_> = target.components().collect();
    let f: Vec<_> = from.components().collect();
    let common = t.iter().zip(&f).take_while(|(a, b)| a == b).count();
    let ups = f.len() - common;
    let mut out = PathBuf::new();
    for _ in 0..ups {
        out.push("..");
    }
    for comp in &t[common..] {
        out.push(comp);
    }
    Some(out.display().to_string())
}

const HEADER: &str = "// AUTO-GENERATED by `meta-harness --generate-tests`. DO NOT EDIT.
// Each `proptest!` block was synthesised from a cert.json fn whose
// signature is simple enough to drive `any::<...>()` directly
// (all-scalar inputs + scalar / tuple-of-scalars output, no
// generics, no refs).
//
// To regenerate:
//   meta-harness --generate-tests \\
//     --sweep tests/llbc \\
//     --tests-src-dir tests/src \\
//     --tests-out tests/lean-checker/differential/tests/diff_auto.rs

#![allow(unused_variables, dead_code, non_snake_case, unused_parens, unused_mut)]

";
