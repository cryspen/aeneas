//! Auto-generate `proptest!` blocks for cert decls whose signatures
//! are simple enough that we can synthesise inputs (all scalar in,
//! scalar / tuple-of-scalars out, fixed-size scalar arrays, and
//! simple all-scalar named-field structs defined in the same fixture).
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
    #[serde(default)]
    type_decls: Option<Vec<RawTypeDecl>>,
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
struct RawTypeDecl {
    id: u64,
    item_meta: RawItemMeta,
    kind: serde_json::Value,
    #[serde(default)]
    generics: serde_json::Value,
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

/// A "shape" we can drive with proptest strategies, both for inputs and
/// for return types. Scalars, fixed-size scalar arrays, simple
/// all-scalar named-field structs, and unit / tuples-of-shapes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Shape {
    Scalar(Scalar),
    Array(Scalar, usize),
    /// Named struct with all-scalar fields. `fixture` is the fixture
    /// where the struct is defined; `name` is the bare struct name;
    /// `fields` is the ordered list of (field_name, field_scalar)
    /// pairs. `field_name` is `None` for tuple structs (positional).
    Struct {
        fixture: String,
        name: String,
        fields: Vec<(Option<String>, Scalar)>,
    },
    Unit,
    Tuple(Vec<Shape>),
}

impl Shape {
    /// Rust type expression for use in `fn` signatures and casts.
    fn rust_ty(&self) -> String {
        match self {
            Shape::Scalar(s) => s.rust().to_string(),
            Shape::Array(s, n) => format!("[{}; {}]", s.rust(), n),
            Shape::Struct { fixture, name, .. } => {
                format!("{fixture}_src::{name}")
            }
            Shape::Unit => "()".to_string(),
            Shape::Tuple(ts) => format!(
                "({})",
                ts.iter().map(|t| t.rust_ty()).collect::<Vec<_>>().join(", ")
            ),
        }
    }

    /// Proptest strategy expression for this shape.
    fn strategy(&self) -> String {
        match self {
            Shape::Scalar(s) => format!("any::<{}>()", s.rust()),
            Shape::Array(s, n) => {
                // proptest::array::uniform<N>(any::<S>()) for small N.
                // Only sizes 1..=32 have a `uniform<N>` helper. For
                // larger sizes we fall back to a runtime-checked init.
                if *n == 0 {
                    format!("Just([] as [{}; 0])", s.rust())
                } else if *n <= 32 {
                    format!(
                        "proptest::array::uniform{}(any::<{}>())",
                        n, s.rust()
                    )
                } else {
                    // Use prop::collection::vec + try_into for big arrays.
                    format!(
                        "prop::collection::vec(any::<{ty}>(), {n}..={n}).prop_map(|v| {{ let a: [{ty}; {n}] = v.try_into().unwrap(); a }})",
                        ty = s.rust(),
                        n = n
                    )
                }
            }
            Shape::Struct { fixture, name, fields } => {
                // Build `(any::<T1>(), any::<T2>(), ...).prop_map(|(f1,f2,...)| Foo { f1, f2, ... })`
                if fields.is_empty() {
                    return format!("Just({fixture}_src::{name} {{}})");
                }
                let strats: Vec<String> = fields
                    .iter()
                    .map(|(_, s)| format!("any::<{}>()", s.rust()))
                    .collect();
                let bind: Vec<String> = (0..fields.len())
                    .map(|i| format!("f{i}"))
                    .collect();
                let assigns: Vec<String> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, (fname, _))| match fname {
                        Some(fn_) => format!("{fn_}: f{i}"),
                        None => format!("f{i}"),
                    })
                    .collect();
                // If all field names are None, emit tuple-struct ctor.
                let is_tuple_struct = fields.iter().all(|(n, _)| n.is_none());
                let ctor = if is_tuple_struct {
                    format!(
                        "{fixture}_src::{name}({})",
                        bind.join(", ")
                    )
                } else {
                    format!(
                        "{fixture}_src::{name} {{ {} }}",
                        assigns.join(", ")
                    )
                };
                let strats_str = strats.join(", ");
                if fields.len() == 1 {
                    // Single-field: `any::<T>().prop_map(|f0| Foo { x: f0 })`
                    format!(
                        "{strats_str}.prop_map(|{}| {ctor})",
                        bind[0]
                    )
                } else {
                    format!(
                        "({strats_str}).prop_map(|({})| {ctor})",
                        bind.join(", ")
                    )
                }
            }
            Shape::Unit => "Just(())".to_string(),
            Shape::Tuple(ts) => {
                let strats: Vec<String> =
                    ts.iter().map(|t| t.strategy()).collect();
                format!("({})", strats.join(", "))
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Candidate {
    pub fixture: String,
    pub fn_name: String,
    pub charon_path: String,
    pub args: Vec<Shape>,
    pub ret: Shape,
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

/// Per-fixture struct registry: ADT id → struct shape (for sigs that
/// reference structs via `Adt { id: Adt N }`).
pub type StructRegistry = BTreeMap<u64, Shape>;

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

        let registry = build_struct_registry_raw(&fixture, &raw.llbc_program);

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

            let Some((args, ret)) = parse_simple_sig(&fd.signature, &registry) else {
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
    let call_args_lhs = arg_names.join(", ");
    let call_args_rhs = arg_names
        .iter()
        .enumerate()
        .map(|(i, n)| {
            // Clone non-Copy args (structs / arrays) so both calls
            // can consume them. Scalars are Copy already; arrays of
            // Copy scalars are Copy; structs may or may not be Copy
            // but `.clone()` is always safe for our shapes (we only
            // accept all-scalar fields).
            match &c.args[i] {
                Shape::Scalar(_) => n.clone(),
                _ => format!("{n}.clone()"),
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    let ret_str = c.ret.rust_ty();
    let args_str = c.args.iter().map(|a| a.rust_ty()).collect::<Vec<_>>().join(", ");
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
        .map(|(ty, n)| format!("{} in {}", n, ty.strategy()))
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
        fixture, c.fn_name, call_args_lhs
    ));
    s.push_str(&format!(
        "        let rhs = model::{}_{}_model({});\n",
        fixture, c.fn_name, call_args_rhs
    ));
    s.push_str("        prop_assert_eq!(lhs, rhs);\n    }\n}\n");
    s
}

/// Build a per-fixture map of ADT-id → simple struct Shape. Only
/// includes structs whose fields are all scalars (no generics, no
/// nested ADTs, no arrays).
pub fn build_struct_registry(fixture: &str, prog_value: &serde_json::Value) -> StructRegistry {
    let mut out = StructRegistry::new();
    let Some(tds) = prog_value.get("type_decls").and_then(|v| v.as_array()) else {
        return out;
    };
    for td in tds {
        let Some(id) = td.get("id").and_then(|v| v.as_u64()) else { continue };
        let Some(name) = td
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
        // Reject nested types — `mod::Foo`-shape.
        if short.contains("::") || short.contains('{') {
            continue;
        }
        // Reject generic structs — proptest can't synthesise <T>.
        let gens = td.get("generics").cloned().unwrap_or(serde_json::Value::Null);
        if !generics_empty(&gens) {
            continue;
        }
        let kind = td.get("kind").cloned().unwrap_or(serde_json::Value::Null);
        let Some(struct_kind) = kind.get("Struct") else { continue };
        let Some(fields) = struct_kind.as_array() else { continue };
        let mut field_shapes: Vec<(Option<String>, Scalar)> = Vec::new();
        let mut ok = true;
        for f in fields {
            let fname = f.get("name").and_then(|v| v.as_str()).map(String::from);
            let ty = f.get("ty");
            let Some(ty) = ty else { ok = false; break };
            let Some(s) = scalar_of(ty) else { ok = false; break };
            field_shapes.push((fname, s));
        }
        if !ok {
            continue;
        }
        out.insert(
            id,
            Shape::Struct {
                fixture: fixture.to_string(),
                name: short.to_string(),
                fields: field_shapes,
            },
        );
    }
    out
}

/// `RawProgram` wrapper that drops directly into `build_struct_registry`.
fn build_struct_registry_raw(fixture: &str, prog: &RawProgram) -> StructRegistry {
    let tds = match &prog.type_decls {
        Some(t) => t,
        None => return StructRegistry::new(),
    };
    // Re-encode through serde_json::Value for uniform handling.
    let v = serde_json::json!({
        "type_decls": tds.iter().map(|td| serde_json::json!({
            "id": td.id,
            "item_meta": {"name": td.item_meta.name},
            "kind": td.kind,
            "generics": td.generics,
        })).collect::<Vec<_>>()
    });
    build_struct_registry(fixture, &v)
}

fn generics_empty(g: &serde_json::Value) -> bool {
    let types = g
        .get("types")
        .and_then(|v| v.as_array())
        .map(|a| a.is_empty())
        .unwrap_or(true);
    let cgs = g
        .get("const_generics")
        .and_then(|v| v.as_array())
        .map(|a| a.is_empty())
        .unwrap_or(true);
    let clauses = g
        .get("trait_clauses")
        .and_then(|v| v.as_array())
        .map(|a| a.is_empty())
        .unwrap_or(true);
    types && cgs && clauses
}

pub fn parse_simple_sig(
    sig: &serde_json::Value,
    registry: &StructRegistry,
) -> Option<(Vec<Shape>, Shape)> {
    let inputs = sig.get("inputs")?.as_array()?;
    let mut args = Vec::new();
    for inp in inputs {
        let s = shape_of(inp, registry)?;
        args.push(s);
    }
    let output = sig.get("output")?;
    let ret = shape_of(output, registry)?;
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

/// Recognise a type as a Shape we can drive with proptest. Returns
/// `None` for refs, slices, generics, opaque, etc.
pub fn shape_of(v: &serde_json::Value, registry: &StructRegistry) -> Option<Shape> {
    // Scalars (Literal).
    if let Some(s) = scalar_of(v) {
        return Some(Shape::Scalar(s));
    }
    // Fixed-size scalar array: {"Array": [<elem>, {"kind": {"Literal":{"Scalar":{"Unsigned":["Usize","<N>"]}}}}]}
    if let Some(arr) = v.get("Array") {
        let arr = arr.as_array()?;
        if arr.len() == 2 {
            let elem = scalar_of(&arr[0])?;
            let n = array_size(&arr[1])?;
            return Some(Shape::Array(elem, n));
        }
        return None;
    }
    // Adt: tuple or simple struct.
    if let Some(adt) = v.get("Adt") {
        let id = adt.get("id")?;
        if id.as_str() == Some("Tuple") {
            let tys = adt.get("generics")?.get("types")?.as_array()?;
            if tys.is_empty() {
                return Some(Shape::Unit);
            }
            let mut shapes = Vec::new();
            for t in tys {
                // Tuple components are scalars only (keeps Display
                // simple). Could be extended later.
                shapes.push(Shape::Scalar(scalar_of(t)?));
            }
            return Some(Shape::Tuple(shapes));
        }
        // Simple named struct: id = {"Adt": N}, no generics applied.
        let gens = adt.get("generics").cloned().unwrap_or(serde_json::Value::Null);
        if !generics_empty(&gens) {
            return None;
        }
        if let Some(n) = id.get("Adt").and_then(|v| v.as_u64()) {
            return registry.get(&n).cloned();
        }
        return None;
    }
    None
}

/// Parse the `N` out of `{"kind": {"Literal": {"Scalar": {"Unsigned":
/// ["Usize", "<N>"]}}}}` (the const-generic literal used in fixed-size
/// arrays).
fn array_size(v: &serde_json::Value) -> Option<usize> {
    let lit = v
        .get("kind")
        .and_then(|k| k.get("Literal"))
        .and_then(|l| l.get("Scalar"))?;
    // {"Unsigned": ["Usize", "<N>"]}  or  {"Signed": [...]}
    for sign_key in ["Unsigned", "Signed"] {
        if let Some(arr) = lit.get(sign_key).and_then(|a| a.as_array()) {
            if let Some(s) = arr.get(1).and_then(|s| s.as_str()) {
                if let Ok(n) = s.parse::<usize>() {
                    return Some(n);
                }
            }
        }
    }
    None
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
pub fn parse_model_fns(model_path: &Path) -> Result<std::collections::HashSet<String>> {
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
// (all-scalar / fixed-size-scalar-array / simple-struct inputs +
// scalar / tuple-of-scalars / array / simple-struct output, no
// generics, no refs).
//
// To regenerate:
//   meta-harness --generate-tests \\
//     --sweep tests/llbc \\
//     --tests-src-dir tests/src \\
//     --tests-out tests/lean-checker/differential/tests/diff_auto.rs

#![allow(unused_variables, dead_code, non_snake_case, unused_parens, unused_mut)]

";

// Quiet unused-warning on the raw helper; some integration paths use
// the JSON variant instead.
#[allow(dead_code)]
fn _unused_keepalive(_p: &RawProgram) {
    let _: StructRegistry = build_struct_registry_raw("x", _p);
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn scalar_array_shape() {
        let registry = StructRegistry::new();
        let ty = json!({"Array": [
            {"Literal": {"UInt": "U32"}},
            {"kind": {"Literal": {"Scalar": {"Unsigned": ["Usize", "4"]}}}}
        ]});
        assert_eq!(
            shape_of(&ty, &registry),
            Some(Shape::Array(Scalar::U32, 4))
        );
    }

    #[test]
    fn struct_shape_via_registry() {
        let mut registry = StructRegistry::new();
        registry.insert(
            0,
            Shape::Struct {
                fixture: "aggregates_basic".into(),
                name: "Pair".into(),
                fields: vec![
                    (Some("x".into()), Scalar::U32),
                    (Some("y".into()), Scalar::U32),
                ],
            },
        );
        let ty = json!({"Adt": {"id": {"Adt": 0}, "generics": {"types": []}}});
        let got = shape_of(&ty, &registry).unwrap();
        match got {
            Shape::Struct { name, .. } => assert_eq!(name, "Pair"),
            _ => panic!("expected Struct"),
        }
    }

    #[test]
    fn array_strategy_uses_uniform() {
        let s = Shape::Array(Scalar::U32, 4);
        assert_eq!(s.strategy(), "proptest::array::uniform4(any::<u32>())");
    }

    #[test]
    fn struct_strategy_uses_prop_map() {
        let s = Shape::Struct {
            fixture: "agg".into(),
            name: "P".into(),
            fields: vec![
                (Some("x".into()), Scalar::U32),
                (Some("y".into()), Scalar::U32),
            ],
        };
        let strat = s.strategy();
        assert!(strat.contains("prop_map"));
        assert!(strat.contains("agg_src::P"));
    }
}
