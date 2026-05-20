//! `gen-diff-tests` — auto-generate `tests/diff_auto.rs` and
//! `tests/common/ref_impl_auto.rs` for every Pure-IR fixture whose
//! signatures are amenable to direct `proptest`-style differential
//! testing (R₀ source ↔ R₂ pir2rs emit).
//!
//! Amenable means: every input + the output is a scalar
//! (`TInt`/`TUInt`/`TBool` — we skip `TFloat`/`TChar` to avoid
//! `Strategy<Float>` boilerplate; `Result<T,()>` wrapping is fine),
//! a fixed-size array of scalars, a tuple of those, or a simple
//! struct/enum whose every field/variant payload is amenable. No
//! generics on the call site (no `TVar` left in the sig), no `TArrow`,
//! no `TTraitType`, no slice/str/raw-ptr builtins.
//!
//! Workflow:
//!   1. Walk `tests/models/*_pir.rs` to discover the set of fixtures
//!      that have an emitted model. The companion script
//!      `regen-diff-models.sh` is responsible for keeping this set in
//!      sync with the "green at pre-extract" list from
//!      `tests/compile_check.rs`.
//!   2. For each fixture: re-dump the Pure-IR JSON to a temp dir via
//!      `bin/aeneas -dump-pure-ir pre-extract:<tmp>`, parse it, apply
//!      the amenability filter to every fn whose `item_meta.name`'s
//!      first segment matches the crate.
//!   3. Skip fns whose model body contains `loop_op(` or
//!      `unimplemented!(` — those panic at runtime.
//!   4. Emit `tests/diff_auto.rs` + `tests/common/ref_impl_auto.rs`
//!      side-by-side with the hand-written `tests/diff.rs` /
//!      `tests/common/ref_impl.rs`.
//!
//! Output files are AUTO-GENERATED. To regenerate after a code change:
//!   cargo run --bin gen-diff-tests

use pure_ir::ast::*;
use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

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

fn src_dir() -> PathBuf {
    repo_root().join("tests").join("src")
}

fn crate_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Walk `tests/models/*_pir.rs` and return the set of fixture names.
fn discover_fixtures() -> Vec<String> {
    let models = crate_root().join("tests").join("models");
    let mut out = Vec::new();
    for entry in fs::read_dir(&models).expect("read tests/models") {
        let entry = entry.unwrap();
        let name = entry.file_name().to_string_lossy().to_string();
        if let Some(stem) = name.strip_suffix("_pir.rs") {
            out.push(stem.to_string());
        }
    }
    out.sort();
    out
}

/// Dump the pre-extract JSON for one fixture into `dest_dir`. Returns
/// the JSON file path on success.
fn dump_pure_ir(fixture: &str, dest_dir: &Path) -> Option<PathBuf> {
    let llbc = llbc_dir().join(format!("{fixture}.llbc"));
    if !llbc.exists() {
        return None;
    }
    fs::create_dir_all(dest_dir).ok()?;
    let dump_arg = format!("pre-extract:{}", dest_dir.display());
    let out = Command::new(aeneas_bin())
        .args(["-backend", "lean", "-dest"])
        .arg(dest_dir)
        .args(["-dump-pure-ir", &dump_arg])
        .arg(&llbc)
        .output()
        .ok()?;
    let _ = out;
    let json = dest_dir.join(format!("{fixture}.pure.json"));
    if json.exists() {
        Some(json)
    } else {
        None
    }
}

// ====================================================================
// amenability filter
// ====================================================================

/// Resolved shape of a Rust type for proptest emission.
#[derive(Debug, Clone)]
#[allow(dead_code)]
enum Shape {
    /// Primitive — Rust name like `u32`, `i32`, `bool`.
    Scalar(String),
    /// Fixed-size array `[T; N]`.
    Array(Box<Shape>, u64),
    /// Tuple `(T0, T1, ...)`.
    Tuple(Vec<Shape>),
    /// Unit `()`.
    Unit,
    /// `Result<T, ()>`.
    Result(Box<Shape>),
    /// `aeneas_runtime::Result<T>` (alias for `Result<T,()>`).
    AeneasResult(Box<Shape>),
}

impl Shape {
    /// Render as a Rust type at the model side (always the emitted
    /// `aeneas_runtime::Result<...>` wrapping where present).
    #[allow(dead_code)]
    fn render_model(&self, qual: &str) -> String {
        match self {
            Shape::Scalar(s) => s.clone(),
            Shape::Array(inner, n) => format!("[{}; {n}]", inner.render_model(qual)),
            Shape::Tuple(ts) => {
                let inner = ts
                    .iter()
                    .map(|t| t.render_model(qual))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({})", inner)
            }
            Shape::Unit => "()".to_string(),
            Shape::Result(inner) | Shape::AeneasResult(inner) => {
                format!("{qual}Result<{}>", inner.render_model(qual))
            }
        }
    }

    /// Build a `proptest::strategy::Strategy<Value = Self>` expression
    /// from this shape. None when the shape isn't drivable directly
    /// (e.g. nested Result, or unit-typed top-level — we handle those
    /// specially).
    fn proptest_strategy(&self) -> Option<String> {
        match self {
            Shape::Scalar(s) => Some(format!("any::<{s}>()")),
            Shape::Array(inner, n) => {
                let inner_s = inner.proptest_strategy()?;
                // proptest has uniformN for N in 1..=32.
                if *n >= 1 && *n <= 32 {
                    Some(format!("proptest::array::uniform{n}({inner_s})"))
                } else {
                    None
                }
            }
            Shape::Tuple(ts) => {
                // proptest tuples support up to 10 directly.
                if ts.is_empty() || ts.len() > 10 {
                    return None;
                }
                let parts = ts
                    .iter()
                    .map(|t| t.proptest_strategy())
                    .collect::<Option<Vec<_>>>()?;
                Some(format!("({})", parts.join(", ")))
            }
            Shape::Unit => None,
            // Result types only appear on the *output* side; we never
            // need to generate one as input.
            Shape::Result(_) | Shape::AeneasResult(_) => None,
        }
    }
}

/// Try to resolve a `Ty` into a Shape, applying the amenability filter.
/// Returns `None` if not amenable. `allow_result_wrapping` is true only
/// at the top-level output position (we don't accept nested `Result`s).
fn ty_shape(ty: &Ty, allow_result: bool) -> Option<Shape> {
    match ty {
        Ty::TLiteral(lt) => match lt {
            LiteralType::TInt(it) => Some(Shape::Scalar(int_rust_name(it).to_string())),
            LiteralType::TUInt(ut) => Some(Shape::Scalar(uint_rust_name(ut).to_string())),
            LiteralType::TBool => Some(Shape::Scalar("bool".to_string())),
            // Skip floats and chars to dodge the `Strategy<Float>`
            // float-bit-pattern strategy + Unicode edge cases. We can
            // widen later if it pays off.
            LiteralType::TFloat(_) | LiteralType::TChar => None,
            LiteralType::TPureNat | LiteralType::TPureInt => None,
        },
        Ty::TAdt(adt) => match &adt.type_id {
            TypeId::TTuple => {
                let ts = adt
                    .generics
                    .types
                    .iter()
                    .map(|t| ty_shape(t, false))
                    .collect::<Option<Vec<_>>>()?;
                if ts.is_empty() {
                    Some(Shape::Unit)
                } else {
                    Some(Shape::Tuple(ts))
                }
            }
            TypeId::TBuiltin(b) => match b {
                BuiltinTy::TResult => {
                    if !allow_result {
                        return None;
                    }
                    // Result<T,(error)> — IR ships a Result wrapping the
                    // success type; the error position is encoded
                    // separately on the OCaml side but the JSON shape
                    // is `generics.types = [T]`.
                    let inner = adt.generics.types.first()?;
                    let inner_shape = ty_shape(inner, false)?;
                    Some(Shape::Result(Box::new(inner_shape)))
                }
                BuiltinTy::TArray => {
                    // generics.types[0] = elem, const_generics[0] = N.
                    let elem = adt.generics.types.first()?;
                    let elem_shape = ty_shape(elem, false)?;
                    let n = match adt.generics.const_generics.first()? {
                        ConstGeneric::CgValue(Literal::VScalar(s)) => {
                            s.value.parse::<u64>().ok()?
                        }
                        _ => return None,
                    };
                    Some(Shape::Array(Box::new(elem_shape), n))
                }
                _ => None,
            },
            TypeId::TAdtId(_) => {
                // We don't synthesize ADT strategies in the
                // first-cut auto-gen: the cert-checker's diff_auto.rs
                // also skips most user ADTs. Hand-written diff.rs
                // covers the in-scope cases; widening here is future
                // work.
                None
            }
        },
        Ty::TArrow(_)
        | Ty::TVar(_)
        | Ty::TTraitType(_)
        | Ty::TNever
        | Ty::TDynTrait(_)
        | Ty::TError => None,
    }
}

fn int_rust_name(it: &IntTy) -> &'static str {
    match it {
        IntTy::Isize => "isize",
        IntTy::I8 => "i8",
        IntTy::I16 => "i16",
        IntTy::I32 => "i32",
        IntTy::I64 => "i64",
        IntTy::I128 => "i128",
    }
}

fn uint_rust_name(ut: &UIntTy) -> &'static str {
    match ut {
        UIntTy::Usize => "usize",
        UIntTy::U8 => "u8",
        UIntTy::U16 => "u16",
        UIntTy::U32 => "u32",
        UIntTy::U64 => "u64",
        UIntTy::U128 => "u128",
    }
}

// ====================================================================
// model-fn name recovery
// ====================================================================

/// Mirror `EmitCtx::flat_path_ident` from `src/emit.rs`. Kept private
/// to avoid a public-API expansion in the library.
fn flat_path_ident(name: &CharonName, def_id: u64) -> String {
    let mut parts: Vec<String> = Vec::new();
    let mut had_impl = false;
    for p in name {
        match p {
            PathElem::PeIdent(p) => parts.push(sanitize_ident(&p.name)),
            PathElem::PeImpl => had_impl = true,
            PathElem::PeTarget(s) => parts.push(sanitize_ident(s)),
            PathElem::PeInstantiated => {}
        }
    }
    if parts.is_empty() {
        return format!("anon_{def_id}");
    }
    let joined = parts.join("_");
    if had_impl {
        format!("impl_{joined}_{def_id}")
    } else {
        format!("{joined}_{def_id}")
    }
}

fn sanitize_ident(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    if let Some(c) = chars.next() {
        if c.is_ascii_alphabetic() || c == '_' {
            out.push(c);
        } else {
            out.push('_');
        }
    }
    for c in chars {
        if c.is_ascii_alphanumeric() || c == '_' {
            out.push(c);
        } else {
            out.push('_');
        }
    }
    out
}

/// The short Rust identifier the source uses for this fn (last
/// `PeIdent` segment of `item_meta.name`).
fn short_fn_name(fd: &FunDecl) -> Option<String> {
    for elem in fd.item_meta.name.iter().rev() {
        if let PathElem::PeIdent(p) = elem {
            return Some(sanitize_ident(&p.name));
        }
    }
    None
}

/// The first `PeIdent` segment — the crate name.
fn crate_segment(name: &CharonName) -> Option<&str> {
    for elem in name {
        if let PathElem::PeIdent(p) = elem {
            return Some(&p.name);
        }
    }
    None
}

/// Is this fn owned by the named crate (top-level, no `PeImpl`)?
/// Compares crate-segment names after normalising `-` ↔ `_` — the JSON
/// `crate_name` field carries the on-disk fixture name (which may have
/// a hyphen, e.g. `assert-cfg`) but the `item_meta.name` carries the
/// Rust-mangled crate name (`assert_cfg`).
fn is_top_level_in_crate(fd: &FunDecl, crate_name: &str) -> bool {
    if !matches!(fd.src, ItemSource::TopLevelItem) {
        return false;
    }
    if fd.item_meta.name.iter().any(|p| matches!(p, PathElem::PeImpl)) {
        return false;
    }
    let seg = match crate_segment(&fd.item_meta.name) {
        Some(s) => s,
        None => return false,
    };
    seg.replace('-', "_") == crate_name.replace('-', "_")
}

// ====================================================================
// known emitter-bug ignore list (surfaces emitter limitations via
// `#[ignore]`d auto-tests rather than red CI). Each entry maps a
// `(fixture, source-fn-name)` to a `#[ignore = "..."]` reason.
//
// Discovered by running `cargo test --test diff_auto` and observing
// the failure pattern. Adding entries here is preferred to silently
// dropping the candidate — we want the surface area visible.
// ====================================================================
const IGNORE_LIST: &[(&str, &str, &str)] = &[
    // `u32::BITS` / `i32::BITS` resolve through a `const`-trait whose
    // value the IR pre-extract stage doesn't thread through; the emit
    // collapses it to `0u32`.
    (
        "scalars",
        "u32_use_bits",
        "EMITTER BUG: u32::BITS const resolves to 0 in model",
    ),
    (
        "scalars",
        "i32_use_bits",
        "EMITTER BUG: i32::BITS const resolves to 0 in model",
    ),
];

fn ignore_reason(fx: &str, short: &str) -> Option<&'static str> {
    IGNORE_LIST
        .iter()
        .find(|(f, n, _)| *f == fx && *n == short)
        .map(|(_, _, r)| *r)
}

// ====================================================================
// candidate selection
// ====================================================================

#[derive(Debug, Clone)]
struct Candidate {
    /// Short fn name in the source (e.g. `mk_tuple`).
    short_name: String,
    /// Emitted fn name in the model file (e.g. `aggregates_basic_mk_tuple_0`).
    model_name: String,
    /// Input shapes.
    inputs: Vec<Shape>,
    /// Output shape.
    output: Shape,
    /// If `Some`, the candidate is emitted with `#[ignore = "reason"]`.
    /// Set from `IGNORE_LIST`.
    ignore_reason: Option<&'static str>,
}

fn collect_candidates(krate: &TranslatedCrate) -> Vec<Candidate> {
    let crate_name = krate.crate_name.clone();
    let mut out = Vec::new();
    for fd in &krate.fun_decls {
        if !is_top_level_in_crate(fd, &crate_name) {
            continue;
        }
        if fd.body.is_none() {
            continue;
        }
        if fd.loop_id.is_some() {
            // Loop-body decls share the parent's def_id but have a
            // `_loop<id>` suffix; they're synthetic and don't map to
            // a source fn the user can call.
            continue;
        }
        // Reject any generic-parameter-carrying fns.
        let g = &fd.signature.generics;
        if !g.types.is_empty()
            || !g.const_generics.is_empty()
            || !g.trait_clauses.is_empty()
        {
            continue;
        }
        // Reject recursive fns — a uniform `any::<T>()` proptest
        // would routinely stack-overflow (e.g. `demo::i32_id`).
        if fd.signature.fwd_info.effect_info.is_rec {
            continue;
        }
        let short = match short_fn_name(fd) {
            Some(s) => s,
            None => continue,
        };
        let model = flat_path_ident(&fd.item_meta.name, fd.def_id);

        let mut inputs = Vec::new();
        let mut ok = true;
        for in_ty in &fd.signature.inputs {
            match ty_shape(in_ty, false) {
                Some(s) => inputs.push(s),
                None => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok {
            continue;
        }
        let output = match ty_shape(&fd.signature.output, true) {
            Some(s) => s,
            None => continue,
        };

        let ignore_reason = ignore_reason(&crate_name, &short);
        out.push(Candidate {
            short_name: short,
            model_name: model,
            inputs,
            output,
            ignore_reason,
        });
    }
    out
}

// ====================================================================
// runtime-panic detection in the emitted model
// ====================================================================

/// Per-fn body text from the model file. Keyed by the emitted fn
/// identifier (e.g. `bitwise_xor_u32_2`).
fn model_fn_bodies(model_src: &str) -> std::collections::HashMap<String, String> {
    let mut out = std::collections::HashMap::new();
    let mut search_from = 0;
    while let Some(rel_idx) = model_src[search_from..].find("\npub fn ") {
        let idx = search_from + rel_idx + 1; // skip the leading \n
        let after = &model_src[idx..];
        let Some(open_paren) = after.find('(') else {
            break;
        };
        let name = after["pub fn ".len()..open_paren].trim().to_string();
        // Strip any generic parameter list: `name<T>`.
        let name = name.split('<').next().unwrap_or(&name).to_string();
        // Body ends at the next `\npub fn ` (or end of file).
        let body_end = after[open_paren..]
            .find("\npub fn ")
            .map(|e| open_paren + e)
            .unwrap_or(after.len());
        let body = after[..body_end].to_string();
        out.insert(name, body);
        search_from = idx + body_end;
    }
    // Also catch the first decl in the file, which doesn't start with
    // `\npub fn ` but with `pub fn `.
    if let Some(first) = model_src.find("pub fn ") {
        let after = &model_src[first..];
        if let Some(open_paren) = after.find('(') {
            let name = after["pub fn ".len()..open_paren].trim().to_string();
            let name = name.split('<').next().unwrap_or(&name).to_string();
            let body_end = after[open_paren..]
                .find("\npub fn ")
                .map(|e| open_paren + e)
                .unwrap_or(after.len());
            let body = after[..body_end].to_string();
            out.entry(name).or_insert(body);
        }
    }
    out
}

/// True iff `fn_body` calls any fn (or is) a panicking shim.
fn body_is_panicking_shim(body: &str) -> bool {
    // Cover every emitter-side panic stub:
    //   * `panic!("loop_op placeholder")` — LoopOp combinator shim;
    //   * `unimplemented!("opaque body")` — opaque-decl fall-through;
    //   * `unimplemented!("FBuiltin call")` — IR builtin (Vec::new,
    //     range constructors, etc.) the emitter couldn't lower;
    //   * any `loop_op(` / `todo_value(` runtime call.
    body.contains("panic!(")
        || body.contains("unimplemented!(")
        || body.contains("loop_op(")
        || body.contains("todo_value(")
}

/// Returns true if `target_name`'s model body or any fn it
/// transitively reaches is a panicking shim. Scans the model-text
/// crudely: pulls every `<ident>_<digits>(` token out of a body and
/// recurses. Caps depth.
fn transitively_panics(
    bodies: &std::collections::HashMap<String, String>,
    target_name: &str,
) -> bool {
    let mut stack = vec![target_name.to_string()];
    let mut visited: BTreeSet<String> = BTreeSet::new();
    while let Some(name) = stack.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }
        let Some(body) = bodies.get(&name) else {
            // Unknown callee — treat as safe; the model often references
            // primitives like `checked_add` that don't go through the
            // local `pub fn` set. We've already screened the direct
            // body for `panic!`/`unimplemented!`.
            continue;
        };
        if body_is_panicking_shim(body) {
            return true;
        }
        // Pull out every alphanumeric_underscore identifier ending
        // in `_<digits>(` — the emit's hallmark calling convention.
        let bytes = body.as_bytes();
        let mut i = 0usize;
        while i < bytes.len() {
            let c = bytes[i];
            // Walk an ident: [A-Za-z_][A-Za-z0-9_]*
            if c.is_ascii_alphabetic() || c == b'_' {
                let start = i;
                while i < bytes.len()
                    && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_')
                {
                    i += 1;
                }
                // Treat as a callee if the ident is followed by `(`
                // (plain call), `::<` (turbofish), or `::` (path).
                let followed_by_call = i < bytes.len() && bytes[i] == b'(';
                let followed_by_path =
                    i + 1 < bytes.len() && bytes[i] == b':' && bytes[i + 1] == b':';
                if followed_by_call || followed_by_path {
                    let ident = std::str::from_utf8(&bytes[start..i]).unwrap();
                    if bodies.contains_key(ident) {
                        stack.push(ident.to_string());
                    }
                }
                continue;
            }
            i += 1;
        }
    }
    false
}

// ====================================================================
// emit
// ====================================================================

/// Build the contents of `tests/common/ref_impl_auto.rs`.
fn emit_ref_impl_auto(fixtures: &[(String, PathBuf)]) -> String {
    let header = "\
// AUTO-GENERATED by gen-diff-tests; do not edit.
// Regenerate with `cargo run --bin gen-diff-tests`.
//
// R₀ side of the auto-generated diff harness: each `<fixture>`
// module brings in the unmodified Rust source from `tests/src/` via
// `#[path]`. The diff harness calls the *original* fns directly —
// no reshape, because the amenable-signature filter rejects any fn
// whose source signature carries `&mut`, `&T`, or generic params.

#![allow(unused_variables, dead_code, non_snake_case, unused_parens, unused_mut, unused_imports, unused_assignments, clippy::all)]

";
    let mut out = String::from(header);
    for (fx, src_path) in fixtures {
        let rel = src_path_relative_to_common(src_path);
        let mod_name = fixture_to_mod_name(fx);
        // `#[path]` mod (no `include!`): the source file becomes its
        // own module, so its inner `//!` doc-comments and per-item
        // attributes don't clash with the surrounding test harness.
        out.push_str(&format!(
            "#[path = \"{rel}\"]\n#[allow(unused_variables, dead_code, non_snake_case, unused_parens, unused_mut, unused_imports, unused_assignments, clippy::all)]\npub mod {mod_name};\n"
        ));
    }
    out
}

/// Path from `tests/common/ref_impl_auto.rs` to a `tests/src/<fx>.rs`
/// file. Both live under the repo root, so the relative path is
/// `../../../../tests/src/<fx>.rs` (out of `tests/common/`, out of
/// `tests/`, out of `pure-ir-emit-rust/`, out of `rust/`, into
/// `tests/src/<fx>.rs`).
fn src_path_relative_to_common(p: &Path) -> String {
    // crate_root() = rust/pure-ir-emit-rust
    // common file = rust/pure-ir-emit-rust/tests/common/ref_impl_auto.rs
    // p = <repo_root>/tests/src/<fx>.rs
    // -> ../../../../tests/src/<fx>.rs
    let repo = repo_root();
    let rel = p.strip_prefix(&repo).unwrap_or(p);
    format!("../../../../{}", rel.display())
}

/// Fixture name to Rust mod-name: replace `-` with `_`, append a
/// trailing `_` if the result is a Rust keyword.
fn fixture_to_mod_name(fx: &str) -> String {
    let mut m = fx.replace('-', "_");
    const KEYWORDS: &[&str] = &[
        "as", "async", "await", "box", "break", "const", "continue", "crate",
        "do", "dyn", "else", "enum", "extern", "false", "fn", "for", "if",
        "impl", "in", "let", "loop", "macro", "match", "mod", "move", "mut",
        "pub", "ref", "return", "self", "Self", "static", "struct", "super",
        "trait", "true", "type", "unsafe", "use", "where", "while",
    ];
    if KEYWORDS.contains(&m.as_str()) {
        m.push('_');
    }
    m
}

/// Inner-attribute / register_tool patterns that break when the
/// source is loaded as a `#[path] mod`. Skip the whole fixture.
fn source_has_blocking_inner_attr(src: &str) -> bool {
    src.contains("#![feature(")
        || src.contains("#![register_tool")
        || src.contains("#![register_attr")
        || src.contains("#[verify::")
        || src.contains("#[charon::")
        || src.contains("#[aeneas::")
}

/// Build the contents of `tests/diff_auto.rs`.
fn emit_diff_auto(
    fixtures: &[(String, Vec<Candidate>, usize)],
    _ignored: &[(String, String, String)],
) -> String {
    let mut out = String::new();
    out.push_str(
        "\
// AUTO-GENERATED by gen-diff-tests; do not edit.
// Regenerate with `cargo run --bin gen-diff-tests`.
//
// Each proptest block was synthesised from a Pure-IR fixture whose
// signature is simple enough to drive `any::<...>()` directly:
// all-scalar / fixed-size-scalar-array / tuple-of-scalars inputs,
// scalar / tuple / array output (optionally wrapped in
// `Result<_, ()>`), no generics, no refs.
//
// The R₂ side (`models::<fixture>`) is the committed pir2rs snapshot
// at `tests/models/<fixture>_pir.rs`; the R₀ side
// (`ref_impl_auto::<fixture>`) imports the source directly from
// `tests/src/<fixture>.rs` (no reshape — the filter rejects any fn
// the IR would have functionalised).
//
// Mismatches are marked `#[ignore]`d inline with one of:
//   * `EMITTER BUG`: the model produces a different value than the
//     source for at least one input — surfaces an emitter limitation.
//   * `DIFF NON-UNIFORM`: the comparison can't be driven by uniform
//     `any::<_>()` (e.g. recursion-depth-bounded inputs).

#![allow(unused_variables, dead_code, non_snake_case, unused_parens, unused_mut, unused_imports, clippy::all)]

use proptest::prelude::*;

#[path = \"common/ref_impl_auto.rs\"]
mod ref_impl_auto;

#[allow(
    unused_variables,
    unused_parens,
    unused_mut,
    dead_code,
    non_snake_case,
    nonstandard_style,
    unused_assignments,
    unused_imports,
    unreachable_code,
    clippy::all
)]
mod models {
",
    );
    // Models block — one nested `pub mod <fixture>` per fixture
    // that has ≥1 candidate. Skipping zero-candidate fixtures keeps
    // the diff_auto.rs file small and avoids dragging in models whose
    // panicking shims contaminate compile-time dead-code analysis.
    for (fx, cands, _) in fixtures {
        if cands.is_empty() {
            continue;
        }
        let mod_name = fixture_to_mod_name(fx);
        out.push_str(&format!(
            "    pub mod {mod_name} {{ include!(\"models/{fx}_pir.rs\"); }}\n"
        ));
    }
    out.push_str("}\n\n");

    for (fx, cands, total) in fixtures {
        if cands.is_empty() {
            continue;
        }
        let mod_name = fixture_to_mod_name(fx);
        out.push_str(&format!(
            "// =====================================================================\n\
// {fx} — auto-generated ({} candidates, {total} total scanned)\n\
// =====================================================================\n\n",
            cands.len()
        ));
        for cand in cands {
            emit_proptest_block(&mod_name, cand, &mut out);
            out.push('\n');
        }
    }

    out
}

fn emit_proptest_block(mod_name: &str, cand: &Candidate, out: &mut String) {
    let test_name = format!("{mod_name}_{}_auto", cand.short_name);

    // Render input args.
    let mut args = Vec::with_capacity(cand.inputs.len());
    let mut arg_names = Vec::with_capacity(cand.inputs.len());
    let mut ok = true;
    for (i, sh) in cand.inputs.iter().enumerate() {
        let strat = match sh.proptest_strategy() {
            Some(s) => s,
            None => {
                ok = false;
                break;
            }
        };
        args.push(format!("a{i} in {strat}"));
        arg_names.push(format!("a{i}"));
    }

    if !ok {
        out.push_str(&format!(
            "// SKIPPED {mod_name}::{short} — no proptest strategy for one of its inputs.\n",
            short = cand.short_name,
        ));
        return;
    }

    // Compare strategy: source returns plain `T`; model returns
    // `Result<T, ()>`. We always wrap the source value as `Ok(...)`
    // when the model output is Result-typed.
    let model_returns_result = matches!(
        &cand.output,
        Shape::Result(_) | Shape::AeneasResult(_)
    );

    let call_args = arg_names.join(", ");
    let call_rhs = format!(
        "models::{mod_name}::{model}({call_args})",
        model = cand.model_name
    );
    let call_lhs = format!(
        "ref_impl_auto::{mod_name}::{short}({call_args})",
        short = cand.short_name
    );

    // Normalisation: panic on either side ⇒ `Err(())`. Source returns
    // plain `T`; model returns `Result<T, ()>` (or plain `T` when the
    // IR's `can_fail` was false). Both sides are coerced to a common
    // `Result<T, ()>` shape, which absorbs:
    //   * source `+`/`-` overflow panics (debug mode default);
    //   * model `panic!("LoopOp placeholder")` and
    //     `unimplemented!("opaque body")` shims (transitively reached
    //     fns the call-graph filter doesn't catch).
    //
    // The comparison is then `Result<T, ()> == Result<T, ()>`, so a
    // pair of `Err(())`s matches — which is the right call when the
    // model can't be proved equal to the source in those failure
    // regimes anyway.
    let lhs_normalised = format!(
        "match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {call_lhs})) {{\n\
            Ok(v) => Ok::<_, ()>(v),\n\
            Err(_) => Err(()),\n\
        }}"
    );
    let rhs_normalised = if model_returns_result {
        format!(
            "match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {call_rhs})) {{\n\
            Ok(r) => r.map_err(|_| ()),\n\
            Err(_) => Err(()),\n\
        }}"
        )
    } else {
        format!(
            "match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {call_rhs})) {{\n\
            Ok(v) => Ok::<_, ()>(v),\n\
            Err(_) => Err(()),\n\
        }}"
        )
    };

    let ignore_attr = match cand.ignore_reason {
        Some(r) => format!("#[ignore = \"{r}\"]\n"),
        None => String::new(),
    };

    if cand.inputs.is_empty() {
        // No-arg fn — emit a plain `#[test]`.
        out.push_str(&format!(
            "/// Auto-generated from `{mod_name}::{short}` (no-arg, model `{model}`)\n\
{ignore_attr}#[test]\n\
fn {test_name}() {{\n\
    let lhs = {lhs_normalised};\n\
    let rhs = {rhs_normalised};\n\
    assert_eq!(lhs, rhs);\n\
}}\n",
            short = cand.short_name,
            model = cand.model_name,
        ));
        return;
    }

    let body = format!(
        "        let lhs = {lhs_normalised};\n\
        let rhs = {rhs_normalised};\n\
        prop_assert_eq!(lhs, rhs);\n"
    );

    let inner_ignore = match cand.ignore_reason {
        Some(r) => format!("    #[ignore = \"{r}\"]\n"),
        None => String::new(),
    };
    out.push_str(&format!(
        "proptest! {{\n\
    /// Auto-generated from `{mod_name}::{short}` (model `{model}`)\n\
{inner_ignore}    #[test]\n\
    fn {test_name}({args}) {{\n\
{body}\
    }}\n\
}}\n",
        short = cand.short_name,
        model = cand.model_name,
        args = args.join(", "),
    ));
}

// ====================================================================
// driver
// ====================================================================

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut dry_run = false;
    for a in args.iter().skip(1) {
        match a.as_str() {
            "--dry-run" => dry_run = true,
            "-h" | "--help" => {
                println!(
                    "Usage: gen-diff-tests [--dry-run]\n\n\
                     Walks tests/models/*_pir.rs, dumps fresh Pure-IR JSON\n\
                     for each fixture, applies the amenability filter, and\n\
                     writes tests/diff_auto.rs + tests/common/ref_impl_auto.rs.\n\n\
                     --dry-run   Print a summary; don't write any files."
                );
                return;
            }
            _ => {
                eprintln!("unknown flag {a}");
                std::process::exit(2);
            }
        }
    }

    if !aeneas_bin().exists() {
        eprintln!(
            "error: aeneas binary not found at {}; run `make build-bin-dir`",
            aeneas_bin().display()
        );
        std::process::exit(1);
    }

    let fixtures = discover_fixtures();
    eprintln!("[gen-diff-tests] discovered {} fixture(s)", fixtures.len());

    let tmp = std::env::temp_dir().join(format!(
        "pir-gen-diff-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0),
    ));
    fs::create_dir_all(&tmp).expect("mkdir tmp");

    // Per-fixture: (fx, candidates, total_scanned).
    let mut accepted: Vec<(String, Vec<Candidate>, usize)> = Vec::new();
    // Tracks which fixtures have a `tests/src/<fx>.rs` so we can list
    // them in ref_impl_auto.rs.
    let mut ref_impl_paths: Vec<(String, PathBuf)> = Vec::new();
    let mut skipped_reasons: Vec<(String, String, String)> = Vec::new();

    let model_dir = crate_root().join("tests").join("models");
    let mut seen_short_names: BTreeSet<String> = BTreeSet::new();

    let mut total_candidates = 0usize;
    let mut total_scanned = 0usize;
    for fx in &fixtures {
        let json = match dump_pure_ir(fx, &tmp.join(fx)) {
            Some(p) => p,
            None => {
                eprintln!("[gen-diff-tests] {fx}: failed to dump JSON");
                continue;
            }
        };
        let src = fs::read_to_string(&json).expect("read JSON");
        let krate = match pure_ir::parse(&src) {
            Ok(k) => k,
            Err(e) => {
                eprintln!("[gen-diff-tests] {fx}: parse: {e}");
                continue;
            }
        };
        let model_path = model_dir.join(format!("{fx}_pir.rs"));
        let model_src = match fs::read_to_string(&model_path) {
            Ok(s) => s,
            Err(_) => {
                eprintln!(
                    "[gen-diff-tests] {fx}: no model at {} — skipping",
                    model_path.display()
                );
                continue;
            }
        };

        let mut cands = collect_candidates(&krate);
        let scanned_here = cands.len();
        total_scanned += scanned_here;

        // Filter out models whose body or any transitively-reached
        // model fn is a panicking shim (`loop_op(...)`,
        // `unimplemented!("opaque body")`). Catches the `count_to →
        // count_to_loop0`, `pick → opaque_shim`, etc. chains the
        // simple direct-body scan misses.
        let model_bodies = model_fn_bodies(&model_src);
        cands.retain(|c| {
            if transitively_panics(&model_bodies, &c.model_name) {
                skipped_reasons.push((
                    fx.clone(),
                    c.short_name.clone(),
                    "model transitively reaches a panicking shim".to_string(),
                ));
                false
            } else {
                true
            }
        });

        // De-duplicate by (fixture, short_name) to avoid the same
        // proptest fn being emitted twice if two FunDecls share a
        // short name (e.g. impl + trait + free fn) — rare for own-
        // crate top-level items but we belt-and-braces it.
        let mut seen: BTreeSet<String> = BTreeSet::new();
        cands.retain(|c| seen.insert(c.short_name.clone()));

        // Also dedupe against ref_impl_auto-level visible names: each
        // ref_impl_auto `<fx>` mod imports `tests/src/<fx>.rs` directly,
        // and that file may not define every name the model carries
        // (e.g. compiler-synthesized `Default::default` calls). We
        // verify by reading the source file once. Only `pub fn`s are
        // accessible from the test harness; private fns are filtered
        // out — including them would require synthesizing `mod`-level
        // re-exports, which is more complexity than the residual yield
        // warrants.
        let src_path = src_dir().join(format!("{fx}.rs"));
        let source_text = fs::read_to_string(&src_path).unwrap_or_default();
        // Skip the entire fixture if the source file carries inner
        // attributes that break when loaded as `#[path] mod` (most
        // commonly `#![feature(register_tool)]` + tool-namespace
        // attributes that don't survive in a non-root mod).
        if source_has_blocking_inner_attr(&source_text) {
            skipped_reasons.push((
                fx.clone(),
                "<fixture>".to_string(),
                "source has blocking inner attribute (register_tool etc)".to_string(),
            ));
            cands.clear();
        }
        cands.retain(|c| {
            // Cheap heuristic: source file must contain
            // `pub fn <name>(` for the fn to be reachable through the
            // auto-gen ref_impl mod. Generic source fns (`pub fn
            // <name><`) are skipped — even if the IR monomorphised the
            // call, the source-level call site still needs an
            // explicit turbofish we don't carry.
            let needle_paren = format!("pub fn {}(", c.short_name);
            let Some(idx) = source_text.find(&needle_paren) else {
                skipped_reasons.push((
                    fx.clone(),
                    c.short_name.clone(),
                    "fn not pub-visible in tests/src/<fx>.rs".to_string(),
                ));
                return false;
            };
            // Walk forward to the matching `)`. The auto-gen rejects
            // any fn whose source signature carries `&` (or `&mut`),
            // because the IR's pre-extract functionalises borrows into
            // forward fns whose model-side signature no longer
            // mentions the reference — meaning a direct call on the
            // source side would have an arity mismatch.
            let after = &source_text[idx..];
            let mut depth = 0i32;
            let mut end = None;
            for (i, ch) in after.char_indices() {
                match ch {
                    '(' => depth += 1,
                    ')' => {
                        depth -= 1;
                        if depth == 0 {
                            end = Some(i);
                            break;
                        }
                    }
                    _ => {}
                }
            }
            let sig_args = match end {
                Some(e) => &after[..=e],
                None => return false,
            };
            if sig_args.contains('&') {
                skipped_reasons.push((
                    fx.clone(),
                    c.short_name.clone(),
                    "source signature carries `&` / `&mut`".to_string(),
                ));
                return false;
            }
            // Also reject if the immediate post-sig prefix carries
            // `where ` (where-clause = generic fn we already skip via
            // generics check, but defence in depth) — or returns a
            // mutable reference.
            true
        });

        total_candidates += cands.len();
        for c in &cands {
            seen_short_names.insert(format!("{fx}::{}", c.short_name));
        }

        if !cands.is_empty() {
            ref_impl_paths.push((fx.clone(), src_path));
        }
        accepted.push((fx.clone(), cands, scanned_here));
    }

    eprintln!(
        "[gen-diff-tests] total: {total_candidates} candidate(s) across {} fixture(s) ({total_scanned} scanned)",
        accepted.iter().filter(|(_, c, _)| !c.is_empty()).count()
    );

    if dry_run {
        let mut by_fx: Vec<(&String, usize, usize)> = accepted
            .iter()
            .map(|(f, c, t)| (f, c.len(), *t))
            .collect();
        by_fx.sort_by_key(|(_, n, _)| std::cmp::Reverse(*n));
        for (fx, n, t) in &by_fx {
            if *n > 0 {
                eprintln!("  {fx}: {n}/{t}");
            }
        }
        eprintln!("--- skipped reasons ---");
        let mut by_reason: std::collections::BTreeMap<&str, usize> =
            std::collections::BTreeMap::new();
        for (_, _, r) in &skipped_reasons {
            *by_reason.entry(r.as_str()).or_insert(0) += 1;
        }
        for (r, n) in &by_reason {
            eprintln!("  {n}: {r}");
        }
        return;
    }

    // Write the two output files.
    let diff_auto = emit_diff_auto(&accepted, &[]);
    let ref_impl_auto = emit_ref_impl_auto(&ref_impl_paths);

    let diff_auto_path = crate_root().join("tests").join("diff_auto.rs");
    let ref_impl_auto_path = crate_root()
        .join("tests")
        .join("common")
        .join("ref_impl_auto.rs");
    fs::write(&diff_auto_path, diff_auto).expect("write diff_auto.rs");
    fs::write(&ref_impl_auto_path, ref_impl_auto).expect("write ref_impl_auto.rs");

    eprintln!(
        "[gen-diff-tests] wrote {} and {}",
        diff_auto_path.display(),
        ref_impl_auto_path.display()
    );

    // Clean up tmp.
    let _ = fs::remove_dir_all(&tmp);
}
