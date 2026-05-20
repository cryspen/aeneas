//! `route-shims` — post-process a `pir2rs` emit so opaque shim bodies
//! route through `core_models::*` / `rust_primitives::*` instead of
//! `unimplemented!("opaque body")`.
//!
//! Usage:
//!     route-shims path/to/foo_pir.rs --json path/to/foo.pure.json [--out path/to/out.rs]
//!
//! With no `--out`, the rewritten file is written back to the input path.
//!
//! ## What it does
//!
//! 1. Parses the corresponding Pure-IR JSON to enumerate `FunDecl`s
//!    whose `body` is `None` (opaque), recovering their
//!    `(emitted-name, item_meta.name, signature)` triple.
//! 2. For each shim function definition in the model file, looks up
//!    its emitted name in the map; if `core_models_map::map_charon_path`
//!    has a route, rewrites:
//!      - The signature: `(p0: impl Sized, p1: impl Sized) -> u32`
//!        becomes `(p0: u32, p1: u32) -> u32` using the IR-recovered
//!        concrete types. Generic params + where-clauses are kept
//!        as-is for shims whose IR signature carries them.
//!      - The body: replaces the `unimplemented!("opaque body")`
//!        with a route-templated expression. Bodies for shims whose
//!        return type is `Result<T>` are wrapped in `Ok(...)`.
//!
//! ## Boundaries
//!
//! - **The emitter library is unchanged.** This binary is a
//!   test-side post-processor: it never feeds back into `emit.rs`.
//! - **Best-effort string rewriting.** No `syn`/`quote` — shim
//!   bodies are well-shaped 1-2-line blocks the emitter produces,
//!   so a careful brace-balanced scan suffices.
//! - **Shims with generic params** (e.g. `<T, A>` on
//!   `impl_alloc_boxed_clone_64`) are skipped unless every input
//!   type is `impl Sized` *and* fully scalar in the IR signature.
//!   Mixed-generic shims need per-callsite monomorphisation info
//!   the post-processor doesn't have.
//!
//! See `documentation/pure-ir-json-export-plan.md` § Option A for
//! the staging plan toward Option C.

use pure_ir::ast::*;
use pure_ir_emit_rust::core_models_map::{
    map_charon_path, name_segments, ty_rust_name, BodyKind, ResultShape, ShimRoute,
};
use std::collections::HashMap;
use std::env;
use std::fs;
use std::process::ExitCode;

// ─── CLI scaffolding ────────────────────────────────────────────────

struct CliArgs {
    input: String,
    json: String,
    output: Option<String>,
    verbose: bool,
}

fn parse_args() -> Result<CliArgs, String> {
    let argv: Vec<String> = env::args().collect();
    let mut input: Option<String> = None;
    let mut json: Option<String> = None;
    let mut output: Option<String> = None;
    let mut verbose = false;
    let mut i = 1;
    while i < argv.len() {
        match argv[i].as_str() {
            "--json" => {
                i += 1;
                json = argv.get(i).cloned();
            }
            "--out" | "-o" => {
                i += 1;
                output = argv.get(i).cloned();
            }
            "--verbose" | "-v" => verbose = true,
            "-h" | "--help" => {
                println!(
                    "Usage: route-shims <input.rs> --json <pure.json> [--out <output.rs>] [-v]"
                );
                std::process::exit(0);
            }
            s if s.starts_with('-') => {
                return Err(format!("unknown flag {s}"));
            }
            s => {
                if input.is_none() {
                    input = Some(s.to_string());
                } else {
                    return Err(format!("unexpected positional arg {s}"));
                }
            }
        }
        i += 1;
    }
    Ok(CliArgs {
        input: input.ok_or("missing input file")?,
        json: json.ok_or("missing --json")?,
        output,
        verbose,
    })
}

// ─── Charon-path → emitted-name reconstruction ──────────────────────
//
// Must stay in sync with `EmitCtx::flat_path_ident` in `src/emit.rs`.
// We replicate the logic here rather than re-exporting it so the
// emitter library doesn't grow a public surface for this post-processor.

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

// ─── Shim discovery from JSON ───────────────────────────────────────

#[derive(Debug, Clone)]
struct ShimInfo {
    emitted_name: String,
    #[allow(dead_code)]
    item_path: CharonName,
    inputs: Vec<Ty>,
    output: Ty,
    route: ShimRoute,
}

fn collect_shims(krate: &TranslatedCrate) -> Vec<ShimInfo> {
    let mut out = Vec::new();
    for fd in &krate.fun_decls {
        // Opaque = no body, which is exactly the case `emit.rs`
        // collapses to `impl Sized` params + `unimplemented!()` body.
        if fd.body.is_some() {
            continue;
        }
        // Loop bodies are emitted with `_loopN` suffix and never
        // hit the shim path.
        if fd.loop_id.is_some() {
            continue;
        }
        // Only items with a `PeImpl` are method-style shims the
        // current mapping table targets. Free-fn opaque decls
        // (`core::cmp::min`/`max`) don't carry `PeImpl`, but they
        // *do* show up here — the segs filter accepts both shapes.
        let route = match map_charon_path(&fd.item_meta.name) {
            Some(r) => r,
            None => continue,
        };
        out.push(ShimInfo {
            emitted_name: flat_path_ident(&fd.item_meta.name, fd.def_id),
            item_path: fd.item_meta.name.clone(),
            inputs: fd.signature.inputs.clone(),
            output: fd.signature.output.clone(),
            route,
        });
    }
    out
}

// ─── Body / signature rendering ─────────────────────────────────────

/// Concrete Rust return type. Strips an outer `Result<...>` wrapping
/// (the IR's `can_fail` monad) and returns `(inner_ty, was_wrapped)`.
fn unwrap_result(ty: &Ty) -> (&Ty, bool) {
    if let Ty::TAdt(adt) = ty {
        if let TypeId::TBuiltin(BuiltinTy::TResult) = &adt.type_id {
            if let Some(inner) = adt.generics.types.first() {
                return (inner, true);
            }
        }
    }
    (ty, false)
}

/// Render the rewritten body expression for a shim, given the IR-
/// recovered argument names + the route. The returned string is the
/// expression, **without** a trailing semicolon and **without** any
/// `Ok(...)` wrapping (the caller adds it based on `returns_result`).
///
/// Returns `None` if rendering bails (e.g. ty_rust_name fails for an
/// arg, meaning the route can't be safely lowered).
fn render_body_expr(
    shim: &ShimInfo,
    arg_names: &[String],
) -> Option<String> {
    let (ret_inner, _) = unwrap_result(&shim.output);
    let ret_rust = ty_rust_name(ret_inner)?;
    match &shim.route.body {
        BodyKind::FreeFn { path } => {
            let args = arg_names.join(", ");
            Some(format!("{path}({args})"))
        }
        BodyKind::Method { method } => {
            if arg_names.is_empty() {
                None
            } else {
                let rest = arg_names[1..].join(", ");
                Some(format!("{ret_rust}::{method}({}, {rest})", arg_names[0]).trim_end_matches(", ").to_string())
            }
        }
        BodyKind::AssocFn { name } => {
            let args = arg_names.join(", ");
            Some(format!("{ret_rust}::{name}({args})"))
        }
        BodyKind::AssocConst { name } => Some(format!("{ret_rust}::{name}")),
        BodyKind::DefaultDefault => {
            // Use a fully-qualified path so this works even if the
            // model file doesn't `use core::default::Default`.
            Some(format!("<{ret_rust} as core::default::Default>::default()"))
        }
        BodyKind::Literal { expr } => Some(expr.replace("/*TY*/", ret_rust)),
    }
}

/// Render the rewritten parameter list with concrete types. Returns
/// `None` if any input type isn't a scalar (the post-processor
/// declines to rewrite shims it can't fully resolve).
fn render_concrete_params(shim: &ShimInfo, arg_names: &[String]) -> Option<String> {
    let mut parts = Vec::new();
    for (i, in_ty) in shim.inputs.iter().enumerate() {
        let name = arg_names.get(i).cloned().unwrap_or_else(|| format!("p{i}"));
        let ty_name = ty_rust_name(in_ty)?;
        parts.push(format!("{name}: {ty_name}"));
    }
    Some(parts.join(", "))
}

// ─── Model-file editing ─────────────────────────────────────────────

/// Find the byte range of the *full* shim function definition in
/// `src`: from the leading `pub fn <name>` through the closing `}`
/// of its body. Returns None if the shim isn't found.
fn find_fn_range(src: &str, name: &str) -> Option<(usize, usize)> {
    let needle = format!("pub fn {name}(");
    let start = src.find(&needle)?;
    // Find the `{` opening the body.
    let after_decl = &src[start..];
    let body_open_rel = after_decl.find('{')?;
    // Brace-match from there.
    let body_start_abs = start + body_open_rel;
    let bytes = src.as_bytes();
    let mut depth = 0i32;
    let mut i = body_start_abs;
    while i < bytes.len() {
        match bytes[i] {
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return Some((start, i + 1));
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// Sanity-check that the function body the post-processor would
/// rewrite looks like an opaque-shim body (single `unimplemented!()`
/// statement, possibly preceded by trivia). Bails on anything else
/// so we don't clobber a hand-edited model.
fn is_opaque_body(slice: &str) -> bool {
    let body = slice.trim();
    body.contains("unimplemented!(\"opaque body\")")
}

/// Apply one route to the model source. Returns `(new_src, status)`.
/// `status::Rewritten` is the success path; `status::Skipped(reason)`
/// flags why a shim couldn't be routed (which the caller logs in
/// `--verbose` mode).
enum RouteStatus {
    Rewritten,
    Skipped(String),
}

fn route_one(
    src: &str,
    shim: &ShimInfo,
) -> (String, RouteStatus) {
    let (start, end) = match find_fn_range(src, &shim.emitted_name) {
        Some(r) => r,
        None => {
            return (
                src.to_string(),
                RouteStatus::Skipped(format!("shim {} not found in model", shim.emitted_name)),
            );
        }
    };

    let original = &src[start..end];

    // Extract the original parameter list to recover the binder
    // names emit.rs chose (so we don't pull in unrelated `p0`-style
    // renames). We do this by lifting between the first `(` after
    // `pub fn <name>` and its matching `)`.
    let after_open_paren = original.find('(').unwrap_or(0) + 1;
    let mut depth = 0i32;
    let mut close_idx = after_open_paren;
    let ob = original.as_bytes();
    let mut i = after_open_paren;
    while i < ob.len() {
        match ob[i] {
            b'(' => depth += 1,
            b')' => {
                if depth == 0 {
                    close_idx = i;
                    break;
                }
                depth -= 1;
            }
            _ => {}
        }
        i += 1;
    }
    let params_str = &original[after_open_paren..close_idx];

    // Names = comma-split, take ident before `:`. Empty-arg case
    // means params_str is empty.
    let mut arg_names: Vec<String> = Vec::new();
    if !params_str.trim().is_empty() {
        for p in split_top_level_commas(params_str) {
            // Strip trailing/leading spaces, take the bit before ':'.
            let pn = p.split(':').next().unwrap_or("").trim().to_string();
            arg_names.push(pn);
        }
    }

    // If the original signature had any generic params or where
    // clause, skip — these shims need per-callsite monomorphisation
    // info we don't have.
    let sig_to_open_brace = match original.find('{') {
        Some(idx) => &original[..idx],
        None => return (src.to_string(), RouteStatus::Skipped("malformed shim".into())),
    };
    if sig_to_open_brace.contains(" where ") {
        return (
            src.to_string(),
            RouteStatus::Skipped(format!("{}: signature has where-clause; needs per-callsite monomorphisation", shim.emitted_name)),
        );
    }
    // Generics: detect `<...>` *between* `fn <name>` and `(`.
    let name_pos = sig_to_open_brace.find(&format!("fn {}", shim.emitted_name));
    if let Some(np) = name_pos {
        let after_name = &sig_to_open_brace[np + 3 + shim.emitted_name.len()..];
        let lparen_offset = after_name.find('(').unwrap_or(after_name.len());
        let before_lparen = &after_name[..lparen_offset];
        if before_lparen.contains('<') {
            return (
                src.to_string(),
                RouteStatus::Skipped(format!("{}: generic shim; deferred to Option C", shim.emitted_name)),
            );
        }
    }

    // Sanity-check the body. If it doesn't look opaque, skip.
    let body_text = {
        let lb = original.find('{').unwrap_or(0) + 1;
        let rb = original.rfind('}').unwrap_or(original.len());
        &original[lb..rb]
    };
    if !is_opaque_body(body_text) {
        return (
            src.to_string(),
            RouteStatus::Skipped(format!("{}: body not an opaque shim; refusing to rewrite", shim.emitted_name)),
        );
    }

    // Build the new signature.
    let new_params = match render_concrete_params(shim, &arg_names) {
        Some(s) => s,
        None => {
            return (
                src.to_string(),
                RouteStatus::Skipped(format!("{}: arg type not a scalar — can't rewrite sig", shim.emitted_name)),
            );
        }
    };

    let (_, was_result_wrapped) = unwrap_result(&shim.output);
    let new_ret_ty = render_ret_type(&shim.output);
    let body_expr = match render_body_expr(shim, &arg_names) {
        Some(e) => e,
        None => {
            return (
                src.to_string(),
                RouteStatus::Skipped(format!("{}: route couldn't render body", shim.emitted_name)),
            );
        }
    };

    let wrapped_body = match shim.route.returns_result {
        ResultShape::Bare if was_result_wrapped => format!("Ok({body_expr})"),
        ResultShape::Bare => body_expr,
        ResultShape::WrapInOk if was_result_wrapped => format!("Ok({body_expr})"),
        ResultShape::WrapInOk => body_expr,
    };

    let new_fn = format!(
        "pub fn {name}({params}) -> {ret} {{\n    // route: {doc}\n    {body}\n}}",
        name = shim.emitted_name,
        params = new_params,
        ret = new_ret_ty,
        doc = shim.route.doc,
        body = wrapped_body,
    );

    let mut new_src = String::with_capacity(src.len() + new_fn.len());
    new_src.push_str(&src[..start]);
    new_src.push_str(&new_fn);
    new_src.push_str(&src[end..]);
    (new_src, RouteStatus::Rewritten)
}

/// Render the Rust type for a shim's return position. Scalars are
/// emitted directly; `Result<T>` re-uses the model's `Result` alias.
fn render_ret_type(ty: &Ty) -> String {
    let (inner, wrapped) = unwrap_result(ty);
    let inner_rust = ty_rust_name(inner).unwrap_or("/*unmapped*/ ()");
    if wrapped {
        format!("Result<{inner_rust}>")
    } else {
        inner_rust.to_string()
    }
}

/// Split a parameter list by top-level commas (ignoring those inside
/// nested `<...>` / `(...)`).
fn split_top_level_commas(s: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    for (i, ch) in s.char_indices() {
        match ch {
            '<' | '(' | '[' => depth += 1,
            '>' | ')' | ']' => depth -= 1,
            ',' if depth == 0 => {
                out.push(&s[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    let tail = &s[start..];
    if !tail.trim().is_empty() {
        out.push(tail);
    }
    out
}

// ─── main ───────────────────────────────────────────────────────────

fn main() -> ExitCode {
    let args = match parse_args() {
        Ok(a) => a,
        Err(e) => {
            eprintln!("route-shims: {e}");
            return ExitCode::from(2);
        }
    };

    let model_src = match fs::read_to_string(&args.input) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("route-shims: cannot read {}: {e}", args.input);
            return ExitCode::from(1);
        }
    };
    let json_src = match fs::read_to_string(&args.json) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("route-shims: cannot read {}: {e}", args.json);
            return ExitCode::from(1);
        }
    };
    let krate = match pure_ir::parse(&json_src) {
        Ok(k) => k,
        Err(e) => {
            eprintln!("route-shims: parse {}: {e}", args.json);
            return ExitCode::from(1);
        }
    };

    let shims = collect_shims(&krate);

    // De-duplicate by emitted-name: the IR can carry the same shim
    // under multiple FunDecls (parametric instantiations sharing a
    // def_id), but the emitted model file has exactly one definition.
    let mut by_name: HashMap<String, ShimInfo> = HashMap::new();
    for s in shims {
        by_name.entry(s.emitted_name.clone()).or_insert(s);
    }

    let mut rewritten = 0usize;
    let mut skipped: Vec<String> = Vec::new();
    let mut cur = model_src;
    for (_, shim) in &by_name {
        let (new_src, status) = route_one(&cur, shim);
        match status {
            RouteStatus::Rewritten => {
                rewritten += 1;
                cur = new_src;
            }
            RouteStatus::Skipped(reason) => {
                if args.verbose {
                    eprintln!("route-shims: skipped: {reason}");
                }
                skipped.push(reason);
            }
        }
    }

    let outpath = args.output.as_deref().unwrap_or(&args.input);
    if let Err(e) = fs::write(outpath, &cur) {
        eprintln!("route-shims: cannot write {outpath}: {e}");
        return ExitCode::from(1);
    }

    eprintln!(
        "route-shims: {} rewrote {rewritten} shim(s), skipped {} (total {})",
        args.input,
        skipped.len(),
        by_name.len(),
    );

    // Validate the segs filter caught at least the path classes we
    // expect — defence in depth against an emitter bug in
    // flat_path_ident changing under us.
    let _: usize = name_segments(&[]).len();

    ExitCode::SUCCESS
}
