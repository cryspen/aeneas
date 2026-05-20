//! IR-faithful Rust emitter for the Pure-IR JSON AST.
//!
//! The output is intentionally **not** a byte-for-byte recovery of the
//! original Rust source — symbolic-to-pure has functionalised mutable
//! borrows, fused loops into recursive helpers, and threaded `Result`
//! through every fallible operation. The emitter targets:
//!
//! 1. Syntactically valid Rust (`rustc --edition 2021` parses it).
//! 2. Structurally faithful to the Pure IR (one Rust construct per
//!    AST node, with no folding back into idiomatic Rust).
//!
//! Unhandled or impossible-to-emit variants degrade gracefully to
//! `unimplemented!()` with a `// TODO: <variant>` comment, keeping the
//! output parseable.

use pure_ir::ast::*;
use std::collections::HashMap;
use std::fmt::Write;

#[derive(Debug, Clone, Default)]
pub struct EmitOptions {
    /// If true, include a banner comment naming the source crate +
    /// pipeline stage.
    pub include_banner: bool,
}

/// Top-level entry point: turn a parsed Pure-IR crate into a Rust
/// source string.
pub fn emit_crate(krate: &TranslatedCrate, opts: &EmitOptions) -> String {
    let mut out = String::new();

    if opts.include_banner {
        let _ = writeln!(
            out,
            "// Auto-emitted from Pure-IR JSON ({} stage `{}`).",
            krate.crate_name, krate.stage,
        );
        out.push_str("// See documentation/pure-ir-json-export-plan.md (Phase 4 MVP).\n\n");
    }

    // A tiny prelude lets the rest of the emit stay schematic.
    out.push_str(PRELUDE);
    out.push_str("use self::aeneas_runtime::Result;\n\n");

    // Build a lookup from type-decl id → short name for ADT pretty
    // printing.
    let type_decls: HashMap<u64, &TypeDecl> =
        krate.type_decls.iter().map(|t| (t.def_id, t)).collect();
    // FunDecls share `def_id` between the entry decl and each loop-
    // body decl (distinguished by `loop_id`). We index by
    // `(def_id, loop_id)` so callers can disambiguate; the lookup at
    // a call site folds back to "no loop marker" for the entry path.
    let fun_decls: HashMap<(u64, Option<u64>), &FunDecl> = krate
        .fun_decls
        .iter()
        .map(|f| ((f.def_id, f.loop_id.as_ref().map(|l| l.loop_id)), f))
        .collect();

    let ctx = EmitCtx {
        type_decls: &type_decls,
        fun_decls: &fun_decls,
    };

    for td in &krate.type_decls {
        let gctx = GenCtx::from_params(&td.generics);
        emit_type_decl(td, &ctx, &gctx, &mut out);
        out.push('\n');
    }

    for fd in &krate.fun_decls {
        let gctx = GenCtx::from_params(&fd.signature.generics);
        emit_fun_decl(fd, &ctx, &gctx, &mut out);
        out.push('\n');
    }

    out
}

const PRELUDE: &str = "\
#![allow(unused_variables, unused_parens, unused_mut, dead_code, non_snake_case, unused_assignments, unused_imports, unreachable_code, clippy::all)]

pub mod aeneas_runtime {
    /// Aeneas pure-IR runtime shim: Result encodes the `can_fail`
    /// monad threaded by symbolic-to-pure. The unit error keeps the
    /// emitted code minimal; downstream models can refine.
    pub type Result<T> = core::result::Result<T, ()>;

    #[inline] pub fn ret<T>(x: T) -> Result<T> { Ok(x) }
    #[inline] pub fn fail<T>() -> Result<T> { Err(()) }

    /// Stub `LoopOp`: the IR's loop fixed-point combinator. At the
    /// Rust level we only need a placeholder with the right type
    /// shape so the surrounding code typechecks; the real semantics
    /// live in the Lean translation.
    #[inline] pub fn loop_op<T, F: FnOnce(T) -> Result<T>>(_body: F, init: T) -> Result<T> {
        Ok(init)
    }
}

";

// ---------- emit context (decl lookup tables) ----------

struct EmitCtx<'a> {
    type_decls: &'a HashMap<u64, &'a TypeDecl>,
    fun_decls: &'a HashMap<(u64, Option<u64>), &'a FunDecl>,
}

/// Per-decl generic-parameter context: name lookup for `TVar(Bound)`
/// references. The IR carries de-Bruijn indices into the surrounding
/// generic-param list; we resolve at emit time using the parent decl's
/// `GenericParams`.
#[derive(Default)]
struct GenCtx {
    type_names: Vec<String>,
    const_names: Vec<String>,
}

impl GenCtx {
    fn from_params(g: &GenericParams) -> Self {
        let type_names = g.types.iter().map(|t| sanitize_ident(&t.name)).collect();
        let const_names = g
            .const_generics
            .iter()
            .map(|c| sanitize_ident(&c.name))
            .collect();
        GenCtx {
            type_names,
            const_names,
        }
    }
    fn type_var(&self, id: u64) -> String {
        self.type_names
            .get(id as usize)
            .cloned()
            .unwrap_or_else(|| format!("T{id}"))
    }
    fn const_var(&self, id: u64) -> String {
        self.const_names
            .get(id as usize)
            .cloned()
            .unwrap_or_else(|| format!("N{id}"))
    }
}

impl<'a> EmitCtx<'a> {
    /// Produce a flat, collision-free identifier for a Charon path.
    /// Concatenates every `PeIdent` with `_`, prepends `impl_` for
    /// every `PeImpl`. Loses the original casing but works for the
    /// Phase 4 demonstration target (rustc-parseable Rust).
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
        if parts.len() <= 2 {
            return parts.last().cloned().unwrap_or_else(|| format!("anon_{def_id}"));
        }
        let joined = parts.join("_");
        if had_impl {
            format!("impl_{joined}_{def_id}")
        } else {
            // Multi-segment paths get disambiguated by def_id to be
            // safe across crate-internal name reuse.
            format!("{joined}_{def_id}")
        }
    }

    fn type_decl_name(&self, id: u64) -> String {
        match self.type_decls.get(&id) {
            Some(td) => Self::flat_path_ident(&td.item_meta.name, td.def_id),
            None => format!("UnknownType{id}"),
        }
    }

    fn fun_decl_name(&self, id: u64, loop_marker: Option<u64>) -> Option<String> {
        self.fun_decls.get(&(id, loop_marker)).map(|f| {
            let base = Self::flat_path_ident(&f.item_meta.name, f.def_id);
            match &f.loop_id {
                Some(lm) => format!("{base}_loop{}", lm.loop_id),
                None => base,
            }
        })
    }

    fn type_decl(&self, id: u64) -> Option<&TypeDecl> {
        self.type_decls.get(&id).copied()
    }

    fn variant_name(&self, adt_id: u64, variant_id: Option<u64>) -> String {
        if let Some(td) = self.type_decl(adt_id) {
            if let TypeDeclKind::Enum(variants) = &td.kind {
                if let Some(vid) = variant_id {
                    if let Some(v) = variants.get(vid as usize) {
                        return v.variant_name.clone();
                    }
                }
            }
        }
        match variant_id {
            Some(v) => format!("V{v}"),
            None => "Default".to_string(),
        }
    }
}

// ---------- binder context (for resolving BVar de-Bruijn refs) ----------

/// One scope of binders: each entry is the chosen Rust identifier for
/// the binder's `id`-th pattern element. Scopes are pushed on entry to
/// a `Lambda` / `Let` / match-arm / `Loop` body and popped on exit.
#[derive(Default)]
struct BinderCtx {
    /// Stack: innermost scope at the back. Each scope is a `Vec` of
    /// names indexed by binder id.
    scopes: Vec<Vec<String>>,
    fresh_counter: u32,
}

impl BinderCtx {
    fn push(&mut self, names: Vec<String>) {
        self.scopes.push(names);
    }
    fn pop(&mut self) {
        self.scopes.pop();
    }
    fn resolve(&self, scope: i64, id: u64) -> String {
        // Pure IR uses 0-indexed `scope` counting *outward* from the
        // current binder. So scope 0 = innermost (top of stack).
        let depth = self.scopes.len();
        if depth == 0 {
            return format!("__b{scope}_{id}");
        }
        let idx_from_top = scope as usize;
        if idx_from_top >= depth {
            return format!("__b{scope}_{id}");
        }
        let scope_idx = depth - 1 - idx_from_top;
        match self.scopes[scope_idx].get(id as usize) {
            Some(name) => name.clone(),
            None => format!("__b{scope}_{id}"),
        }
    }
    fn fresh(&mut self, hint: Option<&str>) -> String {
        let n = self.fresh_counter;
        self.fresh_counter += 1;
        match hint {
            Some(h) if !h.is_empty() => sanitize_ident(&format!("{h}_{n}")),
            _ => format!("v{n}"),
        }
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
    if RUST_KEYWORDS.contains(&out.as_str()) {
        out.push('_');
    }
    out
}

const RUST_KEYWORDS: &[&str] = &[
    "as", "break", "const", "continue", "crate", "else", "enum", "extern",
    "false", "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod",
    "move", "mut", "pub", "ref", "return", "self", "Self", "static", "struct",
    "super", "trait", "true", "type", "unsafe", "use", "where", "while",
    "async", "await", "dyn", "abstract", "become", "box", "do", "final",
    "macro", "override", "priv", "try", "typeof", "unsized", "virtual",
    "yield",
];

// ---------- type-decl emission ----------

fn emit_type_decl(td: &TypeDecl, ctx: &EmitCtx, gctx: &GenCtx, out: &mut String) {
    let name = EmitCtx::flat_path_ident(&td.item_meta.name, td.def_id);
    let generics = emit_generic_params(&td.generics);
    match &td.kind {
        TypeDeclKind::Struct(fields) => {
            // Tuple struct if no field names; otherwise record struct.
            let any_named = fields.iter().any(|f| f.field_name.is_some());
            if fields.is_empty() {
                let _ = writeln!(out, "pub struct {name}{generics};");
            } else if any_named {
                let _ = writeln!(out, "pub struct {name}{generics} {{");
                for (i, f) in fields.iter().enumerate() {
                    let fname = f
                        .field_name
                        .clone()
                        .unwrap_or_else(|| format!("f{i}"));
                    let _ = writeln!(
                        out,
                        "    pub {}: {},",
                        sanitize_ident(&fname),
                        ty_to_rust(&f.field_ty, ctx, gctx)
                    );
                }
                out.push_str("}\n");
            } else {
                let mut tys = Vec::with_capacity(fields.len());
                for f in fields {
                    tys.push(ty_to_rust(&f.field_ty, ctx, gctx));
                }
                let _ =
                    writeln!(out, "pub struct {name}{generics}({});", tys.join(", "));
            }
        }
        TypeDeclKind::Enum(variants) => {
            let _ = writeln!(out, "pub enum {name}{generics} {{");
            for v in variants {
                if v.fields.is_empty() {
                    let _ = writeln!(out, "    {},", sanitize_ident(&v.variant_name));
                } else {
                    let any_named = v.fields.iter().any(|f| f.field_name.is_some());
                    if any_named {
                        let _ = writeln!(out, "    {} {{", sanitize_ident(&v.variant_name));
                        for (i, f) in v.fields.iter().enumerate() {
                            let fname = f
                                .field_name
                                .clone()
                                .unwrap_or_else(|| format!("f{i}"));
                            let _ = writeln!(
                                out,
                                "        {}: {},",
                                sanitize_ident(&fname),
                                ty_to_rust(&f.field_ty, ctx, gctx)
                            );
                        }
                        out.push_str("    },\n");
                    } else {
                        let mut tys = Vec::with_capacity(v.fields.len());
                        for f in &v.fields {
                            tys.push(ty_to_rust(&f.field_ty, ctx, gctx));
                        }
                        let _ = writeln!(
                            out,
                            "    {}({}),",
                            sanitize_ident(&v.variant_name),
                            tys.join(", ")
                        );
                    }
                }
            }
            out.push_str("}\n");
        }
        TypeDeclKind::Opaque => {
            let _ = writeln!(
                out,
                "// TODO: opaque type {name} — emitting marker struct.\npub struct {name}{generics};"
            );
        }
    }
}

fn emit_generic_params(g: &GenericParams) -> String {
    if g.types.is_empty() && g.const_generics.is_empty() {
        return String::new();
    }
    let mut parts = Vec::new();
    for t in &g.types {
        parts.push(sanitize_ident(&t.name));
    }
    for c in &g.const_generics {
        parts.push(format!(
            "const {}: {}",
            sanitize_ident(&c.name),
            literal_type_to_rust(&c.ty)
        ));
    }
    format!("<{}>", parts.join(", "))
}

// ---------- type emission ----------

fn ty_to_rust(ty: &Ty, ctx: &EmitCtx, gctx: &GenCtx) -> String {
    match ty {
        Ty::TLiteral(lt) => literal_type_to_rust(lt),
        Ty::TArrow(a) => {
            // Function type → render as `impl Fn(_) -> _`. This is rare
            // in the fixtures we target; closures show up as `Lambda`
            // expressions whose surrounding context typically asks for
            // a concrete shape.
            format!(
                "impl Fn({}) -> {}",
                ty_to_rust(&a.input, ctx, gctx),
                ty_to_rust(&a.output, ctx, gctx)
            )
        }
        Ty::TAdt(a) => adt_to_rust(a, ctx, gctx),
        Ty::TVar(v) => match v {
            DeBruijnVar::Bound(b) => gctx.type_var(b.value),
            DeBruijnVar::Free(id) => gctx.type_var(*id),
        },
        Ty::TTraitType(_) => "/* TODO: TTraitType */ ()".to_string(),
        Ty::TNever => "!".to_string(),
        Ty::TDynTrait(_) => "/* TODO: dyn Trait */ ()".to_string(),
        Ty::TError => "/* TError */ ()".to_string(),
    }
}

fn adt_to_rust(a: &TAdt, ctx: &EmitCtx, gctx: &GenCtx) -> String {
    match &a.type_id {
        TypeId::TTuple => {
            let parts: Vec<String> = a
                .generics
                .types
                .iter()
                .map(|t| ty_to_rust(t, ctx, gctx))
                .collect();
            match parts.len() {
                0 => "()".to_string(),
                1 => format!("({},)", parts[0]),
                _ => format!("({})", parts.join(", ")),
            }
        }
        TypeId::TBuiltin(b) => match b {
            BuiltinTy::TResult => {
                let inner = a
                    .generics
                    .types
                    .first()
                    .map(|t| ty_to_rust(t, ctx, gctx))
                    .unwrap_or_else(|| "()".to_string());
                format!("Result<{inner}>")
            }
            BuiltinTy::TArray => {
                let elem = a
                    .generics
                    .types
                    .first()
                    .map(|t| ty_to_rust(t, ctx, gctx))
                    .unwrap_or_else(|| "()".to_string());
                let len = a
                    .generics
                    .const_generics
                    .first()
                    .map(|c| const_generic_to_rust(c, gctx))
                    .unwrap_or_else(|| "1".to_string());
                format!("[{elem}; {len}]")
            }
            BuiltinTy::TSlice => {
                let elem = a
                    .generics
                    .types
                    .first()
                    .map(|t| ty_to_rust(t, ctx, gctx))
                    .unwrap_or_else(|| "()".to_string());
                // Slices need a borrow in Rust; we emit a Vec-like
                // owned shape as a closest IR-faithful render.
                format!("Vec<{elem}>")
            }
            BuiltinTy::TStr => "&'static str".to_string(),
            BuiltinTy::TSum => {
                let a_ = a.generics.types.first().map(|t| ty_to_rust(t, ctx, gctx));
                let b_ = a.generics.types.get(1).map(|t| ty_to_rust(t, ctx, gctx));
                format!(
                    "core::result::Result<{}, {}>",
                    a_.unwrap_or_else(|| "()".to_string()),
                    b_.unwrap_or_else(|| "()".to_string()),
                )
            }
            BuiltinTy::TLoopResult => {
                let inner = a
                    .generics
                    .types
                    .first()
                    .map(|t| ty_to_rust(t, ctx, gctx))
                    .unwrap_or_else(|| "()".to_string());
                // We model LoopResult as just its inner type — the
                // distinction matters in the IR but not at the Rust
                // type level for our parseability target.
                inner
            }
            BuiltinTy::TError => "()".to_string(),
            BuiltinTy::TFuel => "u64".to_string(),
            BuiltinTy::TRawPtr(_) => "*const ()".to_string(),
        },
        TypeId::TAdtId(id) => {
            let name = ctx.type_decl_name(*id);
            if a.generics.types.is_empty() && a.generics.const_generics.is_empty() {
                name
            } else {
                let mut parts: Vec<String> = a
                    .generics
                    .types
                    .iter()
                    .map(|t| ty_to_rust(t, ctx, gctx))
                    .collect();
                for c in &a.generics.const_generics {
                    parts.push(const_generic_to_rust(c, gctx));
                }
                format!("{name}<{}>", parts.join(", "))
            }
        }
    }
}

fn literal_type_to_rust(lt: &LiteralType) -> String {
    match lt {
        LiteralType::TInt(it) => match it {
            IntTy::Isize => "isize",
            IntTy::I8 => "i8",
            IntTy::I16 => "i16",
            IntTy::I32 => "i32",
            IntTy::I64 => "i64",
            IntTy::I128 => "i128",
        }
        .to_string(),
        LiteralType::TUInt(ut) => match ut {
            UIntTy::Usize => "usize",
            UIntTy::U8 => "u8",
            UIntTy::U16 => "u16",
            UIntTy::U32 => "u32",
            UIntTy::U64 => "u64",
            UIntTy::U128 => "u128",
        }
        .to_string(),
        LiteralType::TFloat(ft) => match ft {
            FloatTy::F16 => "/* f16 */ f32",
            FloatTy::F32 => "f32",
            FloatTy::F64 => "f64",
            FloatTy::F128 => "/* f128 */ f64",
        }
        .to_string(),
        LiteralType::TBool => "bool".to_string(),
        LiteralType::TChar => "char".to_string(),
        LiteralType::TPureNat => "u128 /* PureNat */".to_string(),
        LiteralType::TPureInt => "i128 /* PureInt */".to_string(),
    }
}

fn const_generic_to_rust(c: &ConstGeneric, gctx: &GenCtx) -> String {
    match c {
        ConstGeneric::CgGlobal(id) => format!("/* global {id} */ 0"),
        ConstGeneric::CgVar(v) => match v {
            DeBruijnVar::Bound(b) => gctx.const_var(b.value),
            DeBruijnVar::Free(id) => gctx.const_var(*id),
        },
        ConstGeneric::CgValue(lit) => literal_to_rust(lit),
    }
}

// ---------- function-decl emission ----------

fn emit_fun_decl(fd: &FunDecl, ctx: &EmitCtx, gctx: &GenCtx, out: &mut String) {
    let base =
        sanitize_ident(&EmitCtx::flat_path_ident(&fd.item_meta.name, fd.def_id));
    let name = match &fd.loop_id {
        Some(lm) => format!("{base}_loop{}", lm.loop_id),
        None => base,
    };
    let generics = emit_generic_params(&fd.signature.generics);

    let input_pats: Vec<&TPat> = match &fd.body {
        Some(b) => b.inputs.iter().collect(),
        None => Vec::new(),
    };

    // Build the parameter list. If a body exists we use its named
    // patterns; otherwise just use positional `p<i>` against the sig.
    let mut params = Vec::new();
    let mut bound_input_names = Vec::new();
    for (i, in_ty) in fd.signature.inputs.iter().enumerate() {
        let (param_name, _bound) = match input_pats.get(i) {
            Some(tp) => pattern_param_name(&tp.pat, i),
            None => (format!("p{i}"), false),
        };
        bound_input_names.push(param_name.clone());
        params.push(format!("{}: {}", param_name, ty_to_rust(in_ty, ctx, gctx)));
    }

    let ret_ty = ty_to_rust(&fd.signature.output, ctx, gctx);

    let _ = writeln!(
        out,
        "pub fn {name}{generics}({}) -> {ret_ty} {{",
        params.join(", ")
    );

    match &fd.body {
        Some(body) => {
            let mut binders = BinderCtx::default();
            binders.push(bound_input_names);

            let mut body_buf = String::new();
            emit_expr(&body.body, ctx, gctx, &mut binders, 1, &mut body_buf);
            out.push_str(&body_buf);
            if !body_buf.ends_with('\n') {
                out.push('\n');
            }
        }
        None => {
            out.push_str("    unimplemented!(\"opaque body\")\n");
        }
    }
    out.push_str("}\n");
}

/// Return the param name to use for a top-level input pattern.
fn pattern_param_name(p: &Pat, idx: usize) -> (String, bool) {
    match p {
        Pat::PBound(b) => {
            let n = b
                .var
                .basename
                .clone()
                .unwrap_or_else(|| format!("p{idx}"));
            (sanitize_ident(&n), true)
        }
        Pat::POpen(o) => {
            let n = o
                .fvar
                .basename
                .clone()
                .unwrap_or_else(|| format!("p{idx}"));
            (sanitize_ident(&n), true)
        }
        Pat::PIgnored => (format!("_p{idx}"), false),
        _ => (format!("p{idx}"), false),
    }
}

// ---------- expression emission ----------

/// Emit `texpr` at indentation `indent` (in 4-space units).
fn emit_expr(
    texpr: &TExpr,
    ctx: &EmitCtx,
    gctx: &GenCtx,
    binders: &mut BinderCtx,
    indent: usize,
    out: &mut String,
) {
    // Detect a `Let`-cascade and emit it as a sequence of statements
    // ending with the last expression. We do this iteratively so deep
    // `Let` chains don't blow the call stack.
    let mut cur = texpr;
    let mut pushed_scopes = 0usize;
    loop {
        // Unwrap Meta wrappers — we don't carry them through.
        let e = unwrap_meta(cur);
        match &e.e {
            Expr::Let(payload) => {
                let pad = "    ".repeat(indent);
                let bound_ty = ty_to_rust(&payload.pat.ty, ctx, gctx);

                // The Let pattern may be a single binder (PBound /
                // POpen) or a tuple destructure (PAdt with TTuple
                // type-id). Both shapes are handled here so the binder
                // scope gets the correct number of names.
                let (pat_rendered, scope_names) = let_pattern(
                    &payload.pat,
                    binders,
                );

                let bound_expr = expr_to_string(&payload.bound, ctx, gctx, binders);
                let q = if payload.monadic { "?" } else { "" };
                let _ = writeln!(
                    out,
                    "{pad}let {pat_rendered}: {bound_ty} = {bound_expr}{q};"
                );

                // Push a new scope for the binders introduced by the
                // pattern. Even a wildcard pattern is treated as a
                // single (unused) binder so id 0 still resolves.
                binders.push(scope_names);
                pushed_scopes += 1;
                cur = &payload.body;
            }
            _ => break,
        }
    }

    // Final expression — render inline, return-position.
    let pad = "    ".repeat(indent);
    let final_e = unwrap_meta(cur);
    let s = expr_to_string(final_e, ctx, gctx, binders);
    let _ = writeln!(out, "{pad}{s}");

    // Pop binder scopes we pushed for the lets above.
    for _ in 0..pushed_scopes {
        binders.pop();
    }
}

/// Render the LHS of a `let` and return the list of binder names
/// introduced (id-indexed) for `BVar` resolution. Single-binder
/// patterns yield `let x: ...`; tuple destructures yield
/// `let (a, b): ...`. ADT patterns we can't render cleanly fall back
/// to a fresh name + `// TODO`.
fn let_pattern(tp: &TPat, binders: &mut BinderCtx) -> (String, Vec<String>) {
    match &tp.pat {
        Pat::PBound(b) => {
            let n = b
                .var
                .basename
                .clone()
                .unwrap_or_else(|| binders.fresh(None));
            let sn = sanitize_ident(&n);
            (sn.clone(), vec![sn])
        }
        Pat::POpen(o) => {
            let n = o
                .fvar
                .basename
                .clone()
                .unwrap_or_else(|| binders.fresh(None));
            let sn = sanitize_ident(&n);
            (sn.clone(), vec![sn])
        }
        Pat::PAdt(adt) => {
            // Treat any zero-variant ADT as a positional tuple
            // destructure; we only do this for actual tuples (the
            // common case from loop output destructuring). Other ADTs
            // get a wildcard + a fresh binder name (loses the IR's
            // structural intent but keeps the output parseable).
            let is_tuple_like =
                matches!(&tp.ty, Ty::TAdt(a) if matches!(a.type_id, TypeId::TTuple));
            if is_tuple_like {
                let mut names = Vec::with_capacity(adt.fields.len());
                for f in &adt.fields {
                    let (_, sub) = let_pattern(f, binders);
                    let n = sub.first().cloned().unwrap_or_else(|| binders.fresh(None));
                    names.push(n);
                }
                (format!("({})", names.join(", ")), names)
            } else {
                // Conservative fallback: bind to a fresh name with
                // `_` LHS — pad scope_names so id 0 resolves to it.
                let n = binders.fresh(Some("adt"));
                (n.clone(), vec![n])
            }
        }
        Pat::PIgnored | Pat::PConstant(_) => {
            let n = binders.fresh(None);
            (n.clone(), vec![n])
        }
    }
}

/// Convert any expression to a single inline Rust string. Multi-line
/// constructs (matches, recursive helpers) are wrapped in a block so
/// the caller can splice them at expression position.
fn expr_to_string(
    texpr: &TExpr,
    ctx: &EmitCtx,
    gctx: &GenCtx,
    binders: &mut BinderCtx,
) -> String {
    let e = unwrap_meta(texpr);
    match &e.e {
        Expr::FVar(id) => format!("v{id}"),
        Expr::BVar(b) => binders.resolve(b.scope, b.id),
        Expr::CVar(id) => format!("__cvar_{id}"),
        Expr::Const(lit) => literal_to_rust(lit),
        Expr::App(_) => emit_app(e, ctx, gctx, binders),
        Expr::Qualif(q) => emit_qualif_standalone(q, &e.ty, ctx, gctx, binders),
        Expr::Lambda(p) => emit_lambda(p, ctx, gctx, binders),
        Expr::Let(_) => emit_let_block(e, ctx, gctx, binders),
        Expr::Switch(s) => emit_switch(s, &e.ty, ctx, gctx, binders),
        Expr::Loop(l) => emit_loop(l, &e.ty, ctx, gctx, binders),
        Expr::StructUpdate(su) => emit_struct_update(su, ctx, gctx, binders),
        Expr::Meta(_) => unreachable!("Meta wrappers stripped by unwrap_meta"),
        Expr::EError(payload) => {
            let m = payload.message.replace('"', "\\\"");
            format!("panic!(\"EError: {m}\")")
        }
    }
}

/// Walk an `Expr::Let` cascade as a block. Used when a `let` shows up
/// at expression position (e.g. as the body of a match arm).
fn emit_let_block(
    texpr: &TExpr,
    ctx: &EmitCtx,
    gctx: &GenCtx,
    binders: &mut BinderCtx,
) -> String {
    let mut buf = String::from("{\n");
    emit_expr(texpr, ctx, gctx, binders, 1, &mut buf);
    buf.push('}');
    buf
}

fn unwrap_meta(mut texpr: &TExpr) -> &TExpr {
    while let Expr::Meta(m) = &texpr.e {
        texpr = &m.expr;
    }
    texpr
}

/// `Expr::App`: collapse a left-nested chain of `App` nodes into a
/// single call: `f a b c` ← `App (App (App f a) b) c`.
fn emit_app(
    texpr: &TExpr,
    ctx: &EmitCtx,
    gctx: &GenCtx,
    binders: &mut BinderCtx,
) -> String {
    let mut args: Vec<&TExpr> = Vec::new();
    let mut cur = texpr;
    loop {
        let e = unwrap_meta(cur);
        match &e.e {
            Expr::App(app) => {
                args.push(&app.arg);
                cur = &app.fun_;
            }
            _ => break,
        }
    }
    args.reverse();
    let head = unwrap_meta(cur);

    // If head is a Qualif, dispatch on the kind for proper rendering.
    if let Expr::Qualif(q) = &head.e {
        return emit_qualif_apply(q, &args, ctx, gctx, binders);
    }

    let head_s = expr_to_string(head, ctx, gctx, binders);
    let args_s: Vec<String> = args
        .iter()
        .map(|a| expr_to_string(a, ctx, gctx, binders))
        .collect();
    format!("({}({}))", head_s, args_s.join(", "))
}

/// Render a `Qualif` that appears at the head of an `App` chain, with
/// its argument list. The argument list may be empty (zero-arg ctor /
/// global / projection).
fn emit_qualif_apply(
    q: &Qualif,
    args: &[&TExpr],
    ctx: &EmitCtx,
    gctx: &GenCtx,
    binders: &mut BinderCtx,
) -> String {
    let args_s: Vec<String> = args
        .iter()
        .map(|a| expr_to_string(a, ctx, gctx, binders))
        .collect();

    match &q.id {
        QualifId::FunOrOp(FunOrOpId::Binop(op)) => emit_binop(op, &args_s),
        QualifId::FunOrOp(FunOrOpId::Unop(op)) => emit_unop(op, &args_s),
        QualifId::FunOrOp(FunOrOpId::Fun(fid)) => {
            emit_fun_call(fid, &args_s, &q.generics, ctx)
        }
        QualifId::Global(_id) => {
            // No global decls in our targeted fixtures yet.
            "/* TODO: Global */ Default::default()".to_string()
        }
        QualifId::AdtCons(cons) => emit_adt_cons(cons, &args_s, &q.generics, ctx),
        QualifId::Proj(p) => emit_projection(p, &args_s, ctx),
        QualifId::ScalarValProj(_) => {
            if args_s.is_empty() {
                "0".to_string()
            } else {
                format!("({} as _)", args_s[0])
            }
        }
        QualifId::TraitConst(_) => "/* TODO: TraitConst */ Default::default()".to_string(),
        QualifId::MkDynTrait(_) => "/* TODO: MkDynTrait */ Default::default()".to_string(),
        QualifId::LoopOp => {
            // `LoopOp` is the loop fixed-point combinator: it takes a
            // body closure and an initial value, and returns the
            // converged result. We rely on the runtime shim emitted
            // in PRELUDE so the surrounding code typechecks.
            format!("(self::aeneas_runtime::loop_op({}))", args_s.join(", "))
        }
    }
}

fn emit_qualif_standalone(
    q: &Qualif,
    _ty: &Ty,
    ctx: &EmitCtx,
    gctx: &GenCtx,
    _binders: &mut BinderCtx,
) -> String {
    // Zero-arg variant: re-use the apply path with an empty arg list.
    emit_qualif_apply(q, &[], ctx, gctx, _binders)
}

fn emit_binop(op: &Binop, args: &[String]) -> String {
    let (lhs, rhs) = match args {
        [a, b] => (a.as_str(), b.as_str()),
        _ => return format!("/* binop wrong arity */ {}", args.join(",")),
    };
    // Symmetric arithmetic: emit `Result<T>`-returning helpers when the
    // op is OPanic so the surrounding `?` (monadic Let) typechecks.
    // OCaml's symbolic-to-pure encodes the overflow check into the
    // monad — we mirror that here with the closest stdlib match.
    let sym = match op {
        Binop::BitXor(_) => "^",
        Binop::BitAnd(_) => "&",
        Binop::BitOr(_) => "|",
        Binop::Eq(_) => "==",
        Binop::Ne(_) => "!=",
        Binop::Lt(_) => "<",
        Binop::Le(_) => "<=",
        Binop::Ge(_) => ">=",
        Binop::Gt(_) => ">",
        Binop::Add(b) => return checked_arith("checked_add", lhs, rhs, &b.overflow_mode),
        Binop::Sub(b) => return checked_arith("checked_sub", lhs, rhs, &b.overflow_mode),
        Binop::Mul(b) => return checked_arith("checked_mul", lhs, rhs, &b.overflow_mode),
        Binop::Div(b) => return checked_arith("checked_div", lhs, rhs, &b.overflow_mode),
        Binop::Rem(b) => return checked_arith("checked_rem", lhs, rhs, &b.overflow_mode),
        Binop::AddChecked(_) => {
            return format!("({lhs}.checked_add({rhs}).ok_or(()))");
        }
        Binop::SubChecked(_) => {
            return format!("({lhs}.checked_sub({rhs}).ok_or(()))");
        }
        Binop::MulChecked(_) => {
            return format!("({lhs}.checked_mul({rhs}).ok_or(()))");
        }
        Binop::Shl(b) => return checked_arith("checked_shl", lhs, rhs, &b.overflow_mode),
        Binop::Shr(b) => return checked_arith("checked_shr", lhs, rhs, &b.overflow_mode),
        Binop::Cmp(_) => return format!("(({} as i64).cmp(&({} as i64)))", lhs, rhs),
        Binop::BoolOr => "||",
    };
    format!("({} {} {})", lhs, sym, rhs)
}

fn checked_arith(method: &str, lhs: &str, rhs: &str, mode: &OverflowMode) -> String {
    // For Shl / Shr the stdlib's `checked_shl` takes a `u32` shift
    // amount; the IR sometimes passes a wider integer. We coerce.
    let rhs_cast = if method == "checked_shl" || method == "checked_shr" {
        format!("({rhs}) as u32")
    } else {
        rhs.to_string()
    };
    match mode {
        OverflowMode::OPanic | OverflowMode::OUB => {
            format!("({lhs}.{method}({rhs_cast}).ok_or(()))")
        }
        OverflowMode::OWrap => {
            let wrap = method.replace("checked_", "wrapping_");
            format!("({lhs}.{wrap}({rhs_cast}))")
        }
    }
}

fn emit_unop(op: &Unop, args: &[String]) -> String {
    let a = args.first().map(|s| s.as_str()).unwrap_or("()");
    match op {
        Unop::Not(_) => format!("(!{a})"),
        Unop::Neg(_) => format!("(-({a}))"),
        Unop::Cast(c) => match c {
            CastKind::CastLit(cl) => {
                format!("({a} as {})", literal_type_to_rust(&cl.dst))
            }
            CastKind::CastRawPtr(_) => format!("/* raw ptr cast */ {a}"),
        },
        Unop::ArrayToSlice => format!("(&{a}[..])"),
    }
}

fn emit_fun_call(
    fid: &FunId,
    args: &[String],
    _generics: &GenericArgs,
    ctx: &EmitCtx,
) -> String {
    match fid {
        FunId::FromLlbc(reg) => match &reg.kind {
            FnPtrKind::FunId(LlbcFunId::FRegular(id)) => {
                // FunDecls share `def_id` between the entry decl and
                // its loop-body decls; disambiguate using the call
                // site's `loop_` marker.
                let lm = reg.loop_.as_ref().map(|l| l.loop_id);
                let n = ctx
                    .fun_decl_name(*id, lm)
                    .or_else(|| ctx.fun_decl_name(*id, None))
                    .unwrap_or_else(|| format!("__fn_{id}"));
                format!("({n}({}))", args.join(", "))
            }
            FnPtrKind::FunId(LlbcFunId::FBuiltin) => {
                format!("/* TODO: FBuiltin */ ({})", args.join(", "))
            }
            FnPtrKind::TraitMethod(tm) => {
                let _ = tm;
                format!("/* TODO: TraitMethod */ ({})", args.join(", "))
            }
        },
        FunId::Pure(p) => emit_pure_builtin(p, args),
    }
}

fn emit_pure_builtin(p: &PureBuiltinFunId, args: &[String]) -> String {
    use PureBuiltinFunId::*;
    let inner = args.join(", ");
    match p {
        Return => format!("Ok({inner})"),
        Fail => "Err(())".to_string(),
        Assert => format!("(if {inner} {{ Ok(()) }} else {{ Err(()) }})"),
        ToResult => format!("Ok({inner})"),
        Loop(_) | RecLoopCall(_) => format!("/* loop helper */ ({inner})"),
        FuelDecrease => format!("({inner}.saturating_sub(1))"),
        FuelEqZero => format!("({inner} == 0)"),
        UpdateAtIndex(_) => format!("/* update_at_index */ ({inner})"),
        Discriminant => format!("/* discriminant */ ({inner})"),
        ResultUnwrapMut => format!("/* unwrap_mut */ ({inner})"),
        GetTarget => format!("/* get_target */ ({inner})"),
    }
}

fn emit_adt_cons(
    cons: &AdtConsId,
    args: &[String],
    _generics: &GenericArgs,
    ctx: &EmitCtx,
) -> String {
    match &cons.adt_id {
        TypeId::TBuiltin(BuiltinTy::TResult) => {
            // Variant 0 = Ok, 1 = Err in the OCaml encoding.
            match cons.variant_id {
                Some(0) => format!("Ok({})", args.join(", ")),
                Some(1) => "Err(())".to_string(),
                _ => format!("Ok({})", args.join(", ")),
            }
        }
        TypeId::TBuiltin(BuiltinTy::TLoopResult) => {
            // Two variants: continue / break. We collapse to the raw
            // inner value at the Rust level (we modelled LoopResult as
            // identity in `ty_to_rust`).
            args.join(", ")
        }
        TypeId::TBuiltin(_) => args.join(", "),
        TypeId::TTuple => {
            if args.is_empty() {
                "()".to_string()
            } else if args.len() == 1 {
                format!("({},)", args[0])
            } else {
                format!("({})", args.join(", "))
            }
        }
        TypeId::TAdtId(id) => {
            let tname = ctx.type_decl_name(*id);
            // Determine if struct / enum variant.
            let td = ctx.type_decl(*id);
            match (td, cons.variant_id) {
                (Some(td), Some(vid)) => {
                    let vname = ctx.variant_name(*id, Some(vid));
                    // Figure out whether the variant is unit / tuple /
                    // record based on the type-decl.
                    if let TypeDeclKind::Enum(variants) = &td.kind {
                        if let Some(v) = variants.get(vid as usize) {
                            let any_named =
                                v.fields.iter().any(|f| f.field_name.is_some());
                            if v.fields.is_empty() {
                                return format!("{tname}::{vname}");
                            } else if any_named {
                                let mut parts = Vec::new();
                                for (i, f) in v.fields.iter().enumerate() {
                                    let fname = f
                                        .field_name
                                        .clone()
                                        .unwrap_or_else(|| format!("f{i}"));
                                    let av = args
                                        .get(i)
                                        .cloned()
                                        .unwrap_or_else(|| "()".to_string());
                                    parts
                                        .push(format!("{}: {}", sanitize_ident(&fname), av));
                                }
                                return format!("{tname}::{vname} {{ {} }}", parts.join(", "));
                            } else {
                                return format!(
                                    "{tname}::{vname}({})",
                                    args.join(", ")
                                );
                            }
                        }
                    }
                    format!("{tname}::{vname}({})", args.join(", "))
                }
                (Some(td), None) => {
                    // Struct constructor.
                    if let TypeDeclKind::Struct(fields) = &td.kind {
                        let any_named =
                            fields.iter().any(|f| f.field_name.is_some());
                        if fields.is_empty() {
                            return tname;
                        } else if any_named {
                            let mut parts = Vec::new();
                            for (i, f) in fields.iter().enumerate() {
                                let fname = f
                                    .field_name
                                    .clone()
                                    .unwrap_or_else(|| format!("f{i}"));
                                let av = args
                                    .get(i)
                                    .cloned()
                                    .unwrap_or_else(|| "Default::default()".to_string());
                                parts
                                    .push(format!("{}: {}", sanitize_ident(&fname), av));
                            }
                            return format!("{tname} {{ {} }}", parts.join(", "));
                        } else {
                            return format!("{tname}({})", args.join(", "));
                        }
                    }
                    tname
                }
                _ => format!("{tname}({})", args.join(", ")),
            }
        }
    }
}

fn emit_projection(p: &Projection, args: &[String], ctx: &EmitCtx) -> String {
    let recv = args
        .first()
        .cloned()
        .unwrap_or_else(|| "/* no recv */ ()".to_string());
    match &p.adt_id {
        TypeId::TTuple => format!("{recv}.{}", p.field_id),
        TypeId::TBuiltin(_) => format!("/* builtin proj */ {recv}.{}", p.field_id),
        TypeId::TAdtId(id) => {
            let td = ctx.type_decl(*id);
            if let Some(td) = td {
                if let TypeDeclKind::Struct(fields) = &td.kind {
                    if let Some(f) = fields.get(p.field_id as usize) {
                        if let Some(fname) = &f.field_name {
                            return format!("{recv}.{}", sanitize_ident(fname));
                        }
                    }
                }
            }
            format!("{recv}.{}", p.field_id)
        }
    }
}

fn emit_lambda(
    p: &LambdaPayload,
    ctx: &EmitCtx,
    gctx: &GenCtx,
    binders: &mut BinderCtx,
) -> String {
    let name = match pat_param(&p.pat.pat) {
        Some(n) => sanitize_ident(&n),
        None => binders.fresh(None),
    };
    let ty = ty_to_rust(&p.pat.ty, ctx, gctx);
    binders.push(vec![name.clone()]);
    let body = expr_to_string(&p.body, ctx, gctx, binders);
    binders.pop();
    format!("(move |{name}: {ty}| {body})")
}

fn emit_switch(
    s: &SwitchPayload,
    _ty: &Ty,
    ctx: &EmitCtx,
    gctx: &GenCtx,
    binders: &mut BinderCtx,
) -> String {
    let scrut = expr_to_string(&s.scrutinee, ctx, gctx, binders);
    match &s.body {
        SwitchBody::If(payload) => {
            let t = expr_to_string(&payload.then_branch, ctx, gctx, binders);
            let e = expr_to_string(&payload.else_branch, ctx, gctx, binders);
            format!("(if {scrut} {{ {t} }} else {{ {e} }})")
        }
        SwitchBody::Match(arms) => {
            // Aeneas Match arms enumerate every variant of the
            // scrutinee's ADT. We need parent-type info to render
            // each `PAdt` arm with the right variant name. Look at
            // the scrutinee's type once and pass it down.
            let scrut_adt_id = match &s.scrutinee.ty {
                Ty::TAdt(a) => match &a.type_id {
                    TypeId::TAdtId(id) => Some(*id),
                    _ => None,
                },
                _ => None,
            };
            let mut buf = String::from("match ");
            buf.push_str(&scrut);
            buf.push_str(" {\n");
            for arm in arms {
                let (pat_s, pat_binders) =
                    pattern_to_rust(&arm.pat.pat, scrut_adt_id, ctx);
                binders.push(pat_binders);
                let body = expr_to_string(&arm.branch, ctx, gctx, binders);
                binders.pop();
                let _ = writeln!(buf, "    {pat_s} => {body},");
            }
            buf.push('}');
            buf
        }
    }
}

/// Render a pattern as a Rust pattern + the list of binder names it
/// introduces. The names are returned in IR id order so the caller
/// can push them as a scope for `BVar` resolution. `scrut_adt_id` is
/// the type-decl id of the surrounding match's scrutinee, used to
/// resolve enum variant names; `None` falls back to wildcard.
fn pattern_to_rust(
    p: &Pat,
    scrut_adt_id: Option<u64>,
    ctx: &EmitCtx,
) -> (String, Vec<String>) {
    match p {
        Pat::PConstant(lit) => (literal_to_rust(lit), Vec::new()),
        Pat::PIgnored => ("_".to_string(), Vec::new()),
        Pat::PBound(b) => {
            let n = b
                .var
                .basename
                .clone()
                .unwrap_or_else(|| "_x".to_string());
            let sn = sanitize_ident(&n);
            (sn.clone(), vec![sn])
        }
        Pat::POpen(o) => {
            let n = o
                .fvar
                .basename
                .clone()
                .unwrap_or_else(|| "_x".to_string());
            let sn = sanitize_ident(&n);
            (sn.clone(), vec![sn])
        }
        Pat::PAdt(adt) => pattern_adt_to_rust(adt, scrut_adt_id, ctx),
    }
}

fn pattern_adt_to_rust(
    adt: &AdtPat,
    scrut_adt_id: Option<u64>,
    ctx: &EmitCtx,
) -> (String, Vec<String>) {
    let mut sub_pats = Vec::new();
    let mut sub_binders = Vec::new();
    for f in &adt.fields {
        let (s, bs) = pattern_to_rust(&f.pat, None, ctx);
        sub_pats.push(s);
        sub_binders.extend(bs);
    }
    // If we know the parent ADT, render a proper enum-variant pattern.
    if let (Some(adt_id), Some(vid)) = (scrut_adt_id, adt.variant_id) {
        let tname = ctx.type_decl_name(adt_id);
        let vname = ctx.variant_name(adt_id, Some(vid));
        // Decide record / tuple / unit shape from the type-decl.
        if let Some(td) = ctx.type_decl(adt_id) {
            if let TypeDeclKind::Enum(variants) = &td.kind {
                if let Some(v) = variants.get(vid as usize) {
                    if v.fields.is_empty() {
                        return (format!("{tname}::{vname}"), sub_binders);
                    }
                    let any_named = v.fields.iter().any(|f| f.field_name.is_some());
                    if any_named {
                        let mut parts = Vec::new();
                        for (i, f) in v.fields.iter().enumerate() {
                            let fname = f
                                .field_name
                                .clone()
                                .unwrap_or_else(|| format!("f{i}"));
                            let pp = sub_pats
                                .get(i)
                                .cloned()
                                .unwrap_or_else(|| "_".to_string());
                            parts
                                .push(format!("{}: {}", sanitize_ident(&fname), pp));
                        }
                        return (
                            format!("{tname}::{vname} {{ {} }}", parts.join(", ")),
                            sub_binders,
                        );
                    }
                    return (
                        format!("{tname}::{vname}({})", sub_pats.join(", ")),
                        sub_binders,
                    );
                }
            }
        }
        return (format!("{tname}::{vname}"), sub_binders);
    }
    // Tuple destructure (no variant_id, no parent ADT id).
    if adt.variant_id.is_none() {
        return (format!("({})", sub_pats.join(", ")), sub_binders);
    }
    ("_".to_string(), sub_binders)
}

fn emit_loop(
    l: &Loop,
    ty: &Ty,
    ctx: &EmitCtx,
    gctx: &GenCtx,
    _binders: &mut BinderCtx,
) -> String {
    // For the MVP, `Loop` nodes (which only appear in `post-s2p`) are
    // emitted as a typed `unimplemented!` returning the right shape so
    // surrounding monadic `?` operators still typecheck. The fully
    // structural lowering happens in `post-micro`, where Aeneas
    // promotes the loop body to its own decl reachable via
    // `RecLoopCall`.
    let _ = (l, gctx);
    let rty = ty_to_rust(ty, ctx, gctx);
    format!("(unimplemented!(\"Loop\") as {rty})")
}

fn emit_struct_update(
    su: &StructUpdate,
    ctx: &EmitCtx,
    gctx: &GenCtx,
    binders: &mut BinderCtx,
) -> String {
    // Render `Name { f: v, ..init }` style if we have `init`, or
    // `Name { f: v, ... }` if not. Field names are looked up from
    // the type decl when the parent ADT is identifiable.
    let head = match &su.struct_id {
        TypeId::TAdtId(id) => ctx.type_decl_name(*id),
        TypeId::TTuple => {
            let parts: Vec<String> = su
                .updates
                .iter()
                .map(|u| expr_to_string(&u.expr, ctx, gctx, binders))
                .collect();
            return format!("({})", parts.join(", "));
        }
        TypeId::TBuiltin(_) => "/* builtin struct */".to_string(),
    };
    let mut parts = Vec::new();
    let td = if let TypeId::TAdtId(id) = &su.struct_id {
        ctx.type_decl(*id)
    } else {
        None
    };
    for u in &su.updates {
        let fname = if let Some(td) = td {
            if let TypeDeclKind::Struct(fields) = &td.kind {
                fields
                    .get(u.field_id as usize)
                    .and_then(|f| f.field_name.clone())
            } else {
                None
            }
        } else {
            None
        };
        let fname = fname.unwrap_or_else(|| format!("f{}", u.field_id));
        let val = expr_to_string(&u.expr, ctx, gctx, binders);
        parts.push(format!("{}: {}", sanitize_ident(&fname), val));
    }
    match &su.init {
        Some(init) => {
            let i = expr_to_string(init, ctx, gctx, binders);
            format!("{head} {{ {}, ..{i} }}", parts.join(", "))
        }
        None => format!("{head} {{ {} }}", parts.join(", ")),
    }
}

fn pat_param(p: &Pat) -> Option<String> {
    match p {
        Pat::PBound(b) => b.var.basename.clone(),
        Pat::POpen(o) => o.fvar.basename.clone(),
        _ => None,
    }
}

// ---------- literal emission ----------

fn literal_to_rust(lit: &Literal) -> String {
    match lit {
        Literal::VScalar(s) => {
            // The `ty` field is raw JSON of either `IntTy` or `UIntTy`.
            // We render the value with the matching Rust suffix.
            let suffix = scalar_ty_suffix(&s.ty, s.signed);
            // Negative values for signed get a leading `-`; the JSON
            // already encodes them as `value: "-7"`.
            format!("{}{}", s.value, suffix)
        }
        Literal::VFloat(f) => {
            let suf = match f.ty {
                FloatTy::F32 => "f32",
                FloatTy::F64 => "f64",
                FloatTy::F16 | FloatTy::F128 => "f64",
            };
            format!("{}{}", f.value, suf)
        }
        Literal::VBool(b) => b.to_string(),
        Literal::VChar(c) => {
            // We render as a u32 literal cast to char to dodge escaping
            // edge cases.
            format!("(char::from_u32({c}u32).unwrap_or('\\0'))")
        }
        Literal::VByteStr(bs) => {
            let parts: Vec<String> = bs.iter().map(|b| format!("{b}u8")).collect();
            format!("[{}]", parts.join(", "))
        }
        Literal::VStr(s) => {
            let escaped = s.replace('\\', "\\\\").replace('"', "\\\"");
            format!("\"{escaped}\"")
        }
        Literal::VPureNat(s) | Literal::VPureInt(s) => format!("{s}i128"),
    }
}

fn scalar_ty_suffix(ty: &serde_json::Value, signed: bool) -> &'static str {
    // The OCaml side ships either a quoted variant ("U32") or a small
    // tagged object — but in practice the goldens show bare strings.
    let s = match ty {
        serde_json::Value::String(s) => s.as_str(),
        serde_json::Value::Object(o) => o
            .get("kind")
            .and_then(|v| v.as_str())
            .unwrap_or(""),
        _ => "",
    };
    match (signed, s) {
        (false, "U8") => "u8",
        (false, "U16") => "u16",
        (false, "U32") => "u32",
        (false, "U64") => "u64",
        (false, "U128") => "u128",
        (false, "Usize") => "usize",
        (true, "I8") => "i8",
        (true, "I16") => "i16",
        (true, "I32") => "i32",
        (true, "I64") => "i64",
        (true, "I128") => "i128",
        (true, "Isize") => "isize",
        _ => "",
    }
}
