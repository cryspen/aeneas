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
#![allow(unused_variables, unused_parens, unused_mut, dead_code, non_snake_case, nonstandard_style, unused_assignments, unused_imports, unreachable_code, clippy::all)]

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

    /// Typed placeholder used wherever the emitter can't faithfully
    /// recover a concrete expression (trait-method dispatch,
    /// builtin calls, opaque globals, etc). Returns `Result<T>` so
    /// the surrounding `?` operator typechecks.
    #[inline] pub fn todo_result<T>(_what: &'static str) -> Result<T> { Err(()) }

    /// Typed placeholder for non-monadic positions.
    #[inline] pub fn todo_value<T>(what: &'static str) -> T { panic!(\"todo_value: {what}\") }
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
    /// every `PeImpl`. Always disambiguates with `def_id` because
    /// Aeneas can produce multiple decls sharing a short name (e.g.
    /// trait + impl + free fn all called `eq` / `ne` / `next` / etc).
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
        } else if parts.len() <= 2 {
            // Single-segment names get the def_id appended only when
            // the short name is reused across decls. Conservative
            // approach: always append. Yes, this makes `incr` become
            // `incr_3`, but it eliminates a whole class of collisions.
            format!("{joined}_{def_id}")
        } else {
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
    #[allow(dead_code)]
    fn fresh(&mut self, hint: Option<&str>) -> String {
        let n = self.fresh_counter;
        self.fresh_counter += 1;
        match hint {
            Some(h) if !h.is_empty() => sanitize_ident(&format!("{h}_{n}")),
            _ => format!("v{n}"),
        }
    }
    /// Like `fresh` but always uses the hint as a prefix. Used for
    /// pattern binders where the hint comes from the IR's basename and
    /// would collide if reused across sibling patterns.
    fn fresh_from_hint(&mut self, hint: &str) -> String {
        let n = self.fresh_counter;
        self.fresh_counter += 1;
        if hint.is_empty() {
            format!("v{n}")
        } else {
            sanitize_ident(&format!("{hint}_{n}"))
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
    // Self-reference detection: any field whose type transitively
    // reaches this decl's `def_id` (directly or via mutually-recursive
    // ADT references) must be boxed for the resulting Rust type to be
    // sized.
    let self_id = td.def_id;
    let field_ty = |ty: &Ty| -> String {
        let s = ty_to_rust(ty, ctx, gctx);
        if ty_transitively_references(ty, self_id, ctx) {
            format!("Box<{s}>")
        } else {
            s
        }
    };
    // We also need a "uses generics?" check — Rust complains about
    // unused type params; we inject a `PhantomData` marker field for
    // any unused params.
    let unused_type_params: Vec<String> = td
        .generics
        .types
        .iter()
        .filter_map(|t| {
            let used = match &td.kind {
                TypeDeclKind::Struct(fs) => {
                    fs.iter().any(|f| ty_uses_typaram(&f.field_ty, t.index))
                }
                TypeDeclKind::Enum(vs) => vs.iter().any(|v| {
                    v.fields
                        .iter()
                        .any(|f| ty_uses_typaram(&f.field_ty, t.index))
                }),
                TypeDeclKind::Opaque => true,
            };
            if used { None } else { Some(sanitize_ident(&t.name)) }
        })
        .collect();
    let phantom_field = if unused_type_params.is_empty() {
        String::new()
    } else {
        let inner = unused_type_params.join(", ");
        format!("    pub _ph: core::marker::PhantomData<fn() -> ({inner},)>,\n")
    };
    // No derive — too brittle to predict whether all referenced types
    // (opaque structs, FnOnce closures, etc.) implement `Clone`.
    match &td.kind {
        TypeDeclKind::Struct(fields) => {
            // Tuple struct if no field names; otherwise record struct.
            let any_named = fields.iter().any(|f| f.field_name.is_some());
            if fields.is_empty() && phantom_field.is_empty() {
                let _ = writeln!(out, "pub struct {name}{generics};");
            } else if any_named || !phantom_field.is_empty() {
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
                        field_ty(&f.field_ty)
                    );
                }
                out.push_str(&phantom_field);
                out.push_str("}\n");
            } else {
                let mut tys = Vec::with_capacity(fields.len());
                for f in fields {
                    tys.push(field_ty(&f.field_ty));
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
                                field_ty(&f.field_ty)
                            );
                        }
                        out.push_str("    },\n");
                    } else {
                        let mut tys = Vec::with_capacity(v.fields.len());
                        for f in &v.fields {
                            tys.push(field_ty(&f.field_ty));
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
            // Add a unit phantom variant if there are unused params.
            if !unused_type_params.is_empty() {
                let inner = unused_type_params.join(", ");
                let _ = writeln!(
                    out,
                    "    _PhantomData(core::marker::PhantomData<fn() -> ({inner},)>),"
                );
            }
            out.push_str("}\n");
        }
        TypeDeclKind::Opaque => {
            // Opaque types — we don't know the layout. Emit a marker
            // struct with a `PhantomData` over the type params so the
            // type-checker doesn't complain about unused generics.
            if td.generics.types.is_empty() && td.generics.const_generics.is_empty() {
                let _ = writeln!(
                    out,
                    "// TODO: opaque type {name} — emitting marker struct.\npub struct {name};"
                );
            } else {
                let typaram_list: Vec<String> = td
                    .generics
                    .types
                    .iter()
                    .map(|t| sanitize_ident(&t.name))
                    .collect();
                let phantom_inner = if typaram_list.is_empty() {
                    "()".to_string()
                } else {
                    format!("({},)", typaram_list.join(", "))
                };
                let _ = writeln!(
                    out,
                    "// TODO: opaque type {name} — emitting marker struct.\npub struct {name}{generics}(pub core::marker::PhantomData<fn() -> {phantom_inner}>);"
                );
            }
        }
    }
}

/// Emit a typed default value matching `ty` — used as the
/// expression-position fallback for `CVar`, `Global`, and `TraitConst`
/// references where we don't have the actual definition. Returns a
/// concrete-typed expression so `.checked_*` / binop receivers
/// continue to typecheck.
fn cvar_default_for_ty(ty: &Ty) -> String {
    match ty {
        Ty::TLiteral(LiteralType::TInt(it)) => {
            let s = match it {
                IntTy::Isize => "isize",
                IntTy::I8 => "i8",
                IntTy::I16 => "i16",
                IntTy::I32 => "i32",
                IntTy::I64 => "i64",
                IntTy::I128 => "i128",
            };
            format!("0{s}")
        }
        Ty::TLiteral(LiteralType::TUInt(ut)) => {
            let s = match ut {
                UIntTy::Usize => "usize",
                UIntTy::U8 => "u8",
                UIntTy::U16 => "u16",
                UIntTy::U32 => "u32",
                UIntTy::U64 => "u64",
                UIntTy::U128 => "u128",
            };
            format!("0{s}")
        }
        Ty::TLiteral(LiteralType::TBool) => "false".to_string(),
        Ty::TLiteral(LiteralType::TChar) => "'\\0'".to_string(),
        Ty::TLiteral(LiteralType::TFloat(_)) => "0.0".to_string(),
        Ty::TLiteral(LiteralType::TPureNat) | Ty::TLiteral(LiteralType::TPureInt) => {
            "0i128".to_string()
        }
        _ => "unimplemented!(\"placeholder\")".to_string(),
    }
}

/// Recursively check whether `ty` mentions the given `adt_def_id`.
#[allow(dead_code)]
fn ty_references(ty: &Ty, adt_id: u64) -> bool {
    match ty {
        Ty::TAdt(a) => {
            if matches!(&a.type_id, TypeId::TAdtId(id) if *id == adt_id) {
                return true;
            }
            a.generics.types.iter().any(|t| ty_references(t, adt_id))
        }
        Ty::TArrow(a) => ty_references(&a.input, adt_id) || ty_references(&a.output, adt_id),
        _ => false,
    }
}

/// Like [`ty_references`] but follows ADT references through the
/// crate's type-decl table to detect mutually-recursive cycles. The
/// search bails on already-visited type ids so cycles in the graph
/// don't cause non-termination.
fn ty_transitively_references(ty: &Ty, adt_id: u64, ctx: &EmitCtx) -> bool {
    fn go(ty: &Ty, target: u64, ctx: &EmitCtx, seen: &mut Vec<u64>) -> bool {
        match ty {
            Ty::TAdt(a) => {
                if let TypeId::TAdtId(id) = &a.type_id {
                    if *id == target {
                        return true;
                    }
                    if !seen.contains(id) {
                        seen.push(*id);
                        if let Some(td) = ctx.type_decl(*id) {
                            let fields_iter: Vec<&Ty> = match &td.kind {
                                TypeDeclKind::Struct(fs) => {
                                    fs.iter().map(|f| &f.field_ty).collect()
                                }
                                TypeDeclKind::Enum(vs) => vs
                                    .iter()
                                    .flat_map(|v| v.fields.iter().map(|f| &f.field_ty))
                                    .collect(),
                                TypeDeclKind::Opaque => Vec::new(),
                            };
                            for ft in fields_iter {
                                if go(ft, target, ctx, seen) {
                                    return true;
                                }
                            }
                        }
                    }
                }
                a.generics.types.iter().any(|t| go(t, target, ctx, seen))
            }
            Ty::TArrow(a) => {
                go(&a.input, target, ctx, seen) || go(&a.output, target, ctx, seen)
            }
            _ => false,
        }
    }
    let mut seen = Vec::new();
    go(ty, adt_id, ctx, &mut seen)
}

/// Recursively check whether `ty` uses the type-param at `idx`.
fn ty_uses_typaram(ty: &Ty, idx: u64) -> bool {
    match ty {
        Ty::TVar(DeBruijnVar::Bound(b)) => b.value == idx,
        Ty::TVar(DeBruijnVar::Free(id)) => *id == idx,
        Ty::TAdt(a) => a.generics.types.iter().any(|t| ty_uses_typaram(t, idx)),
        Ty::TArrow(a) => ty_uses_typaram(&a.input, idx) || ty_uses_typaram(&a.output, idx),
        _ => false,
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

/// Emit `where T: 'static, U: 'static, ...` clauses so generic type
/// parameters can survive inside boxed-trait-object closures
/// (the dyn `FnOnce` default-bound is `'static`).
fn emit_static_where_clause(g: &GenericParams) -> String {
    if g.types.is_empty() {
        return String::new();
    }
    let parts: Vec<String> = g
        .types
        .iter()
        .map(|t| format!("{}: 'static", sanitize_ident(&t.name)))
        .collect();
    format!(" where {}", parts.join(", "))
}

// ---------- type emission ----------

fn ty_to_rust(ty: &Ty, ctx: &EmitCtx, gctx: &GenCtx) -> String {
    match ty {
        Ty::TLiteral(lt) => literal_type_to_rust(lt),
        Ty::TArrow(a) => {
            // Closures show up as `Lambda` expressions; for the type
            // position we render as a boxed `FnOnce` trait object so
            // the same type works in `let` bindings, struct fields,
            // tuple elements, and return positions alike. `FnOnce` is
            // permissive about captured-by-move state — Aeneas
            // backward functions are call-once by design, matching
            // the s2p one-shot semantics.
            format!(
                "Box<dyn FnOnce({}) -> {}>",
                ty_to_rust(&a.input, ctx, gctx),
                ty_to_rust(&a.output, ctx, gctx)
            )
        }
        Ty::TAdt(a) => adt_to_rust(a, ctx, gctx),
        Ty::TVar(v) => match v {
            DeBruijnVar::Bound(b) => gctx.type_var(b.value),
            DeBruijnVar::Free(id) => gctx.type_var(*id),
        },
        Ty::TTraitType(tt) => {
            // Best-effort: render as `<Self as Trait>::AssocTy`. We
            // don't have an associated-type name lookup here; emit a
            // unit-typed placeholder so callers still typecheck.
            let _ = tt;
            "()".to_string()
        }
        Ty::TNever => "!".to_string(),
        // `dyn Trait` is hard to recover faithfully — we use a unit
        // wrapper so the type at least exists and supports
        // `Default::default()` for placeholder construction.
        Ty::TDynTrait(_) => "()".to_string(),
        Ty::TError => "()".to_string(),
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
    let where_clause = emit_static_where_clause(&fd.signature.generics);

    let _ = writeln!(
        out,
        "pub fn {name}{generics}({}) -> {ret_ty}{where_clause} {{",
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
                    ctx,
                );

                // If the bound expression is a known placeholder (one
                // of the QualifIds we can't faithfully emit), swap in
                // a typed `Err::<T,()>(())` for monadic context (so
                // `?` typechecks) or a `unimplemented!()` for direct
                // assignment. This is necessary because placeholders
                // can't satisfy `Try` AND act as a value uniformly.
                let bound_expr = if is_placeholder_qualif(&payload.bound) {
                    if payload.monadic {
                        format!("(Err::<{bound_ty}, ()>(()))")
                    } else {
                        format!("unimplemented!(\"placeholder\")")
                    }
                } else {
                    expr_to_string(&payload.bound, ctx, gctx, binders)
                };
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
/// `let (a, b): ...`; struct destructures yield
/// `let Name { f: v0, .. } = ...`. ADT patterns we can't render
/// cleanly fall back to a fresh name + a `// TODO`.
///
/// Critical: all binder names returned must be unique across the
/// produced pattern; we always allocate fresh names rather than
/// echoing the IR's basename (which would collide whenever two
/// sibling fields share a hint like `back`).
fn let_pattern(
    tp: &TPat,
    binders: &mut BinderCtx,
    ctx: &EmitCtx,
) -> (String, Vec<String>) {
    match &tp.pat {
        Pat::PBound(b) => {
            let hint = b.var.basename.clone().unwrap_or_default();
            let sn = binders.fresh_from_hint(&hint);
            (sn.clone(), vec![sn])
        }
        Pat::POpen(o) => {
            let hint = o.fvar.basename.clone().unwrap_or_default();
            let sn = binders.fresh_from_hint(&hint);
            (sn.clone(), vec![sn])
        }
        Pat::PAdt(adt) => {
            // Tuples: render as `(a, b, c)`.
            let is_tuple =
                matches!(&tp.ty, Ty::TAdt(a) if matches!(a.type_id, TypeId::TTuple));
            if is_tuple {
                let mut names = Vec::with_capacity(adt.fields.len());
                let mut rendered = Vec::with_capacity(adt.fields.len());
                for f in &adt.fields {
                    let (s, sub) = let_pattern(f, binders, ctx);
                    rendered.push(s);
                    names.extend(sub);
                }
                return (format!("({})", rendered.join(", ")), names);
            }
            // Single-variant ADT (struct destructure).
            if let Ty::TAdt(a) = &tp.ty {
                if let TypeId::TAdtId(id) = &a.type_id {
                    if let Some(td) = ctx.type_decl(*id) {
                        if let TypeDeclKind::Struct(fields) = &td.kind {
                            let tname = ctx.type_decl_name(*id);
                            let any_named =
                                fields.iter().any(|f| f.field_name.is_some());
                            let mut sub_pats = Vec::with_capacity(adt.fields.len());
                            let mut binder_names = Vec::with_capacity(adt.fields.len());
                            for (i, f) in adt.fields.iter().enumerate() {
                                let (s, sub) = let_pattern(f, binders, ctx);
                                let fname = fields
                                    .get(i)
                                    .and_then(|f| f.field_name.clone())
                                    .unwrap_or_else(|| format!("f{i}"));
                                if any_named {
                                    sub_pats.push(format!(
                                        "{}: {}",
                                        sanitize_ident(&fname),
                                        s
                                    ));
                                } else {
                                    sub_pats.push(s);
                                }
                                // Box-deref the binder if this field
                                // is self-recursive (same as for
                                // enum-variant patterns). Uses
                                // transitive reachability so
                                // mutually-recursive families work.
                                let is_rec = fields
                                    .get(i)
                                    .map(|f| {
                                        ty_transitively_references(
                                            &f.field_ty, *id, ctx,
                                        )
                                    })
                                    .unwrap_or(false);
                                if is_rec {
                                    for n in sub {
                                        binder_names.push(format!("(*{n})"));
                                    }
                                } else {
                                    binder_names.extend(sub);
                                }
                            }
                            let rendered = if any_named {
                                format!("{tname} {{ {} }}", sub_pats.join(", "))
                            } else {
                                format!("{tname}({})", sub_pats.join(", "))
                            };
                            return (rendered, binder_names);
                        }
                    }
                }
            }
            // Enum-with-explicit-variant pattern in let-position:
            // unusual (would have to be irrefutable). Fall back to
            // a fresh name (loses structural intent).
            let n = binders.fresh_from_hint("adt");
            (n.clone(), vec![n])
        }
        Pat::PIgnored => {
            // `_` introduces no binder — important: the IR's BVar
            // indices skip PIgnored slots, so we must NOT push a
            // placeholder name (doing so would shift the entire
            // scope and break later resolutions).
            ("_".to_string(), Vec::new())
        }
        Pat::PConstant(_) => {
            // Refutable in `let`, but accepted in some IR shapes —
            // emit as `_` with no binder.
            ("_".to_string(), Vec::new())
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
        Expr::CVar(_id) => {
            // CVar = lifted const value. We don't have the const
            // table at emit time. Use the expression's type to pick
            // a concrete shape — integers/bools get a 0/false
            // literal; everything else gets `unimplemented!()` which
            // is `!` and coerces, with the let-site wrapping it in
            // `Err::<_,()>(())` for monadic positions.
            cvar_default_for_ty(&texpr.ty)
        }
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

/// Recognise expressions whose emission yields one of our typed
/// placeholders. Used by the let-emit site to swap in a `Try`-friendly
/// `Err::<T, ()>(())` when the surrounding `?` would otherwise reject
/// the placeholder's type. We walk through `App` chains and `Meta`
/// wrappers to find the head qualif.
fn is_placeholder_qualif(texpr: &TExpr) -> bool {
    let e = unwrap_meta(texpr);
    match &e.e {
        Expr::Qualif(q) => placeholder_qualif_id(&q.id),
        Expr::App(_) => {
            // Walk to the head.
            let mut cur = e;
            loop {
                let e2 = unwrap_meta(cur);
                match &e2.e {
                    Expr::App(app) => cur = &app.fun_,
                    Expr::Qualif(q) => return placeholder_qualif_id(&q.id),
                    _ => return false,
                }
            }
        }
        _ => false,
    }
}

fn placeholder_qualif_id(id: &QualifId) -> bool {
    match id {
        QualifId::Global(_)
        | QualifId::TraitConst(_)
        | QualifId::MkDynTrait(_) => true,
        QualifId::FunOrOp(FunOrOpId::Fun(FunId::FromLlbc(reg))) => {
            matches!(
                reg.kind,
                FnPtrKind::FunId(LlbcFunId::FBuiltin) | FnPtrKind::TraitMethod(_)
            )
        }
        QualifId::FunOrOp(FunOrOpId::Fun(FunId::Pure(p))) => matches!(
            p,
            PureBuiltinFunId::UpdateAtIndex(_)
                | PureBuiltinFunId::Discriminant
                | PureBuiltinFunId::ResultUnwrapMut
                | PureBuiltinFunId::GetTarget
        ),
        _ => false,
    }
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
    // The IR represents curried closure application as a left-nested
    // `App` chain. When the head's type is a `TArrow`, we walk through
    // the arrow chain in lock-step with the args list, emitting either
    // `f(a)` for a single-arg slot or `f((a, b))` if the input is a
    // tuple. Anything left over once the arrow chain is exhausted is
    // appended directly (defensive — shouldn't happen in well-typed
    // IR but keeps the output rustc-parseable).
    if matches!(&head.ty, Ty::TArrow(_)) {
        let mut s = head_s.clone();
        let mut cur_ty = &head.ty;
        let mut i = 0usize;
        while i < args_s.len() {
            let next_ty = if let Ty::TArrow(a) = cur_ty {
                if matches!(&*a.input, Ty::TAdt(ad) if matches!(ad.type_id, TypeId::TTuple))
                {
                    // Tuple input: figure out arity from the input
                    // type's generics so we know how many `args` to
                    // bundle. If the IR provides too few, just take
                    // them all.
                    let arity = if let Ty::TAdt(ad) = &*a.input {
                        ad.generics.types.len().max(1)
                    } else {
                        1
                    };
                    let end = (i + arity).min(args_s.len());
                    if end - i == 1 {
                        s = format!("({}({}))", s, args_s[i]);
                    } else {
                        let tup = args_s[i..end].join(", ");
                        s = format!("({}(({})))", s, tup);
                    }
                    i = end;
                } else {
                    s = format!("({}({}))", s, args_s[i]);
                    i += 1;
                }
                &*a.output
            } else {
                // Type chain exhausted but more args remain — emit a
                // best-effort positional call and bail.
                let rest = args_s[i..].join(", ");
                return format!("({s}({rest}))");
            };
            cur_ty = next_ty;
        }
        return s;
    }
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
            emit_fun_call(fid, &args_s, &q.generics, ctx, gctx)
        }
        QualifId::Global(_id) => {
            // Look up the global decl and emit a path reference; if
            // not found, emit a typed `Default::default()` so the
            // value supports method-call syntax (`.checked_mul(..)`
            // etc. wouldn't work on `!`). The let-site rewrites this
            // to `Err::<T, ()>(())` when monadic so `?` still
            // typechecks.
            "Default::default()".to_string()
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
        QualifId::TraitConst(_) => "Default::default()".to_string(),
        QualifId::MkDynTrait(_) => "Default::default()".to_string(),
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
    ty: &Ty,
    ctx: &EmitCtx,
    gctx: &GenCtx,
    binders: &mut BinderCtx,
) -> String {
    // Zero-arg variant: re-use the apply path with an empty arg list.
    // For pure-placeholder qualifs (Global / TraitConst / etc.), pick
    // a type-driven default expression so receivers like
    // `.checked_mul(..)` continue to typecheck.
    match &q.id {
        QualifId::Global(_)
        | QualifId::TraitConst(_)
        | QualifId::MkDynTrait(_) => cvar_default_for_ty(ty),
        // Fn ref at value position (no args, surrounding type is a
        // `TArrow`): reify the fn into a boxed-trait-object closure
        // so the let-binding's `Box<dyn FnOnce(..)..>` annotation
        // typechecks. We pass through `Box::new(fn_name)` and rely on
        // the auto-coercion to `Box<dyn FnOnce>`.
        QualifId::FunOrOp(FunOrOpId::Fun(FunId::FromLlbc(reg)))
            if matches!(ty, Ty::TArrow(_)) =>
        {
            if let FnPtrKind::FunId(LlbcFunId::FRegular(id)) = &reg.kind {
                let lm = reg.loop_.as_ref().map(|l| l.loop_id);
                let n = ctx
                    .fun_decl_name(*id, lm)
                    .or_else(|| ctx.fun_decl_name(*id, None))
                    .unwrap_or_else(|| format!("__fn_{id}"));
                return format!("(Box::new({n}))");
            }
            emit_qualif_apply(q, &[], ctx, gctx, binders)
        }
        _ => emit_qualif_apply(q, &[], ctx, gctx, binders),
    }
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
        // The IR threads `Neg` through the `can_fail` monad (because
        // signed integer negation overflows on `MIN`). Mirror that
        // here so the surrounding `?` typechecks.
        Unop::Neg(_) => format!("({a}.checked_neg().ok_or(()))"),
        Unop::Cast(c) => match c {
            CastKind::CastLit(cl) => {
                format!("({a} as {})", literal_type_to_rust(&cl.dst))
            }
            CastKind::CastRawPtr(_) => format!("/* raw ptr cast */ {a}"),
        },
        // `array_to_slice` in the IR returns a (logical) slice; we
        // model slices as `Vec<T>` at the Rust level (owned, sized),
        // so synthesize a `Vec::from(&{a}[..])` to match the type.
        Unop::ArrayToSlice => format!("(Vec::from(&{a}[..]))"),
    }
}

/// Emit a `::<T, U, N>` turbofish for the given generic-args bundle,
/// or an empty string if there's nothing to instantiate.
fn turbofish(g: &GenericArgs, ctx: &EmitCtx, gctx: &GenCtx) -> String {
    if g.types.is_empty() && g.const_generics.is_empty() {
        return String::new();
    }
    let mut parts: Vec<String> = g
        .types
        .iter()
        .map(|t| ty_to_rust(t, ctx, gctx))
        .collect();
    for c in &g.const_generics {
        parts.push(const_generic_to_rust(c, gctx));
    }
    format!("::<{}>", parts.join(", "))
}

fn emit_fun_call(
    fid: &FunId,
    args: &[String],
    generics: &GenericArgs,
    ctx: &EmitCtx,
    gctx: &GenCtx,
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
                let turbo = turbofish(generics, ctx, gctx);
                format!("({n}{turbo}({}))", args.join(", "))
            }
            FnPtrKind::FunId(LlbcFunId::FBuiltin) => {
                // Builtin call (e.g. array_index, slice_to_array): we
                // don't have a name to dispatch on at this layer, so
                // emit a `!`-typed placeholder. The arg-side
                // expressions are still evaluated for side-effect
                // shape preservation.
                let _ = args;
                "unimplemented!(\"FBuiltin call\")".to_string()
            }
            FnPtrKind::TraitMethod(tm) => {
                // Best-effort trait-method dispatch: we don't have a
                // method-name lookup here, so emit an unimplemented
                // placeholder. The args are computed but discarded.
                let _ = tm;
                let _ = args;
                "unimplemented!(\"TraitMethod\")".to_string()
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
        // Loop / RecLoopCall placeholders need to fit the Result<T>
        // shape that the surrounding monadic `?` expects.
        Loop(_) | RecLoopCall(_) => format!("Err::<_, ()>(())"),
        FuelDecrease => match args.first() {
            Some(a) => format!("({a}.saturating_sub(1))"),
            None => "0u64".to_string(),
        },
        FuelEqZero => match args.first() {
            Some(a) => format!("({a} == 0)"),
            None => "false".to_string(),
        },
        // `update_at_index` IR call: `(coll, idx, val)` ⇒ a Result-
        // wrapped new collection. We emit a permissive Err placeholder
        // so the `?` typechecks; the args are still emitted as
        // expression positions but discarded.
        UpdateAtIndex(_) => {
            let _ = inner;
            "Err::<_, ()>(())".to_string()
        }
        Discriminant => match args.first() {
            Some(a) => format!("(unimplemented!(\"discriminant {a}\"))"),
            None => "unimplemented!(\"discriminant\")".to_string(),
        },
        ResultUnwrapMut => match args.first() {
            Some(a) => format!("(unimplemented!(\"unwrap_mut {a}\"))"),
            None => "unimplemented!(\"unwrap_mut\")".to_string(),
        },
        GetTarget => match args.first() {
            Some(a) => format!("(unimplemented!(\"get_target {a}\"))"),
            None => "unimplemented!(\"get_target\")".to_string(),
        },
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
            // Wrap any arg whose corresponding field type is
            // self-recursive in `Box::new(...)` (matches the field
            // boxing in `emit_type_decl`). Uses transitive
            // reachability so mutually-recursive families are also
            // boxed.
            let box_self = |idx: usize, fields: &[Field], av: &str| -> String {
                fields
                    .get(idx)
                    .map(|f| {
                        if ty_transitively_references(&f.field_ty, *id, ctx) {
                            format!("Box::new({av})")
                        } else {
                            av.to_string()
                        }
                    })
                    .unwrap_or_else(|| av.to_string())
            };
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
                                        .unwrap_or_else(|| "Default::default()".to_string());
                                    let av = box_self(i, &v.fields, &av);
                                    parts
                                        .push(format!("{}: {}", sanitize_ident(&fname), av));
                                }
                                return format!("{tname}::{vname} {{ {} }}", parts.join(", "));
                            } else {
                                let parts: Vec<String> = args
                                    .iter()
                                    .enumerate()
                                    .map(|(i, av)| box_self(i, &v.fields, av))
                                    .collect();
                                return format!(
                                    "{tname}::{vname}({})",
                                    parts.join(", ")
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
                                    .unwrap_or_else(|| "unimplemented!()".to_string());
                                let av = box_self(i, fields, &av);
                                parts
                                    .push(format!("{}: {}", sanitize_ident(&fname), av));
                            }
                            return format!("{tname} {{ {} }}", parts.join(", "));
                        } else {
                            let parts: Vec<String> = args
                                .iter()
                                .enumerate()
                                .map(|(i, av)| box_self(i, fields, av))
                                .collect();
                            return format!("{tname}({})", parts.join(", "));
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
    // Reuse the same pattern-destructuring logic as `let` so tuple /
    // struct lambdas (e.g. `|(iter, a)|`) bind every field correctly.
    // We wrap every closure in `Box::new(...)` because the `TArrow`
    // type emit produces a `Box<dyn Fn(..)..>` shape — raw closures
    // would mismatch the expected boxed-trait-object type.
    let in_ty = ty_to_rust(&p.pat.ty, ctx, gctx);
    let out_ty = ty_to_rust(&p.body.ty, ctx, gctx);
    let (pat_rendered, scope_names) = let_pattern(&p.pat, binders, ctx);
    binders.push(scope_names);
    let body = expr_to_string(&p.body, ctx, gctx, binders);
    binders.pop();
    format!(
        "(Box::new(move |{pat_rendered}: {in_ty}| -> {out_ty} {{ {body} }}) as Box<dyn FnOnce({in_ty}) -> {out_ty}>)"
    )
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
                    pattern_to_rust(&arm.pat.pat, scrut_adt_id, ctx, binders);
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
///
/// All binder names are allocated via `binders.fresh_from_hint(..)`
/// so sibling patterns never collide on the IR's basename.
fn pattern_to_rust(
    p: &Pat,
    scrut_adt_id: Option<u64>,
    ctx: &EmitCtx,
    binders: &mut BinderCtx,
) -> (String, Vec<String>) {
    match p {
        Pat::PConstant(lit) => (literal_to_rust(lit), Vec::new()),
        Pat::PIgnored => ("_".to_string(), Vec::new()),
        Pat::PBound(b) => {
            let hint = b.var.basename.clone().unwrap_or_default();
            let sn = binders.fresh_from_hint(&hint);
            (sn.clone(), vec![sn])
        }
        Pat::POpen(o) => {
            let hint = o.fvar.basename.clone().unwrap_or_default();
            let sn = binders.fresh_from_hint(&hint);
            (sn.clone(), vec![sn])
        }
        Pat::PAdt(adt) => pattern_adt_to_rust(adt, scrut_adt_id, ctx, binders),
    }
}

fn pattern_adt_to_rust(
    adt: &AdtPat,
    scrut_adt_id: Option<u64>,
    ctx: &EmitCtx,
    binders: &mut BinderCtx,
) -> (String, Vec<String>) {
    let mut sub_pats = Vec::new();
    let mut sub_binders = Vec::new();
    // If we know the parent ADT, check each variant field for
    // self-recursion; the recursive fields are stored as `Box<Self>`
    // in our emit. We rewrite the binder name to `(*name)` so the
    // body sees the deref'd value (matching the IR's value-semantics
    // model).
    let self_id = scrut_adt_id;
    let fields_meta: Vec<Option<&Ty>> = match (self_id, adt.variant_id) {
        (Some(adt_id), Some(vid)) => match ctx.type_decl(adt_id) {
            Some(td) => match &td.kind {
                TypeDeclKind::Enum(variants) => match variants.get(vid as usize) {
                    Some(v) => v.fields.iter().map(|f| Some(&f.field_ty)).collect(),
                    None => adt.fields.iter().map(|_| None).collect(),
                },
                _ => adt.fields.iter().map(|_| None).collect(),
            },
            None => adt.fields.iter().map(|_| None).collect(),
        },
        _ => adt.fields.iter().map(|_| None).collect(),
    };
    for (i, f) in adt.fields.iter().enumerate() {
        let is_recursive = self_id
            .and_then(|id| {
                fields_meta
                    .get(i)
                    .copied()
                    .flatten()
                    .map(|ty| ty_transitively_references(ty, id, ctx))
            })
            .unwrap_or(false);
        if is_recursive {
            // Field stored as `Box<...>` in our emit; we can't pattern-
            // match through a Box on stable Rust. Render the slot as
            // a bare binder that receives the whole `Box<...>` value.
            // If the inner pattern is a single bare binder, we
            // remap that one binder's resolution to `(*name)` so the
            // IR's value-semantics access reads through transparently.
            // For multi-binder sub-patterns (e.g. struct destructure
            // through a Box), we can't faithfully resolve all field
            // refs without unstable `box` patterns; we still bind to
            // a single name and let the resulting unresolved binders
            // surface as type errors in the affected fixtures (logged
            // as KNOWN_GAPS).
            let n = binders.fresh_from_hint("rec");
            sub_pats.push(n.clone());
            // Map each of the inner pattern's binders to `(*n)` (best-
            // effort — only correct for the single-binder case).
            let n_inner = count_binders(&f.pat);
            if n_inner <= 1 {
                sub_binders.push(format!("(*{n})"));
            } else {
                for _ in 0..n_inner {
                    sub_binders.push(format!("(*{n})"));
                }
            }
            continue;
        }
        // Determine the sub-field's parent ADT id (for nested enum
        // variant pattern rendering).
        let sub_scrut_adt_id = match &f.ty {
            Ty::TAdt(a) => match &a.type_id {
                TypeId::TAdtId(id) => Some(*id),
                _ => None,
            },
            _ => None,
        };
        let (s, bs) = pattern_to_rust(&f.pat, sub_scrut_adt_id, ctx, binders);
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
        // If we DO know the parent ADT id (and it's a struct), use
        // a struct-field destructure instead.
        if let Some(adt_id) = scrut_adt_id {
            if let Some(td) = ctx.type_decl(adt_id) {
                if let TypeDeclKind::Struct(fields) = &td.kind {
                    let tname = ctx.type_decl_name(adt_id);
                    if fields.is_empty() {
                        return (tname, sub_binders);
                    }
                    let any_named =
                        fields.iter().any(|f| f.field_name.is_some());
                    if any_named {
                        let mut parts = Vec::new();
                        for (i, f) in fields.iter().enumerate() {
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
                            format!("{tname} {{ {} }}", parts.join(", ")),
                            sub_binders,
                        );
                    }
                    return (
                        format!("{tname}({})", sub_pats.join(", ")),
                        sub_binders,
                    );
                }
            }
        }
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
            if parts.is_empty() {
                return "()".to_string();
            } else if parts.len() == 1 {
                return format!("({},)", parts[0]);
            }
            return format!("({})", parts.join(", "));
        }
        TypeId::TBuiltin(b) => {
            // `TArray` / `TSlice` aggregate literals come through
            // StructUpdate too. Render them as `[e1, e2, ...]` (array)
            // or `vec![e1, e2, ...]` (slice). Empty updates ⇒ `[]`.
            let parts: Vec<String> = su
                .updates
                .iter()
                .map(|u| expr_to_string(&u.expr, ctx, gctx, binders))
                .collect();
            return match b {
                BuiltinTy::TArray => format!("[{}]", parts.join(", ")),
                BuiltinTy::TSlice => format!("vec![{}]", parts.join(", ")),
                _ => {
                    // For Result/LoopResult/Sum/Error/Fuel/RawPtr/Str:
                    // these don't show up as struct-update literals in
                    // practice, but emit a defensive `()`.
                    let _ = parts;
                    "()".to_string()
                }
            };
        }
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
    // We deliberately drop the `..init` tail: Aeneas's IR uses it to
    // model functional updates (the result may even have a different
    // generic instantiation than `init`), but Rust's struct-update
    // syntax requires both to share the same struct type. Synthesise
    // missing fields from `init` instead — for any field not in
    // `updates`, project it from `init`. This produces a literal that
    // typechecks even when the IR's "init" has a different generic
    // parameterisation than the result.
    if let Some(td) = td {
        if let TypeDeclKind::Struct(fields) = &td.kind {
            let init_s = su
                .init
                .as_ref()
                .map(|init| expr_to_string(init, ctx, gctx, binders));
            let mut all_parts = Vec::new();
            let mut covered: Vec<bool> = vec![false; fields.len()];
            for (idx, u) in su.updates.iter().enumerate() {
                let fid = u.field_id as usize;
                if fid < covered.len() {
                    covered[fid] = true;
                }
                let _ = idx;
            }
            // Helper: render field i. If updates has it, take that;
            // else project from init.
            for (i, f) in fields.iter().enumerate() {
                let any_named = f.field_name.is_some();
                let fname = f
                    .field_name
                    .clone()
                    .unwrap_or_else(|| format!("f{i}"));
                let val = if covered[i] {
                    let u = su.updates.iter().find(|u| u.field_id as usize == i).unwrap();
                    expr_to_string(&u.expr, ctx, gctx, binders)
                } else if let Some(ref init) = init_s {
                    if any_named {
                        format!("{}.{}", init, sanitize_ident(&fname))
                    } else {
                        format!("{}.{}", init, i)
                    }
                } else {
                    "unimplemented!()".to_string()
                };
                if fields.iter().any(|f| f.field_name.is_some()) {
                    all_parts.push(format!("{}: {}", sanitize_ident(&fname), val));
                } else {
                    all_parts.push(val);
                }
            }
            let any_named = fields.iter().any(|f| f.field_name.is_some());
            return if any_named {
                format!("{head} {{ {} }}", all_parts.join(", "))
            } else {
                format!("{head}({})", all_parts.join(", "))
            };
        }
    }
    // Fallback: structurally formed struct literal with whatever we
    // can recover.
    match &su.init {
        Some(init) => {
            let i = expr_to_string(init, ctx, gctx, binders);
            format!("{head} {{ {}, ..{i} }}", parts.join(", "))
        }
        None => format!("{head} {{ {} }}", parts.join(", ")),
    }
}

/// Count the number of binders a pattern would introduce (PBound /
/// POpen, including those nested under PAdt).
fn count_binders(p: &Pat) -> usize {
    match p {
        Pat::PBound(_) | Pat::POpen(_) => 1,
        Pat::PIgnored | Pat::PConstant(_) => 0,
        Pat::PAdt(adt) => adt.fields.iter().map(|f| count_binders(&f.pat)).sum(),
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
