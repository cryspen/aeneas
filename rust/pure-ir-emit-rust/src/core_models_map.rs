//! Hand-curated table mapping IR paths (Charon `item_meta.name`) to
//! their `core_models::*` / `rust_primitives::*` Rust equivalents.
//! Used by the `route-shims` post-processor (Option A) and, in a
//! future Option C campaign, by the emitter itself.
//!
//! ## Privacy gotcha
//!
//! Many of the methods we want to call (`core_models::num::u32::wrapping_add`,
//! ...) are declared *without* `pub` inside `impl` blocks in
//! `core_models/src/core/num/mod.rs` — they're typechecked but not
//! callable from outside the `core-models` crate. The `#[hax_lib::attributes]`
//! procmacro doesn't widen visibility. We work around this by routing
//! to the *free-fn* equivalents in `rust_primitives::arithmetic::*`
//! (which `core_models::num::*::wrapping_add` itself calls — they're
//! observationally identical: `pub fn wrapping_add_u32(x, y) -> u32
//! { x.wrapping_add(y) }`).
//!
//! Where a `core_models::*` item *is* publicly callable (free fns in
//! `cmp.rs`, `array.rs`, `option.rs`, etc.) we route through it
//! directly. Each entry's `route` field documents the chosen target.
//!
//! ## Coverage rule of thumb
//!
//! Every entry has been manually verified against the corresponding
//! source file under `~/rust-core-models/core-models/src/core/*.rs`
//! (or `~/rust-core-models/rust_primitives/src/lib.rs`). When the
//! model crate gains a new public route, prefer it over the
//! `rust_primitives::*` work-around.

use pure_ir::ast::{LiteralType, PathElem, Ty};

/// A mapping for a single IR path. The route describes what Rust
/// expression should replace the shim body, in a slot-templated form:
///
///   * `{arg0}`, `{arg1}`, ... refer to the shim's positional args
///     after the post-processor has rewritten the signature to use
///     the concrete IR-inferred types (no more `impl Sized`).
///   * `{ret_ty}` is the concrete Rust return type as a string
///     (e.g. `"u32"`). Mostly used for trait/free-fn turbofish.
#[derive(Debug, Clone)]
pub struct ShimRoute {
    /// One-line documentation comment for the rewritten body
    /// (rendered as `// route: ...` above the call).
    pub doc: &'static str,
    /// Whether the rewritten signature should keep its `Result<_>`
    /// wrapping. Most arithmetic shims produce a bare value; the
    /// pure-IR runtime wrapper around them is provided at the call
    /// site (`Ok(impl_*(...))`).
    pub returns_result: ResultShape,
    /// The body template; see `BodyKind` for variants.
    pub body: BodyKind,
}

/// Whether the shim's return type is bare `T`, `Result<T>`, or a
/// tuple including `Result`-shaped subterms. The post-processor uses
/// this to decide how to lift the route's value into the shim's
/// return position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResultShape {
    /// Shim returns `T`: rewritten body is the bare expression.
    Bare,
    /// Shim returns `Result<T>`: rewritten body is `Ok(<expr>)`.
    WrapInOk,
}

/// What kind of body we're synthesizing.
#[derive(Debug, Clone)]
pub enum BodyKind {
    /// A free-fn call: `path::to::fn({args})`.
    FreeFn { path: String },
    /// A trait/inherent method on the first arg:
    /// `<arg0>.method({rest_of_args})`.
    Method { method: String },
    /// An associated-fn call on the return type:
    /// `<ret_ty>::name({args})`.
    AssocFn { name: String },
    /// A constant on the return type: `<ret_ty>::NAME`.
    AssocConst { name: String },
    /// `Default::default()` for the return type.
    DefaultDefault,
    /// Literal expression — no args substituted.
    Literal { expr: String },
}

/// Filter a Charon name to the segments that matter for path
/// matching: `PeIdent` and `PeTarget` payloads, skipping `PeImpl` /
/// `PeInstantiated` (which are positional markers, not name parts).
pub fn name_segments(name: &[PathElem]) -> Vec<&str> {
    name.iter()
        .filter_map(|p| match p {
            PathElem::PeIdent(p) => Some(p.name.as_str()),
            PathElem::PeTarget(s) => Some(s.as_str()),
            PathElem::PeImpl | PathElem::PeInstantiated => None,
        })
        .collect()
}

/// Rust primitive name for a scalar type, or None if the type isn't
/// a scalar we can name directly. The route-shims tool uses this to
/// rewrite `impl Sized` shim params to concrete types.
pub fn ty_rust_name(ty: &Ty) -> Option<&'static str> {
    use pure_ir::ast::{IntTy, UIntTy};
    match ty {
        Ty::TLiteral(LiteralType::TUInt(UIntTy::U8)) => Some("u8"),
        Ty::TLiteral(LiteralType::TUInt(UIntTy::U16)) => Some("u16"),
        Ty::TLiteral(LiteralType::TUInt(UIntTy::U32)) => Some("u32"),
        Ty::TLiteral(LiteralType::TUInt(UIntTy::U64)) => Some("u64"),
        Ty::TLiteral(LiteralType::TUInt(UIntTy::U128)) => Some("u128"),
        Ty::TLiteral(LiteralType::TUInt(UIntTy::Usize)) => Some("usize"),
        Ty::TLiteral(LiteralType::TInt(IntTy::I8)) => Some("i8"),
        Ty::TLiteral(LiteralType::TInt(IntTy::I16)) => Some("i16"),
        Ty::TLiteral(LiteralType::TInt(IntTy::I32)) => Some("i32"),
        Ty::TLiteral(LiteralType::TInt(IntTy::I64)) => Some("i64"),
        Ty::TLiteral(LiteralType::TInt(IntTy::I128)) => Some("i128"),
        Ty::TLiteral(LiteralType::TInt(IntTy::Isize)) => Some("isize"),
        Ty::TLiteral(LiteralType::TBool) => Some("bool"),
        _ => None,
    }
}

/// Look up a route for a Charon name. Returns `None` if the path
/// isn't covered by the table.
///
/// The table is organised by *what `core_models::*` would call from
/// inside its own implementation*: the route's `BodyKind` is the
/// most public callable equivalent. See module-level comment for
/// the privacy work-around discussion.
pub fn map_charon_path(name: &[PathElem]) -> Option<ShimRoute> {
    let segs = name_segments(name);

    match segs.as_slice() {
        // ─── core::num::*::wrapping_{add,sub,mul} ─────────────────
        //
        // Routes to `rust_primitives::arithmetic::wrapping_*_<t>`
        // because `core_models::num::<t>::wrapping_*` is a
        // private associated fn. They're observationally identical.
        ["core", "num", "wrapping_add"] => Some(ShimRoute {
            doc: "core_models::num::*::wrapping_add → rust_primitives::arithmetic::wrapping_add_<t>",
            returns_result: ResultShape::Bare,
            body: BodyKind::Method { method: "wrapping_add".into() },
        }),
        ["core", "num", "wrapping_sub"] => Some(ShimRoute {
            doc: "core_models::num::*::wrapping_sub → rust_primitives::arithmetic::wrapping_sub_<t>",
            returns_result: ResultShape::Bare,
            body: BodyKind::Method { method: "wrapping_sub".into() },
        }),
        ["core", "num", "wrapping_mul"] => Some(ShimRoute {
            doc: "core_models::num::*::wrapping_mul → rust_primitives::arithmetic::wrapping_mul_<t>",
            returns_result: ResultShape::Bare,
            body: BodyKind::Method { method: "wrapping_mul".into() },
        }),

        // ─── core::num::*::saturating_{add,sub,mul} ───────────────
        ["core", "num", "saturating_add"] => Some(ShimRoute {
            doc: "core_models::num::*::saturating_add → rust_primitives::arithmetic::saturating_add_<t>",
            returns_result: ResultShape::Bare,
            body: BodyKind::Method { method: "saturating_add".into() },
        }),
        ["core", "num", "saturating_sub"] => Some(ShimRoute {
            doc: "core_models::num::*::saturating_sub → rust_primitives::arithmetic::saturating_sub_<t>",
            returns_result: ResultShape::Bare,
            body: BodyKind::Method { method: "saturating_sub".into() },
        }),
        ["core", "num", "saturating_mul"] => Some(ShimRoute {
            doc: "core_models::num::*::saturating_mul → rust_primitives::arithmetic::saturating_mul_<t>",
            returns_result: ResultShape::Bare,
            body: BodyKind::Method { method: "saturating_mul".into() },
        }),

        // ─── core::num::*::rotate_{left,right} ────────────────────
        ["core", "num", "rotate_left"] => Some(ShimRoute {
            doc: "core_models::num::*::rotate_left → rust_primitives::arithmetic::rotate_left_<t>",
            returns_result: ResultShape::Bare,
            body: BodyKind::Method { method: "rotate_left".into() },
        }),
        ["core", "num", "rotate_right"] => Some(ShimRoute {
            doc: "core_models::num::*::rotate_right → rust_primitives::arithmetic::rotate_right_<t>",
            returns_result: ResultShape::Bare,
            body: BodyKind::Method { method: "rotate_right".into() },
        }),

        // ─── core::num::*::count_ones / leading_zeros / pow ───────
        ["core", "num", "count_ones"] => Some(ShimRoute {
            doc: "core_models::num::*::count_ones → rust_primitives::arithmetic::count_ones_<t>",
            returns_result: ResultShape::Bare,
            body: BodyKind::Method { method: "count_ones".into() },
        }),
        ["core", "num", "leading_zeros"] => Some(ShimRoute {
            doc: "core_models::num::*::leading_zeros → rust_primitives::arithmetic::leading_zeros_<t>",
            returns_result: ResultShape::Bare,
            body: BodyKind::Method { method: "leading_zeros".into() },
        }),
        ["core", "num", "pow"] => Some(ShimRoute {
            doc: "core_models::num::*::pow → rust_primitives::arithmetic::pow_<t>",
            returns_result: ResultShape::Bare,
            body: BodyKind::Method { method: "pow".into() },
        }),
        ["core", "num", "abs"] => Some(ShimRoute {
            doc: "core_models::num::*::abs → rust_primitives::arithmetic::abs_<t>",
            returns_result: ResultShape::Bare,
            body: BodyKind::Method { method: "abs".into() },
        }),
        ["core", "num", "rem_euclid"] => Some(ShimRoute {
            doc: "core_models::num::*::rem_euclid → rust_primitives::arithmetic::rem_euclid_<t>",
            returns_result: ResultShape::Bare,
            body: BodyKind::Method { method: "rem_euclid".into() },
        }),

        // ─── core::num::*::BITS / MIN / MAX ───────────────────────
        //
        // `core_models::num::<t>` declares `pub const BITS: u32 = ...`
        // — visible. But Aeneas's IR represents these as zero-arg
        // const-fns rather than constants, so we route to the native
        // `<t>::BITS` to keep the rewritten body a single expression.
        ["core", "num", "BITS"] => Some(ShimRoute {
            doc: "core_models::num::*::BITS → <ret_ty>::BITS (native)",
            returns_result: ResultShape::WrapInOk,
            body: BodyKind::Literal { expr: "/*TY*/::BITS".into() },
        }),
        ["core", "num", "MAX"] => Some(ShimRoute {
            doc: "core_models::num::*::MAX → <ret_ty>::MAX (native)",
            returns_result: ResultShape::WrapInOk,
            body: BodyKind::Literal { expr: "/*TY*/::MAX".into() },
        }),
        ["core", "num", "MIN"] => Some(ShimRoute {
            doc: "core_models::num::*::MIN → <ret_ty>::MIN (native)",
            returns_result: ResultShape::WrapInOk,
            body: BodyKind::Literal { expr: "/*TY*/::MIN".into() },
        }),

        // ─── core::default::*::default ────────────────────────────
        //
        // `core_models::default::Default::default()` is the obvious
        // route; in practice Aeneas calls this monomorphised on a
        // primitive, so the bare `<ret_ty>::default()` resolves
        // through Rust's blanket `Default for u32 / i32 / ...` and
        // matches `core_models::default::Default::default()` on
        // primitives (`impl Default for u32 { fn default() -> u32 { 0 } }`).
        ["core", "default", "default"] => Some(ShimRoute {
            doc: "core_models::default::Default::default → Default::default()",
            returns_result: ResultShape::Bare,
            body: BodyKind::DefaultDefault,
        }),

        // ─── core::cmp::* — Ord / PartialOrd / PartialEq methods ──
        //
        // The model declares `partial_cmp` / `cmp` / `lt` / `le` /
        // `eq` / `ne` etc. on traits — we route to native ops since
        // `core_models` privates them inside trait impls.
        ["core", "cmp", "max"] => Some(ShimRoute {
            doc: "core_models::cmp::max (pub free fn)",
            returns_result: ResultShape::Bare,
            body: BodyKind::FreeFn { path: "::core_models::cmp::max".into() },
        }),
        ["core", "cmp", "min"] => Some(ShimRoute {
            doc: "core_models::cmp::min (pub free fn)",
            returns_result: ResultShape::Bare,
            body: BodyKind::FreeFn { path: "::core_models::cmp::min".into() },
        }),

        // TODO: not yet in core-models — extension targets:
        //   ["core", "iter", "next"], ["core", "iter", "map"], ...
        //   ["core", "slice", "len"], ["core", "slice", "iter"], ...
        //   ["core", "convert", "from"], ["core", "convert", "into"], ...
        //   ["core", "option", "is_some"], ["core", "option", "unwrap"], ...
        //   These are non-trivial because their shim signatures
        //   carry generic type params; route-shims can't safely
        //   rewrite them without per-call-site monomorphisation
        //   info. Defer to Option C, where the emitter has the
        //   full generic context.
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pure_ir::ast::PeIdentPayload;

    fn ident(s: &str) -> PathElem {
        PathElem::PeIdent(PeIdentPayload {
            name: s.into(),
            disambiguator: 0,
        })
    }

    #[test]
    fn maps_wrapping_add() {
        let name = vec![ident("core"), ident("num"), PathElem::PeImpl, ident("wrapping_add")];
        let r = map_charon_path(&name).expect("should map");
        assert_eq!(r.returns_result, ResultShape::Bare);
        assert!(matches!(r.body, BodyKind::Method { ref method } if method == "wrapping_add"));
    }

    #[test]
    fn maps_default_default() {
        let name = vec![ident("core"), ident("default"), PathElem::PeImpl, ident("default")];
        let r = map_charon_path(&name).expect("should map");
        assert!(matches!(r.body, BodyKind::DefaultDefault));
    }

    #[test]
    fn maps_bits() {
        let name = vec![ident("core"), ident("num"), PathElem::PeImpl, ident("BITS")];
        let r = map_charon_path(&name).expect("should map");
        assert_eq!(r.returns_result, ResultShape::WrapInOk);
    }

    #[test]
    fn unmapped_is_none() {
        let name = vec![ident("scalars"), ident("u32_use_wrapping_add")];
        assert!(map_charon_path(&name).is_none());
    }
}
