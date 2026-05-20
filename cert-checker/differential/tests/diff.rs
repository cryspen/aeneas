//! Differential property tests for the aeneas-lean-checker vertical slice.
//!
//! For each fixture, generate random inputs, run the original Rust
//! function (R₀ — `aeneas_cert_differential::ref_impl` and the ADT
//! per-fixture modules) and the generated model (R₁ —
//! `aeneas_cert_differential::model` and the per-fixture
//! `*_model.rs` includes), assert they agree.
//!
//! Fixtures live under `tests/src/*.rs`; certs under
//! `tests/llbc/*.cert.json`. Regenerate models with
//! `./scripts/regen-diff-models.sh`.

use aeneas_cert_differential::{model, ref_impl};
use aeneas_cert_differential::aggregates_basic::{
    mk_pair_model, mk_pair_ref, mk_tuple_model, mk_tuple_ref,
};
use aeneas_cert_differential::reborrows::{self, set_fst_model, set_fst_ref};
use proptest::prelude::*;

// ====================================================================
// incr_cert.rs
// ====================================================================

proptest! {
    /// `incr_cert::incr` — direct-borrow `*x += 1`, reshaped by the
    /// cert to `u32 → u32`. Existing pre-campaign test (kept for
    /// back-compat with the M9.0c era harness).
    #[test]
    fn incr_matches_model(x in any::<u32>()) {
        prop_assert_eq!(ref_impl::incr_cert_incr(x), model::incr_model(x));
    }
}

// ====================================================================
// constants.rs
// ====================================================================

proptest! {
    /// `constants::incr` — `const fn incr(n: u32) -> u32 { n + 1 }`.
    /// Generic case across the full u32 range. Release-mode `+`
    /// wraps silently, matching R₀'s `wrapping_add(1)`.
    #[test]
    fn constants_incr_matches_model(n in any::<u32>()) {
        prop_assert_eq!(ref_impl::constants_incr(n), model::constants_incr_model(n));
    }

    /// Edge case: small inputs (0..256) where `+ 1` cannot wrap.
    #[test]
    fn constants_incr_matches_model_small(n in 0u32..256) {
        prop_assert_eq!(ref_impl::constants_incr(n), model::constants_incr_model(n));
    }

    /// Edge case: top of the u32 range (MAX-256 ..= MAX) where `+ 1`
    /// wraps. Stresses the model's release-mode overflow semantics.
    #[test]
    fn constants_incr_matches_model_top(n in (u32::MAX - 255)..=u32::MAX) {
        prop_assert_eq!(ref_impl::constants_incr(n), model::constants_incr_model(n));
    }

    /// `constants::mk_pair0` — `const fn mk_pair0(x, y) -> (x, y)`.
    #[test]
    fn constants_mk_pair0_matches_model(x in any::<u32>(), y in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::constants_mk_pair0(x, y),
            model::constants_mk_pair0_model(x, y)
        );
    }

    /// `constants::add` — `const fn add(a: i32, b: i32) -> a + b`.
    /// Release-mode `+` wraps silently, matching R₀'s
    /// `wrapping_add`. Both `a` and `b` cover the full i32 range.
    #[test]
    fn constants_add_matches_model(a in any::<i32>(), b in any::<i32>()) {
        prop_assert_eq!(ref_impl::constants_add(a, b), model::constants_add_model(a, b));
    }
}

// ====================================================================
// bitwise.rs
// ====================================================================

proptest! {
    #[test]
    fn bitwise_xor_u32_matches_model(a in any::<u32>(), b in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::bitwise_xor_u32(a, b),
            model::bitwise_xor_u32_model(a, b)
        );
    }

    #[test]
    fn bitwise_or_u32_matches_model(a in any::<u32>(), b in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::bitwise_or_u32(a, b),
            model::bitwise_or_u32_model(a, b)
        );
    }

    #[test]
    fn bitwise_and_u32_matches_model(a in any::<u32>(), b in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::bitwise_and_u32(a, b),
            model::bitwise_and_u32_model(a, b)
        );
    }

    #[test]
    fn bitwise_shift_u32_matches_model(a in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::bitwise_shift_u32(a),
            model::bitwise_shift_u32_model(a)
        );
    }

    #[test]
    fn bitwise_shift_i32_matches_model(a in any::<i32>()) {
        prop_assert_eq!(
            ref_impl::bitwise_shift_i32(a),
            model::bitwise_shift_i32_model(a)
        );
    }
}

// ====================================================================
// compare_simple.rs
// ====================================================================

proptest! {
    #[test]
    fn compare_simple_id_u32_matches_model(x in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::compare_simple_id_u32(x),
            model::compare_simple_id_u32_model(x)
        );
    }

    /// `compare_simple::add_u32` — newly unblocked by `3d086b79`
    /// (brace-path fix). Previously the model emitted
    /// `core::num::{u32}::wrapping_add(...)` which is invalid Rust
    /// syntax.
    #[test]
    fn compare_simple_add_u32_matches_model(a in any::<u32>(), b in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::compare_simple_add_u32(a, b),
            model::compare_simple_add_u32_model(a, b)
        );
    }
}

// ====================================================================
// calls.rs
// ====================================================================

proptest! {
    /// `calls::incr_inner(y: &mut u32)` — the cert collapses the
    /// in/out borrow into a forward scalar; we shim R₀ to
    /// `u32 → u32` to match.
    #[test]
    fn calls_incr_inner_matches_model(y in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::calls_incr_inner(y),
            model::calls_incr_inner_model(y)
        );
    }

    /// `calls::pick(b, x, y)` — newly unblocked by `3d086b79`. The
    /// cert routes the body through `eval_switch_with_join`; the
    /// emitted model uses an if/else and a final `wrapping_add(1)`.
    #[test]
    fn calls_pick_matches_model(b in any::<bool>(), x in any::<u32>(), y in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::calls_pick(b, x, y),
            model::calls_pick_model(b, x, y)
        );
    }

    /// Phase 1C: SymRecord lowering → Rust struct literal
    /// (`Pair { x: e1, y: e2 }`). Exercises the
    /// `PExpr.recordLit fields (some "Pair")` path through RustEmit.
    #[test]
    fn mk_pair_matches_model(x in any::<u32>(), y in any::<u32>()) {
        let r = mk_pair_ref(x, y);
        let m = mk_pair_model(x, y);
        prop_assert_eq!(r.x, m.x);
        prop_assert_eq!(r.y, m.y);
    }

    /// Sanity check: the tuple-aggregate path (`PExpr.tuple`) has
    /// always worked, but living alongside the ADT proptest catches
    /// any regression in the `(e1, e2)` lowering caused by the Phase
    /// 1C plumbing.
    #[test]
    fn mk_tuple_matches_model(x in any::<u32>(), y in any::<u32>()) {
        prop_assert_eq!(mk_tuple_ref(x, y), mk_tuple_model(x, y));
    }

    /// Phase 1C: struct field update through `&mut Pair`. Exercises
    /// the `PExpr.structUpdate base "fst" value (some "Pair")` path
    /// → Rust's `Pair { fst: x2, ..x1 }` struct-update syntax via
    /// RustEmit.
    #[test]
    fn set_fst_matches_model(fst in any::<u32>(), snd in any::<u32>(), v in any::<u32>()) {
        let p = reborrows::Pair { fst, snd };
        let r = set_fst_ref(p, v);
        let m = set_fst_model(p, v);
        prop_assert_eq!(r.fst, m.fst);
        prop_assert_eq!(r.snd, m.snd);
    }
}

// ====================================================================
// scalars.rs (Phase 4b — new fixture, 13 differential fns)
// ====================================================================

proptest! {
    #[test]
    fn scalars_u32_use_wrapping_add_matches_model(x in any::<u32>(), y in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::scalars_u32_use_wrapping_add(x, y),
            model::scalars_u32_use_wrapping_add_model(x, y)
        );
    }
    #[test]
    fn scalars_i32_use_wrapping_add_matches_model(x in any::<i32>(), y in any::<i32>()) {
        prop_assert_eq!(
            ref_impl::scalars_i32_use_wrapping_add(x, y),
            model::scalars_i32_use_wrapping_add_model(x, y)
        );
    }
    #[test]
    fn scalars_u32_use_wrapping_sub_matches_model(x in any::<u32>(), y in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::scalars_u32_use_wrapping_sub(x, y),
            model::scalars_u32_use_wrapping_sub_model(x, y)
        );
    }
    #[test]
    fn scalars_i32_use_wrapping_sub_matches_model(x in any::<i32>(), y in any::<i32>()) {
        prop_assert_eq!(
            ref_impl::scalars_i32_use_wrapping_sub(x, y),
            model::scalars_i32_use_wrapping_sub_model(x, y)
        );
    }
    #[test]
    fn scalars_u32_use_shift_right_matches_model(x in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::scalars_u32_use_shift_right(x),
            model::scalars_u32_use_shift_right_model(x)
        );
    }
    #[test]
    fn scalars_i32_use_shift_right_matches_model(x in any::<i32>()) {
        prop_assert_eq!(
            ref_impl::scalars_i32_use_shift_right(x),
            model::scalars_i32_use_shift_right_model(x)
        );
    }
    #[test]
    fn scalars_u32_use_shift_left_matches_model(x in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::scalars_u32_use_shift_left(x),
            model::scalars_u32_use_shift_left_model(x)
        );
    }
    #[test]
    fn scalars_i32_use_shift_left_matches_model(x in any::<i32>()) {
        prop_assert_eq!(
            ref_impl::scalars_i32_use_shift_left(x),
            model::scalars_i32_use_shift_left_model(x)
        );
    }
    #[test]
    fn scalars_add_and_matches_model(a in any::<u32>(), b in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::scalars_add_and(a, b),
            model::scalars_add_and_model(a, b)
        );
    }
    #[test]
    fn scalars_u32_use_rotate_right_matches_model(x in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::scalars_u32_use_rotate_right(x),
            model::scalars_u32_use_rotate_right_model(x)
        );
    }
    #[test]
    fn scalars_i32_use_rotate_right_matches_model(x in any::<i32>()) {
        prop_assert_eq!(
            ref_impl::scalars_i32_use_rotate_right(x),
            model::scalars_i32_use_rotate_right_model(x)
        );
    }
    #[test]
    fn scalars_u32_use_rotate_left_matches_model(x in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::scalars_u32_use_rotate_left(x),
            model::scalars_u32_use_rotate_left_model(x)
        );
    }
    #[test]
    fn scalars_i32_use_rotate_left_matches_model(x in any::<i32>()) {
        prop_assert_eq!(
            ref_impl::scalars_i32_use_rotate_left(x),
            model::scalars_i32_use_rotate_left_model(x)
        );
    }
}

// ====================================================================
// demo.rs (Phase 4b — new fixture, 2 differential fns)
// ====================================================================

proptest! {
    #[test]
    fn demo_mul2_add1_matches_model(x in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::demo_mul2_add1(x),
            model::demo_mul2_add1_model(x)
        );
    }
    #[test]
    fn demo_incr_matches_model(x in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::demo_incr(x),
            model::demo_incr_model(x)
        );
    }
}

// ====================================================================
// demo.rs (Session 4 — Phase 4b sweep Item 4a: intra-crate calls
// via `mod demo` wrap).
// ====================================================================

proptest! {
    /// `use_mul2_add1(x, y) = mul2_add1(x) + y = (x + x + 1) + y`.
    /// Exercises the intra-crate-call path resolution via the
    /// per-fixture `mod demo` wrap.
    #[test]
    fn demo_use_mul2_add1_matches_model(x in any::<u32>(), y in any::<u32>()) {
        use aeneas_cert_differential::demo::{use_mul2_add1_ref, use_mul2_add1_model};
        prop_assert_eq!(use_mul2_add1_ref(x, y), use_mul2_add1_model(x, y));
    }

    /// `mod_add(x, y)` — Aeneas-style modular addition by 3329 via
    /// wrapping_sub + shift mask. Tests both the bit-shift emit
    /// (`>> 16i32` on `u32`) and a longer let-chain.
    #[test]
    fn demo_mod_add_matches_model(x in any::<u32>(), y in any::<u32>()) {
        use aeneas_cert_differential::demo::{mod_add_ref, mod_add_model};
        prop_assert_eq!(mod_add_ref(x, y), mod_add_model(x, y));
    }
}

// ====================================================================
// enums_basic.rs (Session 4 — newly unblocked by the RustEmit
// `Type.Ctor` → `Type::Ctor` path rewrite).
// ====================================================================

proptest! {
    /// `flip` round-trips through the 3-variant `Sign` enum. Property:
    /// `flip ∘ flip ∘ flip == flip` (only when the Zero-fixed-point
    /// is excluded; here we simply require ref ≡ model.
    #[test]
    fn enums_basic_flip_matches_model(v in 0u8..3) {
        use aeneas_cert_differential::enums_basic::{Sign, flip_ref, flip_model};
        let s = match v { 0 => Sign::Pos, 1 => Sign::Neg, _ => Sign::Zero };
        prop_assert_eq!(flip_ref(s), flip_model(s));
    }
}

// ====================================================================
// enums_payload.rs (Session 4 — payload-bearing match-arm + variant
// construction).
// ====================================================================

proptest! {
    #[test]
    fn enums_payload_value_matches_model(tag in 0u8..2, n in any::<u32>()) {
        use aeneas_cert_differential::enums_payload::{NumOrZero, value_ref, value_model};
        let x = if tag == 0 { NumOrZero::Num(n) } else { NumOrZero::Zero };
        prop_assert_eq!(value_ref(x), value_model(x));
    }

    #[test]
    fn enums_payload_wrap_matches_model(n in any::<u32>()) {
        use aeneas_cert_differential::enums_payload::{wrap_ref, wrap_model};
        prop_assert_eq!(wrap_ref(n), wrap_model(n));
    }

    #[test]
    fn enums_payload_zero_matches_model(_dummy in any::<u8>()) {
        use aeneas_cert_differential::enums_payload::{zero_ref, zero_model};
        prop_assert_eq!(zero_ref(), zero_model());
    }
}

// ====================================================================
// no_nested_borrows.rs (Session 6 — cast keyword + get_max fixes).
// ====================================================================

proptest! {
    /// `cast_u32_to_i32(x: u32) -> i32 { x as i32 }`. Wraps in two's
    /// complement when `x ≥ 0x80000000` — assert byte-identical
    /// output across the full u32 range.
    #[test]
    fn no_nested_borrows_cast_u32_to_i32_matches_model(x in any::<u32>()) {
        use aeneas_cert_differential::no_nested_borrows::{
            cast_u32_to_i32_ref, cast_u32_to_i32_model,
        };
        prop_assert_eq!(cast_u32_to_i32_ref(x), cast_u32_to_i32_model(x));
    }

    /// `cast_bool_to_i32(x: bool) -> i32 { x as i32 }`. Should
    /// produce 1 for true / 0 for false.
    #[test]
    fn no_nested_borrows_cast_bool_to_i32_matches_model(x in any::<bool>()) {
        use aeneas_cert_differential::no_nested_borrows::{
            cast_bool_to_i32_ref, cast_bool_to_i32_model,
        };
        prop_assert_eq!(cast_bool_to_i32_ref(x), cast_bool_to_i32_model(x));
    }

    /// `cast_bool_to_bool(x: bool) -> bool { x as bool }`. Identity
    /// — Charon's prepass elides this so the model emits bare `x`.
    #[test]
    fn no_nested_borrows_cast_bool_to_bool_matches_model(x in any::<bool>()) {
        use aeneas_cert_differential::no_nested_borrows::{
            cast_bool_to_bool_ref, cast_bool_to_bool_model,
        };
        prop_assert_eq!(cast_bool_to_bool_ref(x), cast_bool_to_bool_model(x));
    }

    /// `get_max(x, y) -> u32 { if x >= y then x else y }`. The
    /// pre-fix model emitted `if x { x } else { y }` (picked the
    /// first input param instead of the precomputed `t0 = (x >= y)`);
    /// the fix threads `lastWrite` into the cond surface form.
    #[test]
    fn no_nested_borrows_get_max_u32_matches_model(x in any::<u32>(), y in any::<u32>()) {
        use aeneas_cert_differential::no_nested_borrows::{
            get_max_ref, get_max_model,
        };
        prop_assert_eq!(get_max_ref(x, y), get_max_model(x, y));
    }

    /// Edge case for get_max: equal inputs (the boundary of `>=`).
    #[test]
    fn no_nested_borrows_get_max_u32_matches_model_equal(x in any::<u32>()) {
        use aeneas_cert_differential::no_nested_borrows::{
            get_max_ref, get_max_model,
        };
        prop_assert_eq!(get_max_ref(x, x), get_max_model(x, x));
    }
}
