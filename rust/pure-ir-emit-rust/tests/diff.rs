//! Differential proptest harness for the pure-ir-emit-rust pipeline.
//!
//! For each fixture in `tests/models/`, the corresponding model file is
//! a verbatim snapshot of the `pir2rs` emit at the `pre-extract` stage
//! (regenerate with `scripts/regen-diff-models.sh`). This harness:
//!
//!   1. `include!`s each `<fixture>_pir.rs` snapshot under a dedicated
//!      `models::<fixture>` module — the snapshot brings its own
//!      `aeneas_runtime` shim and `Result` alias, so the wrapping
//!      module gives them a private namespace.
//!   2. For each public function whose runtime path is free of
//!      `unimplemented!()` / `LoopOp placeholder` panics, runs a
//!      `proptest!` block: generates random scalar/ADT inputs, calls
//!      the R₀ wrapper from `ref_impl` and the R₂ emit from
//!      `models::<fixture>`, and asserts they agree.
//!
//! Conventions:
//!
//!   * Both sides return `Result<T, ()>` — the IR's `can_fail` monad
//!     surfaces as `checked_*` operations that can `Err` on overflow.
//!     We compare `Result<T>` values directly via `prop_assert_eq!`,
//!     including the `Err(())` branch.
//!
//!   * The emit's fn names carry a `<crate>_<fn>_<def_id>` suffix
//!     (e.g. `incr_cert_incr_0`). We address them by their full
//!     identifier at the call site so reshuffling def_ids is the only
//!     change needed to keep proptests pointing at the right fn.
//!
//!   * ADT R₀ types in `ref_impl` are *not* the same Rust type as the
//!     emit's `<crate>_<TypeName>_<id>` ADTs. Proptests compare them
//!     field-by-field after running both sides.
//!
//! Tests marked `#[ignore]` document concrete emitter limitations the
//! diff harness can't validate today; see the inline comments.

use proptest::prelude::*;

// `ref_impl` lives under `tests/common/` so cargo doesn't pick it up
// as its own (empty) test binary. The `#[path]` attribute lets us
// keep the symmetric `ref_impl::<fixture>::<fn>` call shape at the
// proptest call sites.
#[path = "common/ref_impl.rs"]
mod ref_impl;

// The model files carry the same `#![allow(...)]` set the emitter
// puts at the top of every `pir2rs` output (cleaned by
// `regen-diff-models.sh` so the inner-attr → outer-attr rewrite is
// handled here once, on the wrapping module).
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
    pub mod incr_cert {
        include!("models/incr_cert_pir.rs");
    }
    pub mod constants {
        include!("models/constants_pir.rs");
    }
    pub mod bitwise {
        include!("models/bitwise_pir.rs");
    }
    pub mod compare_simple {
        include!("models/compare_simple_pir.rs");
    }
    pub mod aggregates_basic {
        include!("models/aggregates_basic_pir.rs");
    }
    pub mod enums_basic {
        include!("models/enums_basic_pir.rs");
    }
    pub mod traits_basic {
        include!("models/traits_basic_pir.rs");
    }
    pub mod enums_payload {
        include!("models/enums_payload_pir.rs");
    }
    pub mod demo {
        include!("models/demo_pir.rs");
    }
}

// ====================================================================
// incr_cert.rs — 2 fn pairs
// ====================================================================

proptest! {
    /// `pub fn incr(x: &mut u32) { *x += 1; }` — IR functionalises
    /// the `&mut` and lowers `+= 1` to `checked_add(1).ok_or(())`.
    #[test]
    fn incr_cert_incr_diff(x in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::incr_cert::incr(x),
            models::incr_cert::incr_cert_incr_0(x),
        );
    }

    /// `pub fn incr_local(mut y: u32) -> u32`.
    #[test]
    fn incr_cert_incr_local_diff(y in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::incr_cert::incr_local(y),
            models::incr_cert::incr_cert_incr_local_1(y),
        );
    }
}

// ====================================================================
// constants.rs — 3 fn pairs covering scalar arith + tuple aggregate.
//
// The other `constants::*` items in the emit are either:
//   * non-fn globals (`X0` .. `S4`) whose runtime evaluation paths
//     hit `Err::<_,()>(())` placeholders for `Const` / `Global`
//     references the IR doesn't fully thread through pre-extract;
//   * const fns that take no args (`get_z1`, `unwrap_y`, ...) where
//     the model still reaches an opaque global stub at runtime.
//
// We restrict to the three fns whose runtime paths are entirely
// scalar-arithmetic.
// ====================================================================

proptest! {
    #[test]
    fn constants_incr_diff(n in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::constants::incr(n),
            models::constants::constants_incr_0(n),
        );
    }

    #[test]
    fn constants_mk_pair0_diff(x in any::<u32>(), y in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::constants::mk_pair0(x, y),
            models::constants::constants_mk_pair0_1(x, y),
        );
    }

    #[test]
    fn constants_add_diff(a in any::<i32>(), b in any::<i32>()) {
        prop_assert_eq!(
            ref_impl::constants::add(a, b),
            models::constants::constants_add_5(a, b),
        );
    }
}

// ====================================================================
// bitwise.rs — 5 fn pairs.
// ====================================================================

proptest! {
    #[test]
    fn bitwise_xor_u32_diff(a in any::<u32>(), b in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::bitwise::xor_u32(a, b),
            models::bitwise::bitwise_xor_u32_2(a, b),
        );
    }

    #[test]
    fn bitwise_or_u32_diff(a in any::<u32>(), b in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::bitwise::or_u32(a, b),
            models::bitwise::bitwise_or_u32_3(a, b),
        );
    }

    #[test]
    fn bitwise_and_u32_diff(a in any::<u32>(), b in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::bitwise::and_u32(a, b),
            models::bitwise::bitwise_and_u32_4(a, b),
        );
    }

    /// `a >> 16; t <<= 16; t` — shift amounts are constant 16, so
    /// neither `checked_shr` nor `checked_shl` ever returns None.
    #[test]
    fn bitwise_shift_u32_diff(a in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::bitwise::shift_u32(a),
            models::bitwise::bitwise_shift_u32_0(a),
        );
    }

    #[test]
    fn bitwise_shift_i32_diff(a in any::<i32>()) {
        prop_assert_eq!(
            ref_impl::bitwise::shift_i32(a),
            models::bitwise::bitwise_shift_i32_1(a),
        );
    }
}

// ====================================================================
// compare_simple.rs — 3 fn pairs. `add_u32` previously routed through
// an `unimplemented!()` opaque shim; Option A's route-shims pass
// rewrote `impl_core_num_wrapping_add_3` to call `u32::wrapping_add`,
// so the diff now runs.
// ====================================================================

proptest! {
    #[test]
    fn compare_simple_id_u32_diff(x in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::compare_simple::id_u32(x),
            models::compare_simple::compare_simple_id_u32_0(x),
        );
    }

    #[test]
    fn compare_simple_incr_val_diff(x in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::compare_simple::incr_val(x),
            models::compare_simple::compare_simple_incr_val_1(x),
        );
    }

    /// Previously `#[ignore]`d under "EMITTER GAP: routes through
    /// unimplemented!() opaque shim"; unblocked by the Option-A
    /// shim-routing pass.
    #[test]
    fn compare_simple_add_u32_diff(a in any::<u32>(), b in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::compare_simple::add_u32(a, b),
            models::compare_simple::compare_simple_add_u32_2(a, b),
        );
    }
}

// ====================================================================
// aggregates_basic.rs — 2 fn pairs.
//
// R₀'s `aggregates_basic::Pair` and R₂'s `aggregates_basic_Pair_0`
// are distinct Rust types; we compare them field-by-field.
// ====================================================================

proptest! {
    #[test]
    fn aggregates_basic_mk_tuple_diff(x in any::<u32>(), y in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::aggregates_basic::mk_tuple(x, y),
            models::aggregates_basic::aggregates_basic_mk_tuple_0(x, y),
        );
    }

    #[test]
    fn aggregates_basic_mk_pair_diff(x in any::<u32>(), y in any::<u32>()) {
        let r0 = ref_impl::aggregates_basic::mk_pair(x, y).expect("ref_impl Ok");
        let r2 = models::aggregates_basic::aggregates_basic_mk_pair_1(x, y)
            .expect("model Ok");
        prop_assert_eq!(r0.x, r2.x);
        prop_assert_eq!(r0.y, r2.y);
    }
}

// ====================================================================
// enums_basic.rs — 1 fn pair.
//
// R₀'s `Sign` and R₂'s `enums_basic_Sign_0` are distinct types; we
// pivot through a `u8` discriminant for comparison.
// ====================================================================

proptest! {
    #[test]
    fn enums_basic_flip_diff(v in 0u8..3) {
        use ref_impl::enums_basic::Sign as RSign;
        use models::enums_basic::enums_basic_Sign_0 as MSign;

        let (r_in, m_in) = match v {
            0 => (RSign::Pos, MSign::Pos),
            1 => (RSign::Neg, MSign::Neg),
            _ => (RSign::Zero, MSign::Zero),
        };

        let r_tag = match ref_impl::enums_basic::flip(r_in).expect("ref Ok") {
            RSign::Pos => 0u8,
            RSign::Neg => 1u8,
            RSign::Zero => 2u8,
        };
        let m_tag = match models::enums_basic::enums_basic_flip_0(m_in)
            .expect("model Ok")
        {
            MSign::Pos => 0u8,
            MSign::Neg => 1u8,
            MSign::Zero => 2u8,
        };
        prop_assert_eq!(r_tag, m_tag);
    }
}

// ====================================================================
// traits_basic.rs — 1 fn pair.
//
// The emit recovers the impl-method dispatch (`Tag::value()` → 42)
// directly; the runtime path doesn't touch any `unimplemented!()`
// shim.
// ====================================================================

proptest! {
    #[test]
    fn traits_basic_use_numeric_diff(_dummy in any::<u8>()) {
        let r0 = ref_impl::traits_basic::use_numeric(ref_impl::traits_basic::Tag);
        let r2 = models::traits_basic::traits_basic_use_numeric_0(
            models::traits_basic::traits_basic_Tag_0,
        );
        prop_assert_eq!(r0, r2);
    }
}

// ====================================================================
// enums_payload.rs — 3 fn pairs.
//
// Same R₀/R₂-distinct-types pivot as `enums_basic` — we tag through
// (u8, u32) so the value-carrying variant survives the cross-type
// comparison.
// ====================================================================

proptest! {
    #[test]
    fn enums_payload_value_diff(tag in 0u8..2, n in any::<u32>()) {
        use ref_impl::enums_payload::NumOrZero as RN;
        use models::enums_payload::enums_payload_NumOrZero_0 as MN;
        let (r_in, m_in) = if tag == 0 {
            (RN::Num(n), MN::Num(n))
        } else {
            (RN::Zero, MN::Zero)
        };
        prop_assert_eq!(
            ref_impl::enums_payload::value(r_in),
            models::enums_payload::enums_payload_value_0(m_in),
        );
    }

    #[test]
    fn enums_payload_wrap_diff(n in any::<u32>()) {
        use ref_impl::enums_payload::NumOrZero as RN;
        use models::enums_payload::enums_payload_NumOrZero_0 as MN;
        let r = ref_impl::enums_payload::wrap(n).expect("ref Ok");
        let m = models::enums_payload::enums_payload_wrap_1(n).expect("model Ok");
        let (r_tag, r_val) = match r { RN::Num(v) => (0u8, v), RN::Zero => (1u8, 0u32) };
        let (m_tag, m_val) = match m { MN::Num(v) => (0u8, v), MN::Zero => (1u8, 0u32) };
        prop_assert_eq!(r_tag, m_tag);
        prop_assert_eq!(r_val, m_val);
    }

    #[test]
    fn enums_payload_zero_diff(_dummy in any::<u8>()) {
        use ref_impl::enums_payload::NumOrZero as RN;
        use models::enums_payload::enums_payload_NumOrZero_0 as MN;
        let r = ref_impl::enums_payload::zero().expect("ref Ok");
        let m = models::enums_payload::enums_payload_zero_2().expect("model Ok");
        let r_tag = match r { RN::Num(_) => 0u8, RN::Zero => 1u8 };
        let m_tag = match m { MN::Num(_) => 0u8, MN::Zero => 1u8 };
        prop_assert_eq!(r_tag, m_tag);
    }
}

// ====================================================================
// demo.rs — 3 fn pairs (scalar arithmetic helpers).
//
// The full `demo` fixture has 13+ items; many use closures, recursive
// ADTs, or `wrapping_*` trait-method calls that still go through the
// emitter's `unimplemented!()` opaque shims. The scalar helpers
// covered here exercise let-chained `checked_add` lowering and
// intra-crate calls (`use_mul2_add1` → `mul2_add1`).
// ====================================================================

proptest! {
    #[test]
    fn demo_mul2_add1_diff(x in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::demo::mul2_add1(x),
            models::demo::demo_mul2_add1_1(x),
        );
    }

    #[test]
    fn demo_use_mul2_add1_diff(x in any::<u32>(), y in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::demo::use_mul2_add1(x, y),
            models::demo::demo_use_mul2_add1_2(x, y),
        );
    }

    #[test]
    fn demo_incr_diff(x in any::<u32>()) {
        prop_assert_eq!(
            ref_impl::demo::incr(x),
            models::demo::demo_incr_3(x),
        );
    }
}

// Previously `#[ignore]`d under "EMITTER GAP: demo_mod_add routes
// through unimplemented!() wrapping_* shims". The Option-A
// shim-routing pass rewrote `impl_core_num_wrapping_{add,sub}_*`
// in the demo model so `demo_mod_add_*` is now executable.
proptest! {
    #[test]
    fn demo_mod_add_diff(a in 0u32..3329, b in 0u32..3329) {
        prop_assert_eq!(
            ref_impl::demo::mod_add(a, b),
            models::demo::demo_mod_add_11(a, b),
        );
    }
}

// EMITTER GAP: `demo::i32_id` is structurally a recursive identity
// function (`if i == 0 { 0 } else { i32_id(i - 1) + 1 }`). The R₂
// emit replicates the recursion faithfully but would diverge /
// stack-overflow for large positive inputs and return `Err(())` for
// negative inputs (via `checked_sub`). The diff is sound but
// untestable as a uniform `any::<i32>()` proptest without bounding
// the depth.
#[test]
#[ignore = "DIFF NON-UNIFORM: demo_i32_id recursion depth bounded by input"]
fn demo_i32_id_diff_ignored() {}
