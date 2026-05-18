//! Differential property tests.
//!
//! For each function in the M8+ slice, generate random inputs, run
//! the reference function and the generated model, assert they agree.

use aeneas_cert_differential::{incr_model, incr_ref};
use aeneas_cert_differential::aggregates_basic::{mk_pair_ref, mk_pair_model, mk_tuple_ref, mk_tuple_model};
use aeneas_cert_differential::reborrows::{self, set_fst_ref, set_fst_model};
use proptest::prelude::*;

proptest! {
    #[test]
    fn incr_matches_model(x in any::<u32>()) {
        // M9.0c: param count now comes from the LLBC signature, so
        // `incr_model` has one param (matching `incr(x: &mut u32)`)
        // rather than the M7-era over-counted placeholder. Once M9.1
        // / M10 add binop and call hooks the *reference* side will
        // shift to `x.wrapping_add(1)` and exercise the full pipeline.
        prop_assert_eq!(incr_ref(x), incr_model(x));
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
