//! Differential property tests.
//!
//! For each function in the M8 slice, generate random inputs, run
//! the reference function and the generated model, assert they agree.

use aeneas_cert_differential::{incr_model, incr_ref};
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
}
