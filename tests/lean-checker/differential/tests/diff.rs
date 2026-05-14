//! Differential property tests.
//!
//! For each function in the M8 slice, generate random inputs, run
//! the reference function and the generated model, assert they agree.

use aeneas_cert_differential::{incr_model, incr_ref};
use proptest::prelude::*;

proptest! {
    #[test]
    fn incr_matches_model(x in any::<u32>()) {
        // The generated model has 2 params (a quirk of the M7
        // placeholder param-count heuristic); we pass `x` twice so
        // the test still exercises a meaningful comparison.
        prop_assert_eq!(incr_ref(x), incr_model(x, x));
    }
}
