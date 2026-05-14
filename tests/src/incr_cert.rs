//! Minimal fixture for the aeneas-lean-checker vertical slice (M3-M8).
//!
//! [incr] is the canonical direct-borrow example used in the LLBC# papers.
//! [incr_local] takes a value, creates the borrow in-body, and exercises
//! `eval_rvalue_ref` directly — useful when sanity-checking M3 cert hooks.

pub fn incr(x: &mut u32) {
    *x += 1;
}

pub fn incr_local(mut y: u32) -> u32 {
    let r: &mut u32 = &mut y;
    *r += 1;
    y
}
