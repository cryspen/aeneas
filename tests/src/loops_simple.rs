//! M12.0 cert fixture: a minimal counter loop.
//!
//! [count_to] exercises the [eval_loop_symbolic] hook point in
//! `src/interp/InterpLoops.ml`: a single `while`, no nested loops, no
//! mutable borrows surviving across iterations, no calls. The OCaml
//! symbolic interpreter computes a fixed-point for this trivially and
//! emits exactly one [EvLoopInv] event per call.
//!
//! M12.1 (next milestone) will consume the [EvLoopInv] summary in the
//! Lean translator to emit a `partial_fixpoint` Lean definition; for
//! now the Lean side accepts the event structurally as a no-op.

pub fn count_to(n: u32) -> u32 {
    let mut i: u32 = 0;
    while i < n {
        i = i + 1;
    }
    i
}
