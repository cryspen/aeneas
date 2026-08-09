// Minimized repro (triaged). rustc --edition=2021 --crate-type=rlib
// -C overflow-checks=on accepts this (the loop diverges: `!` coerces to `u32`).
//
// This isolates the function that produces the NAMED fingerprint,
// InterpLoops.ml:407 — an infinite loop with no `break` and no `return`:
//   [Error] (Infinite) loops which do not contain breaks are not supported yet
//   Compiler source: interp/InterpLoops.ml, line 407   ([%craise], FORK)
//   Compiler source: interp/InterpLoops.ml, line 411   (UPSTREAM)
//
// This is an EXPECTED feature-gate rejection (class B): the message literally
// says "not supported yet". It only LOOKS like a crash because -abort-on-error
// turns the craise into an uncaught exception + backtrace.
//
// NOTE on the original pack: it also bundled the F6 shared-borrow loop, whose
// "Unreachable" / InterpAbs.ml:1671 crash was the actual uncaught exception
// (the fatal one). See ../unreachable-interpexpressions-55 for the F6 case.
pub fn spin(p: &mut u32) {
    loop {
        *p = (*p).wrapping_add(1);
    }
}
