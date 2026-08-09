// Controls isolating the trigger (empirically verified on the fork binary).
// Compile each `pub fn` in its own crate to observe: single/distinct-operand
// asserts translate fine (exit 0); a second assert of an already-concretized
// operand crashes (exit 2, InterpExpressions.ml:55).

// OK — one assert: b0 is still symbolic, symbolic branch, no delegation.
pub fn ok_single(b0: bool) { assert!(b0); }

// OK — two DISTINCT operands: b1 is still symbolic at its only assert.
pub fn ok_distinct(b0: bool, b1: bool) { assert!(b0); assert!(b1); }

// CRASH — second assert of b0: first assert expands b0 ~~> true, so the second
// takes the concrete path and re-evaluates the `move` operand → reads ⊥.
pub fn crash_same(b0: bool) { assert!(b0); assert!(b0); }

// CRASH — same effect for a re-asserted second variable.
pub fn crash_second_var(b0: bool, b1: bool) { assert!(b0); assert!(b1); assert!(b1); }
