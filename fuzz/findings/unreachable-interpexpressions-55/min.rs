// Minimized repro (triaged). rustc --edition=2021 --crate-type=rlib
// -C overflow-checks=on accepts this.
//
// The original fuzz pack bundled TWO independent functions and its fingerprint
// was MISLABELED: the file:line `InterpExpressions.ml:55` came from a preceding
// NON-fatal [Error], while the actual uncaught exception was F6:
//   [Error] Unreachable
//   Compiler source: interp/InterpAbs.ml, line 1671   (merge_abs_conts_aux)
//
// This minimization isolates the function that produces that FATAL crash: a
// shared reference parameter reassigned before a loop. It is a DUPLICATE of F6
// (cryspen/aeneas#24) — the inverted `can_end` guard in eliminate_shared_loans.
// Crashes on both FORK (InterpAbs.ml:1671) and UPSTREAM (InterpAbs.ml:1688).
//
// The pack's OTHER function (`let y = if b {1} else {panic!()}` duplicated) is
// the separate no-bottoms double-eval bug — see ../other-interpexpressions-55.
pub fn reassign_shared_before_loop<'a>(mut a: &'a u32, y: &'a u32) -> u32 {
    let mut s = *a;
    a = y;
    let mut i = 0u32;
    loop {
        s = s.wrapping_add(*a);
        i = i.wrapping_add(1);
        if i > 10 {
            return s;
        }
    }
}
