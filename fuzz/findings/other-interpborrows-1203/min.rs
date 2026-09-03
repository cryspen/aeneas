// Minimized repro (triaged). rustc --edition=2021 --crate-type=rlib
// -C overflow-checks=on accepts this.
//
// A closure that returns references derived from its captured state, built via
// std::array::from_fn. On the FORK toolchain (charon v0.1.196) aeneas crashes
// during backward symbolic evaluation:
//   [Error] Can't end abstraction N as it is set as non-endable
//   Compiler source: interp/InterpBorrows.ml, line 1203
// The closure is essential: a manual `[&s[0]]` (see verified.md) does NOT crash.
// This is a manifestation of AeneasVerif/aeneas#804 (the fuzz seed is exactly
// that regression test, which is `//@ [!lean] skip`-listed). Does NOT reproduce
// on current upstream (charon v0.1.225), which axiomatizes `array::from_fn`.
pub fn each_ref(s: &[u8; 1]) -> [&u8; 1] {
    std::array::from_fn(|i| &s[i])
}
