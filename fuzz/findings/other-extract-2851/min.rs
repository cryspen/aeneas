// NOT A CRASH (triaged). rustc --edition=2021 --crate-type=rlib
// -C overflow-checks=on accepts this.
//
// `str::chars().collect::<Vec<char>>()` makes aeneas emit a NON-fatal warning:
//   [Warn] When retrieving the builtin information for trait decl
//          'core::iter::traits::iterator::Iterator', could not find the
//          information for item 'collect'. ...
//   Compiler source: extract/Extract.ml, line 2851   (FORK; [%warn], not [%craise])
//   Compiler source: extract/Extract.ml, line 2868   (UPSTREAM)
// Translation then COMPLETES: exit 0, "Generated: .../Crate.lean" is emitted.
//
// The fuzzer harness mis-tagged this warning as a crash (its oracle keyed on the
// "Compiler source: ... line" marker, which [%warn] also prints). INVALID
// finding — no bug. See verified.md.
pub fn collect() {
    let s = "hello";
    let _chs: Vec<char> = s.chars().collect();
}
