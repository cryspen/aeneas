// Minimized repro (triaged). rustc --edition=2021 --crate-type=rlib
// -C overflow-checks=on accepts this.
//
// The SAME boolean local is asserted twice. This is the truly minimal form:
// no `&&`, no `!`, no shadowing, no second variable. Crashes both FORK and
// UPSTREAM aeneas:
//   [Error] There should be no bottoms in the value
//   Compiler source: interp/InterpExpressions.ml, line 55   (span = `b0` in the 2nd assert)
//
// Root cause: `eval_assertion` (InterpStatements.ml) evaluates the `move`
// operand once; the first assert concretizes b0 to `true`, so the SECOND assert
// takes the concrete-bool path and delegates to `eval_assertion_concrete`, which
// calls `eval_operand` AGAIN on the post-move context, reading the bottom the
// first move left behind. NEW bug, not F1-F6 / #22-#24. See verified.md.
//
// Distinguishing controls (see verified.md): `assert!(b0); assert!(b1);` with
// two DIFFERENT vars does NOT crash; `assert!(b0||b1)` twice does NOT crash.
pub fn f(b0: bool) {
    assert!(b0);
    assert!(b0);
}
