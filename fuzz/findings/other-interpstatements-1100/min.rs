// Minimal reproducer: matching on a `char` crashes aeneas.
//
// Matching a CONCRETE `char` literal aborts translation with
//   [Error] Inconsistent state   (interp/InterpStatements.ml, eval_switch_raw)
// on rustc-valid code in the safe supported subset.
//
// (A SYMBOLIC char match — e.g. `fn g(ch: char) { match ch { 'a' => 1, _ => 2 } }`
//  — crashes too, but with a different message: `(Failure Unexpected)` from
//  Charon__ValuesUtils.literal_as_scalar via eval_switch_raw at
//  InterpStatements.ml:1064. See observed-output-symbolic.txt. Root cause: the
//  switch evaluator treats the char scrutinee as a scalar.)
pub fn f() -> u32 {
    let ch: char = 'g';
    match ch {
        'a' => 1,
        'g' => 2,
        _ => 3,
    }
}
