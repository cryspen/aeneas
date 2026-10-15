# signed-rem-min-overflow

## Summary

`iN::MIN % -1` panics in Rust (like `iN::MIN / -1`), but the models treated it
as a success returning `0` (fork PR #21). Fixed in the Lean model
(`IScalar.rem` and the `rem`/`checked_rem` specs), the F* and Coq
`scalar_rem` (Coq also gains the missing division-by-zero check), and the
interpreter's concrete evaluation. Suitable for upstream.

## Invariants

- Signed `rem` fails iff `y = 0 ∨ (x = MIN ∧ y = -1)`, consistently in Lean,
  F*, Coq and the interpreter; `checked_rem` returns `none` under exactly that
  condition; `MIN % 1 = 0`.

## Tests

- `#guard` vectors in `backends/lean/Aeneas/Std/Scalar/Ops/Rem.lean`.
- `assert_norm` checks in `backends/fstar/Primitives.fst`.
- `tests/src/rem-min-overflow.rs`: a known failure under `-test-units`; the
  concrete interpreter must panic on `MIN % -1` (`rem-min-overflow.lean.out`).
- `tests/src/rem-concrete.rs` (`tests/lean/RemConcrete.lean`): the
  non-overflowing cases (`MIN % 1`, `MIN % -2`, `(MIN + 1) % -1`, `-7 % 3`) do
  not panic under `-test-units`.

## Rebase notes

- The concrete interpreter (`-test-units`) is not used by any upstream test and
  fails on `assert!` ("There should be no bottoms in the value"), so the
  concrete tests only check whether evaluation panics.

- The test vectors are `#guard`s (upstream #1402); failures are checked with a
  local `panics` predicate since `RustM` has no `BEq`. `Ops/Rem.lean` needs
  `meta import Aeneas.Std.Scalar.Core` so that `#guard` can evaluate scalar
  operations under the module system.
- HOL4 has the same gap: the `iN_rem_def` definitions in
  `backends/hol4/primitivesScript.sml` only fail on `y = 0`. Left alone (not
  checked locally).

## History

- 2026-10-07: bootstrapped from fork PR #21; `#assert` replaced with `#guard`
  (upstream #1402).
