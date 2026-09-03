# unreachable-interpexpressions-55

## Fingerprint

- class: Unreachable
- site: interp/InterpExpressions.ml:55
- message: Unreachable
- top frame: Aeneas__InterpAbs.merge_abs_conts_aux @ interp/InterpAbs.ml:1915

## Provenance / oracle

needs 2 functions together

## Triage (2026-07-26)

See `verified.md`. **Fingerprint mislabeled.** Pack bundles two independent
bugs; the fatal uncaught exception is **F6** (`Unreachable`, InterpAbs.ml:1671 =
cryspen/aeneas#24), triggered by the `mut a: &u32`-reassigned-before-loop
function. The `InterpExpressions.ml:55` in the label is a preceding NON-fatal
error from the pack's other function (the no-bottoms double-eval bug =
`../other-interpexpressions-55`). Verdict: **class C — DUPLICATE of F6**;
no new bug here. `min.rs` isolated to the F6 shape.
