# unreachable-interploops-407

## Fingerprint

- class: Unreachable
- site: interp/InterpLoops.ml:407
- message: Unreachable
- top frame: Aeneas__InterpAbs.merge_abs_conts_aux @ interp/InterpAbs.ml:1915

## Provenance / oracle

needs 2 functions together

## Triage (2026-07-26)

See `verified.md`. **Fingerprint mislabeled.** Pack bundles two things: (1) the
named `InterpLoops.ml:407` = **class B EXPECTED feature gate** ("(Infinite)
loops which do not contain breaks are not supported yet") from the infinite-loop
function; (2) the fatal uncaught exception is **F6** (`Unreachable`,
InterpAbs.ml:1671 = cryspen/aeneas#24) from the `mut a: &u32`-reassigned-before-loop
function. Verdict: **class B (gate) + class C (F6 dup)**; no new bug. `min.rs`
isolated to the InterpLoops:407 gate (`spin`). Harness note: `-abort-on-error`
turns feature gates into "crashes"; fingerprint on the exception backtrace, not
the last-printed `[Error]` line.
