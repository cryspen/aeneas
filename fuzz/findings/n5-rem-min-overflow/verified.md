# N5 — SOUNDNESS: `iN::MIN % -1` modeled as `0` but panics in Rust

**Severity: HIGH (unsoundness / miscompilation).** Not a crash, but a *wrong
model*: Aeneas translates `iN::MIN % -1` to a value of `0`, whereas the Rust
program **panics** with "attempt to calculate the remainder with overflow". A
Lean/F*/Coq proof about the translation could therefore rely on `MIN % -1 = 0`,
which is false — the translation is unsound for this input.

## Provenance — NOT a campaign discovery

N5 was found by **prior manual auditing** (Karthik, 2026-07-22) and is already
fixed/filed as **cryspen/aeneas PR #21** (`fix/rem-min-overflow`), which predates
this fuzzing campaign (2026-07-26). It is recorded here as an **oracle-validation
datapoint**: the Phase-2 semantic differential independently reproduces it (see
below), demonstrating that the native-vs-Lean oracle catches this soundness
class — the analogue of F4/F6 rediscovery validating the crash oracle. The
campaign did **not** discover this bug.

## Independent reproduction by the semantic differential

The **Phase-2 semantic differential** (native execution vs Lean `#eval`), on a
targeted closed `test_*` crate. Native ground truth is compiled with
`-C overflow-checks=on`, so `x % y` traps; the Lean model evaluates it to
`ok 0`. Verified end-to-end firsthand (`aeneas-fuzz semdiff`):

```
MISMATCH test_rem_min: native={"kind":"integerOverflow",
  "msg":"attempt to calculate the remainder with overflow","status":"PANIC"}
  lean=OK
MATCH    test_rem_ok  (control: 17 % 5 == 2)
```

(`semdiff-native.json`, `semdiff-verdicts.json`, `semdiff-lean.txt`.)

## Reproducer (`min.rs`)

```rust
pub fn test_rem_min() {
    let x: i32 = i32::MIN;
    let y: i32 = -1;
    let r = x % y;        // Rust: PANIC (overflow). Aeneas model: 0.
    assert!(r == 0);
}
```

Same as `iN::MIN / -1` (which Aeneas *does* handle) — but the remainder path
was missing the check. `iN::MIN.checked_rem(-1)` returns `None` in Rust; the
model returned `Some 0`.

## Root cause

The result of `MIN % -1` is `0`, which **is representable**, so the generic
range check in `mk_scalar` that catches the *division* overflow never fires for
the remainder. Every layer that models `Rem` shares the omission:

- Interpreter concrete eval: `src/interp/InterpExpressions.ml`, `Rem OPanic`
  only guarded `sv2_value = Z.zero` (divide-by-zero), not `MIN % -1`.
- Backend models: `backends/lean/Aeneas/Std/Scalar/Ops/Rem.lean`
  (`IScalar.rem`), `backends/lean/.../CheckedOps/Rem.lean`,
  `backends/fstar/Primitives.fst` (`scalar_rem`), `backends/coq/Primitives.v`
  (which additionally returned `Ok x` for `x % 0`).

## Scope

Affects the interpreter **and all three backends**, on **both targets** (the
fix's parent is upstream `004e11fe`, i.e. the bug predates the fork and is
present in upstream `main`). Not fork-specific.

## Fix

A fix exists on branch **`fix/rem-min-overflow`** (worktree
`/private/tmp/aeneas-rem-fix`, commit `75f59901`): add the `MIN % -1` overflow
disjunct to the interpreter's `Rem OPanic` and to `IScalar.rem`/`scalar_rem`
across Lean/F*/Coq (mirroring the existing `div` check), extend the
`checked_rem` specs with the overflow disjunct, add regression tests (Coq also
gains the missing `% 0` check). After the fix, `test_rem_min` MATCHes (both
sides panic/`fail integerOverflow`).

## Disposition

Known soundness bug (prior audit), both targets + all backends. Already fixed
and filed as **cryspen/aeneas PR #21** (`fix/rem-min-overflow`) — no new action
from the campaign; land that PR (the fix also applies upstream). Recorded here
only as an oracle-validation datapoint.
