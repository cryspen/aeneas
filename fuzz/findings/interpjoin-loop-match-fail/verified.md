# Two sequential loops with an early return crash the loop fixed-point join

## Summary

Translating a function that runs **two sequential `while let` loops** over a
mutable-borrow iterator, where the **first** loop contains an early `return`,
aborts translation with an uncaught internal error:

```
[Error] Could not match the contexts
Compiler source: interp/InterpJoin.ml, line 1515   (fork; upstream: line 1542)
```

Minimal reproducer (`min.rs`, valid Rust — `rustc --edition=2021 -C overflow-checks=on` accepts it):

```rust
pub struct IterMut<'a> { v: Option<&'a mut i32> }
impl<'a> IterMut<'a> {
    fn next(&mut self) -> Option<&'a mut i32> {
        core::mem::replace(&mut self.v, None)
    }
}
pub fn drain_twice(mut it: IterMut<'_>, stop: bool) {
    while let Some(_) = it.next() {
        if stop { return; }
    }
    while let Some(_) = it.next() {}
}
```

## Classification

**Class A — genuine completeness bug (translator crash on valid Rust).**

Justification:
- `rustc` accepts the input (only unused-var warnings); it is well-typed and
  borrow-checks.
- The failure is an **uncaught OCaml `Failure`** (exit 2, full backtrace), not a
  clean feature-gate rejection. The message `Could not match the contexts` is
  **not** in `fuzz/harness/data/expected_reject_patterns.txt` and is not a
  `not supported yet` gate. So it is not Class B.
- Fingerprint `interp/InterpJoin.ml:1515` is not present in the findings DB
  (nearest DB sites: `InterpAbs.ml:1671` F6, `PureMicroPassesLoops.ml:1818` F4)
  — not Class C.
- Early-returns-inside-a-single-loop **are** supported (control S1 below
  translates fine), so this is not the "Early returns inside of loops are not
  supported yet" gate — it is a real fixed-point-join defect for the
  two-sequential-loops shape.

## Upstream status

Reproduces on **both** targets:
- fork (charon v0.1.196, aeneas `6a3fc35b-dirty`): `InterpJoin.ml:1515`
- upstream (aeneas `main` 3a8586fa, charon v0.1.225): `InterpJoin.ml:1542`

Same function (`match_ctx_with_target`), same message; the line number differs
only by source drift. **This is an upstream bug too and is filable upstream.**

## Root cause (file:line)

Fatal craise: `src/interp/InterpJoin.ml:1515` (upstream `:1542`), function
`match_ctx_with_target`:

```ocaml
match
  try_match_ctxs span ~check_equiv:false ~check_kind:false
    ~check_can_end:false fixed_ids lookup_in_src lookup_in_joined src_ctx
    joined_ctx
with
| Some ctx -> ctx
| None -> [%craise] span "Could not match the contexts"   (* <-- here *)
```

Reached via the loop fixed-point machinery (backtrace):
`Interp.evaluate_function_symbolic`
→ `InterpLoops.eval_loop` / `eval_loop_symbolic`
→ `InterpLoopsFixedPoint.compute_loop_entry_fixed_point`
→ (and later) `InterpLoops.eval_loop_symbolic_apply_loop` (InterpLoops.ml:117-118)
→ `InterpJoin.match_ctx_with_target`.

The early `return` out of the first borrow-carrying loop leaves a live region
abstraction in the context. When the **second** loop's entry context is matched
back against its computed fixed point (`match_ctx_with_target`),
`try_match_ctxs` cannot reconcile the two context shapes and returns `None`,
tripping the craise. The isolation controls show the mutable borrow in the
first loop is the essential ingredient; the second loop can be *anything*
(even a plain integer counter).

## Controls (verified on fork)

| program shape | verdict |
|---|---|
| single `while let` loop with early `return` (S1) | OK |
| two loops, **no** early return (A) | OK |
| one loop *inside* an outer `loop`, with early return (B) | OK |
| two loops, **first** has early `return` (min.rs / E) | **CRASH** InterpJoin:1515 |
| early `return` in the **second** loop instead (G) | OK |
| both loops over a **value** iterator `Option<i32>` (F) | OK (mut borrow needed) |
| first loop = mut-borrow+early-return, second loop = plain `while i<n` counter (S4) | **CRASH** InterpJoin:1515 |

### Sibling fingerprints (same trigger family)

The underlying defect — the loop fixed-point / region-abstraction machinery
cannot reconcile the contexts when **two sequential loops both consume a
mutable-borrow iterator and the first loop exits early** — surfaces at several
distinct craise sites depending on the early-exit kind and the borrow encoding.
Likely the same root cause; flagged for human review:

| variant | fork site | upstream site |
|---|---|---|
| struct `IterMut`, first loop `return` (min.rs) | `InterpJoin.ml:1515` "Could not match the contexts" | `InterpJoin.ml:1542` (crash) |
| struct `IterMut`, first loop `break` (control S2) | `InterpAbs.ml:2169` "Internal error, please file an issue" | `InterpAbs.ml:2188` (crash) |
| inline `Option<&mut i32>` + `mem::replace`, first loop `return` (control M1) | `SymbolicToPureAbs.ml:353` "Unreachable" | success (fork-only) |

Two of the three variants (return / break) reproduce on **both** targets;
`InterpAbs.ml:2169/2188` is a distinct fingerprint from F6 (`InterpAbs.ml:1671/1688`,
`Unreachable`) and from F4 (`PureMicroPassesLoops.ml:1818`).

## Severity

**MEDIUM.** Valid, realistic Rust (iterate-with-early-exit then iterate again)
hard-crashes translation and aborts the whole crate. Requires a specific but
natural CFG (two sequential loops, early return in the first, mutable borrow).

## Provenance

Found by the Aeneas fuzzing harness (`fuzz/`), fork Wave A, seed 21, source-level
mutation of `tests/src/iterators.rs`/`loops.rs`-style iterators
(`EarlyReturnInLoop` + `WrapLoopBreak` mutations), auto-bisected to 2 functions
then hand-minimized to the single function above. Harness auto-recorded slug
`unreachable-interpjoin-1515` (the `Unreachable` class label there is a
fingerprint artifact of the multi-error pack; the true message is
`Could not match the contexts`).

## CORRECTION (coordinator dedup, 2026-07-26): DUPLICATE of upstream #930

This is **not** a new bug. It matches open upstream issue
**AeneasVerif/aeneas#930** ("Could not match the contexts"), whose reproducer is
a loop with an early `return` followed by more code, crashing at the exact same
`interp/InterpJoin.ml:1515`. The `break`-variant sibling documented above matches
**#1206** ("`for` loop with conditional `break` and code after it",
`InterpJoin.ml:1542`). N2's essential shape (loop with early exit + code after,
in the loop-fixed-point context matcher) is the same root cause.

**Disposition:** duplicate of #930/#1206; do NOT file. Kept as an
independently-discovered reproducer and a regression test for once #930 is fixed.
The fork inherits the bug (present in both toolchains).
