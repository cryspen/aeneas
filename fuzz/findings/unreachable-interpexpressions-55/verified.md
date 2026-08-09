# Verified triage: unreachable-interpexpressions-55

## Verdict

- **VALID crash:** YES (rustc accepts the pack). But the finding's **fingerprint
  is mislabeled** and the pack bundles TWO independent bugs.
- **Fatal (uncaught) crash: (C) DUPLICATE of F6 (cryspen/aeneas#24)** —
  `Unreachable` at `InterpAbs.ml:1671` (`merge_abs_conts_aux`).
- **Also contains: (A)** the no-bottoms double-eval bug — the `InterpExpressions.ml:55`
  file:line the fingerprint keyed on — which is a DUPLICATE of
  `../other-interpexpressions-55` (the genuinely-new bug).
- **Genuinely NEW:** NO (fatal crash is F6; the class-A part is tracked under
  other-interpexpressions-55).
- **Proposed severity:** dedup → folds into F6 (#24, already filed) +
  other-interpexpressions-55.

## Why the fingerprint is wrong

The original pack has two functions:
1. `f_0_opt_add_1_or_panic` (`let y = if b {1} else {panic!()}` duplicated) →
   prints a **non-fatal** `[Error] There should be no bottoms in the value`,
   `InterpExpressions.ml:55`. Isolated, it is the same double-eval-of-`move`
   no-bottoms bug as other-interpexpressions-55 (verified: isolating it crashes
   at InterpExpressions.ml:55).
2. `f_1_ignore_input_shared_borrow` (`mut a: &u32` reassigned before a loop) →
   the **fatal uncaught exception** `[Error] Unreachable`, `InterpAbs.ml:1671`.

The fuzzer's oracle took the file:line from the last-printed `[Error]` (case 1)
but the top-frame/backtrace from the actual exception (case 2) — hence the
inconsistent `Unreachable interp/InterpExpressions.ml:55` label with a
`merge_abs_conts_aux @ InterpAbs.ml:1915` top frame.

## Minimized repro (final = the fatal F6 case)

```rust
pub fn reassign_shared_before_loop<'a>(mut a: &'a u32, y: &'a u32) -> u32 {
    let mut s = *a;
    a = y;
    let mut i = 0u32;
    loop {
        s = s.wrapping_add(*a);
        i = i.wrapping_add(1);
        if i > 10 { return s; }
    }
}
```

Isolated, this reproduces the fatal `Unreachable` / `InterpAbs.ml:1671` on the
fork and `InterpAbs.ml:1688` on upstream (line shift only).

## Root cause (file:line) — F6

Inverted `can_end` guard in `eliminate_shared_loans`
(`InterpReduceCollapse.ml:44-46`): the comment says "only update the non-frozen
abstractions" but the code is `if not abs.can_end then update … else abs`, i.e.
it mutates exactly the frozen (`SynthInput`/`FunCall`) abstractions and skips the
endable ones. Reassigning `a` before the loop leaves a matchless shared loan in
the frozen input abstraction; the fixed-point join/collapse
(`collapse_ctx` -> `merge_abstractions` -> `merge_abs_conts_aux`) then hits the
`Unreachable` sanity check. See documentation/translation-study/06-bug-hunt-findings.md,
section F6, and cryspen/aeneas#24 / upstream-repros/f6-inverted-guard.

## Upstream applicability

AFFECTED (F6 predates the Interpreter*→Interp* rename; already filed as an
upstream bug). Confirmed here: upstream crashes at `InterpAbs.ml:1688`.

## Fork-local-fix relevance

None (interpreter-level; fork edits are pure-ir/driver only).
