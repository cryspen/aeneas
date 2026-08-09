# Verified triage: unreachable-interploops-407

## Verdict

- **VALID crash:** YES (rustc accepts the pack). Like unreachable-interpexpressions-55,
  the **fingerprint is mislabeled** and the pack bundles TWO independent things.
- **Named site `InterpLoops.ml:407`: (B) EXPECTED feature-gate rejection** —
  "(Infinite) loops which do not contain breaks are not supported yet".
- **Fatal (uncaught) crash: (C) DUPLICATE of F6 (cryspen/aeneas#24)** —
  `Unreachable` at `InterpAbs.ml:1671`.
- **Genuinely NEW:** NO.
- **Proposed severity:** the InterpLoops:407 part is not a bug (intended gate);
  the fatal part folds into F6 (#24). Main actionable takeaway is a HARNESS note
  (see below), owned by another agent.

## Why the fingerprint is wrong

Two functions in the pack:
1. `f_0_ignore_input_mut_borrow` (`mut a: &u32` reassigned before a loop) →
   **fatal uncaught exception** `[Error] Unreachable`, `InterpAbs.ml:1671` = F6.
2. `f_1_inner_mut_swap` (`loop { if *py>0 {} *py = ...; }`, no break/return) →
   `[Error] (Infinite) loops which do not contain breaks are not supported yet`,
   `InterpLoops.ml:407`.

The oracle keyed the file:line on the InterpLoops:407 message but took the
top-frame from the F6 exception. Isolated, `f_1_inner_mut_swap` fatally craises
at InterpLoops:407; `f_0_ignore_input_mut_borrow` fatally craises at F6.

## Minimized repro (final = the NAMED InterpLoops:407 case)

```rust
pub fn spin(p: &mut u32) {
    loop {
        *p = (*p).wrapping_add(1);
    }
}
```

Reproduces `(Infinite) loops which do not contain breaks are not supported yet`,
`InterpLoops.ml:407` (fork) / `:411` (upstream). rustc accepts it (the loop
diverges; `!` coerces to the `()` return).

For the fatal F6 case, see ../unreachable-interpexpressions-55/min.rs (identical
`reassign-shared-before-loop` shape).

## Root cause (file:line)

`InterpLoops.ml:407`: `[%craise] span "(Infinite) loops which do not contain
breaks are not supported yet"` in the `NoBreak` arm of the loop fixed-point
`break_info` match. This is a deliberate, documented feature gate — Aeneas does
not yet translate loops that never break/return. NOT a soundness or correctness
defect. It surfaces as a "crash" (uncaught exception + backtrace) only because
`-abort-on-error` promotes the `[%craise]` immediately instead of accumulating it.

## Harness note (for the fuzz-harness owner — not fixed here)

`-abort-on-error` turns EVERY `[%craise]` feature-gate into an uncaught
`Failure`, so class-B "unsupported construct" rejections are indistinguishable
from class-A internal crashes at the process level. The oracle should either (a)
run without `-abort-on-error` and treat `[%craise]` with a "not supported"/"not
yet" message text as an expected rejection, or (b) maintain a message allowlist.
It should also fingerprint on the **exception backtrace top frame**, not the
last-printed `[Error] ... Compiler source:` line (which caused the two
`unreachable-*` mislabels).

## Upstream applicability

AFFECTED identically (both the feature gate at InterpLoops:411 and F6 at
InterpAbs:1688 reproduce upstream). Neither is fork-induced.
