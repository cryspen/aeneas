# Verified triage: other-interpexpressions-55

## Verdict

- **VALID crash:** YES. rustc accepts `min.rs`; reproduces on fork AND upstream.
- **Classification: (A) REAL bug** — completeness/crash bug on trivially rustc-valid code.
- **Genuinely NEW:** YES. Not F1-F6, not cryspen/aeneas #22/#23/#24, not AeneasVerif#804.
- **Proposed severity:** MEDIUM (crash-on-valid-input / DoS-of-translation; no
  evidence of miscompilation, but it aborts the whole crate). Worth filing.

## Fingerprint (both toolchains)

- message: `There should be no bottoms in the value`
- fork:     `interp/InterpExpressions.ml:55` (`read_place_check`)
- upstream: `interp/InterpExpressions.ml:55` (same line)
- exit code 2, uncaught `Failure`.

## Minimized repro (final)

```rust
pub fn f(b0: bool) {
    assert!(b0);
    assert!(b0);
}
```

Two consecutive assertions of the SAME boolean local. No `&&`, `!`, shadowing,
or second variable is needed (the original seed `assert!(b0 && !b1)` twice was
not minimal).

## Root cause (file:line)

`eval_assertion` (`src/interp/InterpStatements.ml`, ~:152-168) evaluates the
assertion operand with `eval_operand` once (~:156). When the resulting value is
a **concrete** `VLiteral (VBool _)`, it delegates to `eval_assertion_concrete`
(:129-143) — which calls `eval_operand config span assertion.cond ctx` a
**second time** (:133), now on the post-first-eval context.

The Charon lowering of `assert!(x)` is `_t = copy x; assert(move _t == true)`,
so the operand is a `move`. The first `eval_operand` moves `_t` out, leaving the
place as ⊥ (bottom). The second `eval_operand` then re-reads the same `move`
place, and `read_place_check` (`InterpExpressions.ml:55`) fires its no-bottoms
`[%cassert]`.

Why it only triggers on the *second* assert of the same variable: the concrete
path is only taken when the boolean is already a known literal. On the first
`assert!(b0)`, `b0` is still a fresh symbolic value → the `VSymbolic` branch of
`eval_assertion` runs (no delegation, no double-eval). That first assert
expands `b0 ~~> true`, so on the second `assert!(b0)` the operand reads a
concrete `true` → concrete path → double-eval-of-move → ⊥ read → crash. The
crash span (col of `b0` in the 2nd assert) confirms it is the second read.

## Distinguishing controls (empirically verified on fork)

| program                                  | result                    |
|------------------------------------------|---------------------------|
| `assert!(b0);`                           | OK (symbolic, no delegate)|
| `assert!(b0); assert!(b0);`              | CRASH                     |
| `assert!(b0); assert!(b0); assert!(b0);` | CRASH                     |
| `assert!(b0); assert!(b1);` (2 vars)     | OK (b1 still symbolic)    |
| `assert!(b0); assert!(b1); assert!(b1);` | CRASH (b1 concrete on 3rd)|
| `assert!(b0 && b1); assert!(b0 && b1);`  | CRASH                     |
| `assert!(b0 || b1); assert!(b0 || b1);`  | OK (operand not a bare move of a re-concretized local) |
| `assert!(b0); let _q=b0; assert!(b0);`   | CRASH (adjacency irrelevant) |

## Upstream applicability

AFFECTED. Upstream `InterpStatements.ml` has the identical structure:
`eval_assertion_concrete` re-calls `eval_operand` at :133 and `eval_assertion`
pre-evaluates at :156. `min.rs` crashes upstream at the same `InterpExpressions.ml:55`.

## Fork-local-fix relevance

None. The fork's uncommitted edits are all in `Config.ml/Main.ml/Translate.ml/
pure/PureMicroPasses.ml` (pure-ir JSON dump + preserved-defs gating, inactive
without `-dump-pure-ir`). This crash is in the interpreter, before pure passes
run. Fork-induced: NO.

## Suggested fix (for the eventual issue)

Have `eval_assertion` pass the already-evaluated value/context into the concrete
branch instead of re-evaluating, or make `eval_assertion_concrete` take the
pre-read `v`/`ctx` as arguments (do not call `eval_operand` twice on a `move`).
