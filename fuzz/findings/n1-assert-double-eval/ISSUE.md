# Translating two `assert!` of the same boolean crashes with "There should be no bottoms in the value"

## Summary

Translating a function that asserts the *same* boolean local twice aborts with an
uncaught internal error, killing translation of the whole crate. The input is
valid Rust (rustc accepts it, `bool` is `Copy`).

```rust
pub fn f(b0: bool) {
    assert!(b0);
    assert!(b0);
}
```

- **Observed:** `[Error] There should be no bottoms in the value`,
  `Compiler source: interp/InterpExpressions.ml, line 55`, exit code 2, uncaught
  `Failure`.
- **Expected:** successful translation (the function is well-typed and
  borrow-checks; a single `assert!(b0)`, or two asserts of *distinct* operands,
  both translate fine).

Reproduces on both charon v0.1.196 and current `main` (charon v0.1.225) at
`interp/InterpExpressions.ml:55`.

## Root cause

`eval_assertion` (`src/interp/InterpStatements.ml`) evaluates the assertion
condition with `eval_operand` once; when the value is a **concrete**
`VLiteral (VBool _)` it delegates to `eval_assertion_concrete`, which calls
`eval_operand` on the same condition **a second time**:

```ocaml
let eval_assertion_concrete config span assertion : st_cm_fun =
 fun ctx ->
  let v, ctx, eval_op = eval_operand config span assertion.cond ctx in   (* 2nd eval *)
  ...

let eval_assertion config span assertion : st_cm_fun =
 fun ctx ->
  let v, ctx, cf_eval_op = eval_operand config span assertion.cond ctx in (* 1st eval *)
  match v.value with
  | VLiteral (VBool _) -> eval_assertion_concrete config span assertion ctx  (* re-evals *)
  | VSymbolic sv -> ...
```

Charon lowers `assert!(x)` to `_t = copy x; assert(move _t)`, so the condition
operand is a **move**. The first `eval_operand` moves `_t` out, leaving ⊥ in its
place; the second `eval_operand` re-reads that place and `read_place_check`
(`InterpExpressions.ml:55`) fires its no-bottoms `[%cassert]`.

Why it needs the *second* assert of the same local: on the first `assert!(b0)`,
`b0` is still symbolic, so `eval_assertion` takes the `VSymbolic` branch (no
delegation, single evaluation) and expands `b0 ~~> true`. The second
`assert!(b0)` then reads a concrete `true`, takes the concrete path, and hits
the double-evaluation of the `move`. Asserts of distinct operands never
re-concretize the same local, so they are unaffected.

## Controls (verified)

| program | result |
|---|---|
| `assert!(b0);` | OK |
| `assert!(b0); assert!(b0);` | CRASH |
| `assert!(b0); assert!(b1);` | OK |
| `assert!(b0); assert!(b1); assert!(b1);` | CRASH |

## Suggested fix

Don't evaluate the operand twice: have `eval_assertion` thread the already-read
value/context (and `eval_op` continuation) into the concrete branch, or make
`eval_assertion_concrete` take the pre-evaluated `v`/`ctx` as parameters instead
of calling `eval_operand` again on a `move`.

## Environment

- Found by the Aeneas fuzzing harness (`fuzz/`), source-level mutation of
  `tests/src/assert-cfg.rs`, auto-minimized.
- Repro + controls + full backtrace: `fuzz/findings/n1-assert-double-eval/`.
- Distinct from #392 (that is genuinely invalid Rust — a real move-then-use —
  and is about improving the error message; this input is valid Rust that should
  translate).
