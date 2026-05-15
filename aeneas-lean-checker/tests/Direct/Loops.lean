import AeneasCheck

/-!
M12.1 loop-translation tests.

Drives the `EvLoopInv` / `EvLoopEnd` cert event pair through the
T-Loop-Fixpoint forward translator. The fixture
`loops_simple::count_to` is a minimal `while` counter; the OCaml
symbolic interpreter handles it with a single fixed-point
computation, emitting one `EvLoopInv` event (start of body) and one
`EvLoopEnd` event (end of body) around the canonical body events.
M12.1 plumbing on the Lean side:

* `Typecheck/Stmts.lean::checkEvent` bounds-checks the SymExprs in
  the invariant's env (same shape as the EvJoin handler).
* `LLBCSharp/Replay.lean::stepEvent` threads the state through
  unchanged (no LLBC# loop algebra until M12.3).
* `Translate/Loops.lean::translateLoopFun` walks the body events
  between `EvLoopInv` and `EvLoopEnd` and emits three Pure decls:
    * `<fn>_loop.body` — the loop body returning `ControlFlow`;
    * `<fn>_loop` — the wrapper calling the `loop` combinator;
    * `<fn>` — the top-level shim computing the initial state and
      forwarding to the wrapper.

The asserts below cover all four plumbing points.
-/

open AeneasCheck Json LLBCSharp Typecheck Translate Backends

def main : IO Unit := do
  IO.println "M12.1 loop tests:"
  let cc ← readCrateCert "tests/Direct/loops_simple.cert.json"
  -- Typecheck: the invariant env must clear the bounds check.
  match checkCrateCert cc with
  | .ok _ => IO.println "  ✓ loops_simple.cert.json typechecks"
  | .error errs =>
    for e in errs do IO.eprintln s!"    {e}"
    throw <| IO.userError "expected accept"
  -- Replay: the loopInv / loopEnd branches are no-ops but must not abort.
  match replayCrate cc with
  | .ok _ => IO.println "  ✓ loops_simple.cert.json replays"
  | .error msg =>
    throw <| IO.userError s!"replay failed: {msg}"
  -- Shape sanity: exactly one EvLoopInv + one EvLoopEnd, in order.
  -- M12.1's OCaml restructuring suppresses the fixed-point's
  -- speculative body iterations and emits exactly one canonical
  -- body bracketed by the pair.
  let nLoopInv := cc.functions.foldl (init := 0) fun acc f =>
    acc + (f.events.foldl (init := 0) fun a e => match e with
      | .loopInv _ _ => a + 1
      | _ => a)
  let nLoopEnd := cc.functions.foldl (init := 0) fun acc f =>
    acc + (f.events.foldl (init := 0) fun a e => match e with
      | .loopEnd _ => a + 1
      | _ => a)
  if nLoopInv = 1 ∧ nLoopEnd = 1 then
    IO.println s!"  ✓ saw {nLoopInv} EvLoopInv + {nLoopEnd} EvLoopEnd"
  else
    throw <| IO.userError s!"expected exactly 1 EvLoopInv + 1 EvLoopEnd, got {nLoopInv}/{nLoopEnd}"
  -- Translate: the loop-bearing function must come out with the
  -- three-decl shape (body / wrapper / top).
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "loops_simple" tc
    let mustContain : List String := [
      -- Body decl: signature + ControlFlow return type + cont/done tails.
      "@[rust_loop_body]",
      "def count_to_loop.body",
      "Result (ControlFlow Std.U32 Std.U32)",
      "ok (cont t1)",
      "ok (done i)",
      -- Wrapper: calls `loop` with a lambda over the state.
      "@[rust_loop]",
      "def count_to_loop",
      "loop",
      "count_to_loop.body",
      -- Top-level: forwards inputs + initial state to the wrapper.
      "@[reducible]",
      "def count_to (x1 : Std.U32) : Result Std.U32 := do",
      "(count_to_loop x1 0#u32)"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "emit check failed"
      else
        IO.println s!"  ✓ contains: {c}"
  IO.println "all tests passed"
