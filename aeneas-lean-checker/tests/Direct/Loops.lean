import AeneasCheck

/-!
M12.0 loop-invariant tests.

Drives the `EvLoopInv` cert event end-to-end as a structural no-op.
The fixture `loops_simple::count_to` is a minimal `while` counter
that the OCaml symbolic interpreter handles with a single
fixed-point computation (one `EvLoopInv` event per loop). M12.0
plumbing on the Lean side:

* `Typecheck/Stmts.lean::checkEvent` bounds-checks the SymExprs in
  the invariant's env (same shape as the EvJoin handler).
* `LLBCSharp/Replay.lean::stepEvent` threads the state through
  unchanged (no LLBC# loop algebra until M12.1).
* `Translate/Forward.lean::translateFun` short-circuits any
  function whose events contain an `EvLoopInv`, emitting a sentinel
  `ok 0` body and a `/- TRANSLATOR NOTE: ... -/` block pointing at
  M12.1.

The asserts below cover all three plumbing points.
-/

open AeneasCheck Json LLBCSharp Typecheck Translate Backends

def main : IO Unit := do
  IO.println "M12.0 loop tests:"
  let cc ← readCrateCert "tests/Direct/loops_simple.cert.json"
  -- Typecheck: the invariant env must clear the bounds check.
  match checkCrateCert cc with
  | .ok _ => IO.println "  ✓ loops_simple.cert.json typechecks"
  | .error errs =>
    for e in errs do IO.eprintln s!"    {e}"
    throw <| IO.userError "expected accept"
  -- Replay: the loopInv branch is a no-op but must not abort.
  match replayCrate cc with
  | .ok _ => IO.println "  ✓ loops_simple.cert.json replays"
  | .error msg =>
    throw <| IO.userError s!"replay failed: {msg}"
  -- Shape sanity: at least one EvLoopInv event. The fixed-point
  -- computation runs exactly once per syntactic loop, so a single
  -- `while` produces exactly one EvLoopInv.
  let nLoopInv := cc.functions.foldl (init := 0) fun acc f =>
    acc + (f.events.foldl (init := 0) fun a e => match e with
      | .loopInv _ _ => a + 1
      | _ => a)
  if nLoopInv ≥ 1 then
    IO.println s!"  ✓ saw {nLoopInv} EvLoopInv event(s)"
  else
    throw <| IO.userError "expected ≥ 1 EvLoopInv"
  -- Translate: the loop-bearing function must come out with a
  -- sentinel body and a translator note. We do NOT assert on the
  -- partially-unrolled body shape because the sentinel pre-empts it.
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "loops_simple" tc
    let mustContain : List String := [
      "def count_to (x1 : Std.U32) : Result Std.U32 := do",
      "TRANSLATOR NOTE: loop-containing function",
      "M12.1 implements T-Loop-Fixpoint",
      "ok (0 : Std.U32)"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "emit check failed"
      else
        IO.println s!"  ✓ contains: {c}"
  IO.println "all tests passed"
