import AeneasCheck

/-!
M10.1 forward-call tests.

Drives the EvCall event vocabulary through the `compare_simple` cert:
* `add_u32(a, b) = a.wrapping_add(b)` translates to an `App` with the
  qualified name `core.num.U32.wrapping_add` after the sanitizer maps
  `core::num::{u32}::wrapping_add` to a Lean-valid path.
-/

open AeneasCheck Json LLBCSharp Typecheck Translate Backends

def main : IO Unit := do
  IO.println "M10.1 call tests:"
  let cc ← readCrateCert "tests/Direct/compare_simple.cert.json"
  -- Typecheck + replay must accept the cert.
  match checkCrateCert cc with
  | .ok _ => IO.println "  ✓ compare_simple.cert.json typechecks"
  | .error errs =>
    for e in errs do IO.eprintln s!"    {e}"
    throw <| IO.userError "expected accept"
  match replayCrate cc with
  | .ok _ => IO.println "  ✓ compare_simple.cert.json replays"
  | .error msg =>
    throw <| IO.userError s!"replay failed: {msg}"
  -- Translate + emit must produce the wrapping_add call in add_u32's body.
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "compare_simple" tc
    let mustContain : List String := [
      "def add_u32 (x1 : Std.U32) (x2 : Std.U32) : Result Std.U32 := do",
      "core.num.U32.wrapping_add x1 x2"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        throw <| IO.userError "emit check failed"
      else
        IO.println s!"  ✓ contains: {c}"
  -- Cert sanity: at least one EvCall event with the expected name.
  let nCall := cc.functions.foldl (init := 0) fun acc f =>
    acc + (f.events.foldl (init := 0) fun a e => match e with
      | .call _ _ name _ _ _ =>
        if (name.splitOn "wrapping_add").length ≥ 2 then a + 1 else a
      | _ => a)
  if nCall ≥ 1 then
    IO.println s!"  ✓ saw {nCall} EvCall(wrapping_add) event(s)"
  else
    throw <| IO.userError "expected ≥ 1 wrapping_add EvCall"
  -- M10.2/M10.2b: the `calls.cert.json` fixture exercises both
  -- EvEndAbs (fires when an in-body callee's region abstraction
  -- closes) and the M10.2b-populated `finalValues` payload.
  let callsCC ← readCrateCert "tests/Direct/calls.cert.json"
  match checkCrateCert callsCC with
  | .ok _ => IO.println "  ✓ calls.cert.json typechecks"
  | .error errs =>
    for e in errs do IO.eprintln s!"    {e}"
    throw <| IO.userError "calls.cert.json rejected"
  match replayCrate callsCC with
  | .ok _ => IO.println "  ✓ calls.cert.json replays"
  | .error msg => throw <| IO.userError s!"calls replay failed: {msg}"
  let nEndAbs := callsCC.functions.foldl (init := 0) fun acc f =>
    acc + (f.events.foldl (init := 0) fun a e => match e with
      | .endAbs _ _ => a + 1
      | _ => a)
  if nEndAbs ≥ 1 then
    IO.println s!"  ✓ saw {nEndAbs} EvEndAbs event(s) in calls.cert.json"
  else
    throw <| IO.userError "expected ≥ 1 EvEndAbs in calls.cert.json"
  -- M10.2b: at least one EvEndAbs must now carry a non-empty
  -- finalValues list (was always empty under the M10.2 hook-only
  -- patch).
  let nEndAbsWithFinals :=
    callsCC.functions.foldl (init := 0) fun acc f =>
      acc + (f.events.foldl (init := 0) fun a e => match e with
        | .endAbs _ fv => if fv.size ≥ 1 then a + 1 else a
        | _ => a)
  if nEndAbsWithFinals ≥ 1 then
    IO.println s!"  ✓ saw {nEndAbsWithFinals} EvEndAbs with non-empty finalValues"
  else
    throw <| IO.userError "expected ≥ 1 EvEndAbs with non-empty finalValues (M10.2b)"
  -- M11.1: the `pick` function exercises an in-body join. The cert
  -- must contain at least one EvJoin event whose `result` summary
  -- introduces a fresh symbolic value not equal to either branch's
  -- entry for the same local. Both EvAssert(branch-marker) and
  -- EvJoin must replay cleanly under the new typecheck + step rules.
  let nJoin := callsCC.functions.foldl (init := 0) fun acc f =>
    acc + (f.events.foldl (init := 0) fun a e => match e with
      | .join _ _ _ => a + 1
      | _ => a)
  if nJoin ≥ 1 then
    IO.println s!"  ✓ saw {nJoin} EvJoin event(s) in calls.cert.json"
  else
    throw <| IO.userError "expected ≥ 1 EvJoin (M11.0)"
  let nBranchAssert := callsCC.functions.foldl (init := 0) fun acc f =>
    acc + (f.events.foldl (init := 0) fun a e => match e with
      | .assert (.symVal _) _ => a + 1
      | _ => a)
  if nBranchAssert ≥ 2 then
    IO.println s!"  ✓ saw {nBranchAssert} branch-marker EvAssert event(s)"
  else
    throw <| IO.userError "expected ≥ 2 branch-marker EvAssert (M11.0)"
  -- M10.2b: the emitted Lean must now spell out the backward-
  -- function bind for `incr_via_helper`:
  --   let x1_post ← (calls.incr_inner x1)
  --   ok x1_post
  -- Compare with the standard backend's `incr_inner x` — our shape
  -- is semantically equivalent but makes the post-state slot
  -- explicit.
  match translateCrate callsCC with
  | .error e => throw <| IO.userError s!"calls translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "calls" tc
    let mustContain : List String := [
      "let x1_post ← (calls.incr_inner x1)",
      "ok x1_post"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "incr_via_helper post-state binding missing"
      else
        IO.println s!"  ✓ contains: {c}"
  IO.println "all tests passed"
