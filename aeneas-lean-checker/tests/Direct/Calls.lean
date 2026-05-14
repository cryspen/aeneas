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
  IO.println "all tests passed"
