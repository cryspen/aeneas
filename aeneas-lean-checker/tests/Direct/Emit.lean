import AeneasCheck

/-!
M7 emit smoke test: pipeline through the Lean emitter and assert the
output contains the function name and the expected monadic shape.
-/

open AeneasCheck Json Translate Backends

def main : IO Unit := do
  IO.println "M7 emit tests:"
  let cc ← readCrateCert "tests/Direct/incr.cert.json"
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "incr_cert" tc
    -- Basic shape assertions: header present, function defs present,
    -- monadic Result type used.
    let checks : List String := [
      "AUTOMATICALLY GENERATED",
      "import Aeneas.Std",
      "open Aeneas",
      "def incr_cert.incr",
      "def incr_cert.incr_local",
      "Std.Result Std.U32",
      ".ok"
    ]
    let mut ok := true
    for c in checks do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        ok := false
      else
        IO.println s!"  ✓ contains: {c}"
    if not ok then
      throw <| IO.userError "emit checks failed"
    IO.println "all tests passed"
