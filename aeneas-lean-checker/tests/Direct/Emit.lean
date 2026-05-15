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
    -- Shape assertions match the M9.0a-polished emitter: standard
    -- header (`import Aeneas`, full `open` line), per-function
    -- docstring with `Source: ...`, namespace block, do-syntax body.
    let checks : List String := [
      "AUTOMATICALLY GENERATED",
      "import Aeneas\n",
      "open Aeneas Aeneas.Std Result ControlFlow Error",
      "set_option maxHeartbeats",
      "namespace incr_cert",
      "/-- [incr_cert::incr]:\n    Source:",
      "/-- [incr_cert::incr_local]:\n    Source:",
      "def incr (x1 : Std.U32) : Result Std.U32 := do",
      "def incr_local (x1 : Std.U32) : Result Std.U32 := do",
      -- M10.0: the cert now carries the `*x += 1` binop, so the body
      -- contains an additive expression — both functions translate
      -- to the same surface shape `(x1 + 1#u32)`.
      "(x1 + 1#u32)",
      "end incr_cert"
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
