import AeneasCheck

/-!
M6 replayer smoke test: replay the incr cert and confirm the final
state matches expectations.
-/

open AeneasCheck Json LLBCSharp

def expectReplay (path : System.FilePath) : IO Unit := do
  let cc ← readCrateCert path
  match replayCrate cc with
  | .ok traces =>
    for t in traces do
      IO.println s!"  ✓ {t.fnName} replayed: {t.events.size} events, {t.finalState.loans.size} live loans at exit"
  | .error msg =>
    IO.eprintln s!"  ✗ {path} replay failed:"
    IO.eprintln msg
    throw <| IO.userError "expected replay to succeed"

def expectReplayFails (path : System.FilePath) (substring : String) : IO Unit := do
  let cc ← readCrateCert path
  match replayCrate cc with
  | .ok _ =>
    IO.eprintln s!"  ✗ {path} replayed unexpectedly"
    throw <| IO.userError "expected replay to fail"
  | .error msg =>
    if (msg.splitOn substring).length ≥ 2 then
      IO.println s!"  ✓ {path} rejected with: {substring}"
    else
      IO.eprintln s!"  ✗ wrong message for {path}: {msg}"
      throw <| IO.userError "wrong diagnostic"

def main : IO Unit := do
  IO.println "M6 replayer tests:"
  expectReplay "tests/Direct/incr.cert.json"
  expectReplayFails "tests/Negative/double_end.cert.json" "already-ended"
  expectReplayFails "tests/Negative/missing_end.cert.json" "live borrow"
  IO.println "all tests passed"
