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

/-- Read a cert and assert at least one event of the given tag occurs
    somewhere in the trace. Cheap sanity check that an upstream OCaml
    hook is actually wired (e.g. EvReborrow emitted for `&mut *r`). -/
def expectEventTag (path : System.FilePath) (tagPred : Raw.Event → Bool)
    (label : String) : IO Unit := do
  let cc ← Json.readCrateCert path
  let mut hit := false
  for f in cc.functions do
    for ev in f.events do
      if tagPred ev then hit := true
  if hit then
    IO.println s!"  ✓ {path} contains {label}"
  else
    IO.eprintln s!"  ✗ {path} missing expected event tag {label}"
    throw <| IO.userError "expected event missing"

def main : IO Unit := do
  IO.println "M6 replayer tests:"
  expectReplay "tests/Direct/incr.cert.json"
  expectReplayFails "tests/Negative/double_end.cert.json" "reused after being ended"
  expectReplayFails "tests/Negative/missing_end.cert.json" "live borrow"
  -- M9.1 sanity: the incr_local trace exercises the EvReborrow hook
  -- emitted in InterpExpressions.ml for `&mut *r` shapes.
  expectEventTag "tests/Direct/incr.cert.json"
    (fun | .reborrow _ _ _ => true | _ => false)
    "EvReborrow"
  IO.println "all tests passed"
