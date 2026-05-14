import AeneasCheck

/-!
M5 typechecker smoke test:
* the incr cert passes typechecking;
* each negative fixture is rejected with the expected diagnostic.
-/

open AeneasCheck Json Typecheck

def expectAccept (path : System.FilePath) : IO Unit := do
  let cc ← readCrateCert path
  match checkCrateCert cc with
  | .ok _ => IO.println s!"  ✓ {path} accepted"
  | .error errs =>
    IO.eprintln s!"  ✗ {path} unexpectedly rejected:"
    for e in errs do IO.eprintln s!"    {e}"
    throw <| IO.userError "expected accept, got reject"

def expectReject (path : System.FilePath) (substring : String) : IO Unit := do
  let cc ← readCrateCert path
  match checkCrateCert cc with
  | .ok _ =>
    IO.eprintln s!"  ✗ {path} unexpectedly accepted"
    throw <| IO.userError "expected reject, got accept"
  | .error errs =>
    let combined := String.intercalate "\n" (errs.map (·.toString))
    if (combined.splitOn substring).length ≥ 2 then
      IO.println s!"  ✓ {path} rejected with: {substring}"
    else
      IO.eprintln s!"  ✗ {path} rejected but missing expected substring {substring}"
      IO.eprintln combined
      throw <| IO.userError "wrong diagnostic"

def main : IO Unit := do
  IO.println "M5 typechecker tests:"
  expectAccept "tests/Direct/incr.cert.json"
  expectReject "tests/Negative/double_end.cert.json" "already-ended"
  expectReject "tests/Negative/missing_end.cert.json" "live borrow"
  expectReject "tests/Negative/bad_projection.cert.json" "Index projection"
  IO.println "all tests passed"
