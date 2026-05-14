import AeneasCheck

/-!
M4 smoke test: parse the cert produced for `incr_local` in
`tests/src/incr_cert.rs` and confirm the parser accepts it.
-/

open AeneasCheck Json

def main : IO Unit := do
  let cc ← readCrateCert "tests/Direct/incr.cert.json"
  IO.println s!"fmt_version: {cc.fmtVersion}"
  IO.println s!"crate_hash: {cc.crateHash}"
  IO.println s!"functions: {cc.functions.size}"
  for f in cc.functions do
    IO.println s!"  {f.fnName} (id={f.fnId}): {f.events.size} events"
