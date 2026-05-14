import AeneasCheck

/-!
`lake exe aeneas-check` entry point.

Usage:
  aeneas-check <llbc.json> <cert.json> [--out <generated.lean>] [--rust-model <model.rs>]

For M4 this only parses the cert and reports its shape. M5+ will hook
the typechecker, M6 the LLBC# replayer, M7 the Lean emitter, M8 the
Rust emitter.
-/

open AeneasCheck Json Typecheck

def usage : String :=
  "Usage: aeneas-check <llbc.json> <cert.json> [--out <generated.lean>] [--rust-model <model.rs>]"

def main (args : List String) : IO UInt32 := do
  match args with
  | _llbcJson :: certJson :: _rest => do
    let cc ← readCrateCert certJson
    IO.println s!"parsed cert: fmt={cc.fmtVersion}, hash={cc.crateHash}, fns={cc.functions.size}"
    match checkCrateCert cc with
    | .ok _ =>
      for f in cc.functions do
        IO.println s!"  ✓ fn {f.fnName} (id={f.fnId}): {f.events.size} events"
      return 0
    | .error errs =>
      for e in errs do IO.eprintln s!"  ✗ {e}"
      return 1
  | _ => do
    IO.println usage
    return 1
