import AeneasCheck

/-!
`lake exe aeneas-check` entry point.

Usage:
  aeneas-check <llbc.json> <cert.json> [--out <generated.lean>] [--rust-model <model.rs>]

Pipeline: parse → typecheck → replay → translate → (Lean/Rust emit).
The `--out` and `--rust-model` flags are optional; without them the
checker just validates the cert and prints a summary.
-/

open AeneasCheck Json Typecheck LLBCSharp Translate Backends

def usage : String :=
  "Usage: aeneas-check <llbc.json> <cert.json> [--out <generated.lean>] [--rust-model <model.rs>]"

/-- Find `--flag value` in args, return value if present. -/
def findFlag (args : List String) (flag : String) : Option String :=
  match args with
  | [] => none
  | f :: v :: rest =>
    if f = flag then some v else findFlag (v :: rest) flag
  | [_] => none

def main (args : List String) : IO UInt32 := do
  match args with
  | _llbcJson :: certJson :: rest => do
    let cc ← readCrateCert certJson
    IO.println s!"parsed cert: fmt={cc.fmtVersion}, hash={cc.crateHash}, fns={cc.functions.size}"
    match translateCrate cc with
    | .error e =>
      IO.eprintln s!"  ✗ pipeline error: {e}"
      return 1
    | .ok tc =>
      for d in tc.decls do
        IO.println s!"  ✓ translated {d.name}"
      let crateName :=
        match cc.functions.toList with
        | f :: _ =>
          let parts := f.fnName.splitOn "::"
          parts.headD "crate"
        | [] => "crate"
      match findFlag rest "--out" with
      | some outPath =>
        let src := emitTranslatedCrate crateName tc
        IO.FS.writeFile outPath src
        IO.println s!"  wrote Lean source: {outPath}"
      | none => pure ()
      return 0
  | _ => do
    IO.println usage
    return 1
