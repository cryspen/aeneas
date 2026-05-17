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
    -- M9.6 (Option C, plan §4.1.2): env-var-gated strict EvJoin
    -- per-witness check. AENEAS_STRICT_JOIN=1 turns on per-entry
    -- rule-driven validation against the cert's witnesses; off
    -- by default falls back to the M11 pragmatic ≤ check.
    let strictJoin ← match (← IO.getEnv "AENEAS_STRICT_JOIN") with
      | some "1" | some "true" => pure true
      | _ => pure false
    match translateCrate cc strictJoin with
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
      match findFlag rest "--rust-model" with
      | some rustPath =>
        let src := emitTranslatedCrateRust crateName tc
        IO.FS.writeFile rustPath src
        IO.println s!"  wrote Rust model:  {rustPath}"
      | none => pure ()
      return 0
  | _ => do
    IO.println usage
    return 1
