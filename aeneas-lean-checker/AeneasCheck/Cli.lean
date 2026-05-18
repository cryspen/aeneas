import AeneasCheck

/-!
`lake exe aeneas-check` entry point.

Usage:
  aeneas-check <cert.json>                  [--out …] [--rust-model …]    -- v3+
  aeneas-check <llbc.json> <cert.json>      [--out …] [--rust-model …]    -- legacy

Pipeline: parse → typecheck → replay → translate → (Lean/Rust emit).
The `--out` and `--rust-model` flags are optional; without them the
checker just validates the cert and prints a summary.

M9.7f: cert v3 embeds the post-pre-pass LLBC inside the cert itself
(`cc.llbcProgram`), so the separate `<llbc.json>` argument is no
longer needed. The 2-argument form is still accepted (the first
positional is discarded) for back-compat with scripts that haven't
been updated yet.
-/

open AeneasCheck Json Typecheck LLBCSharp Translate Backends

def usage : String :=
  "Usage: aeneas-check <cert.json> [--out <generated.lean>] [--rust-model <model.rs>]\n" ++
  "                    [--skip-decl <name> ...]\n" ++
  "       aeneas-check <llbc.json> <cert.json> [--out …] [--rust-model …]    (legacy, llbc.json ignored)"

/-- Find `--flag value` in args, return value if present. -/
def findFlag (args : List String) (flag : String) : Option String :=
  match args with
  | [] => none
  | f :: v :: rest =>
    if f = flag then some v else findFlag (v :: rest) flag
  | [_] => none

/-- Session 5 (Item 2): collect every `--flag value` occurrence into
    a list. Used by `--skip-decl <name>` to drop named decls from the
    Lean emit so a fixture's well-emitted subset can ship without
    dragging the broken siblings along. -/
def findFlagsAll (args : List String) (flag : String) : List String :=
  match args with
  | [] => []
  | f :: v :: rest =>
    if f = flag then v :: findFlagsAll rest flag
    else findFlagsAll (v :: rest) flag
  | [_] => []

/-- M9.7f: pick the cert path and the remaining args from the CLI tail.

    Accepts the 1-arg form (`<cert.json> …`) and the 2-arg legacy
    form (`<llbc.json> <cert.json> …`, where `<llbc.json>` is
    discarded). The heuristic: if the first positional ends with
    `.cert.json` it is the cert path; otherwise we treat it as the
    legacy LLBC arg and consume the next positional as the cert. -/
def parsePositional (args : List String) : Option (String × List String) :=
  match args with
  | first :: rest =>
    if first.endsWith ".cert.json" then some (first, rest)
    else
      match rest with
      | cert :: tail => some (cert, tail)
      | [] => none
  | [] => none

def main (args : List String) : IO UInt32 := do
  match parsePositional args with
  | some (certJson, rest) => do
    let cc ← readCrateCert certJson
    IO.println s!"parsed cert: fmt={cc.fmtVersion}, hash={cc.crateHash}, fns={cc.functions.size}"
    -- M9.6 (Option C, plan §7.1 #22): strict EvJoin per-witness
    -- check is now ON by default. Pass AENEAS_STRICT_JOIN=0 (or
    -- "false") to opt out — the pragmatic ≤ helpers
    -- ([joinEntryOk] / [isFreshSym] / [symExprBeq]) are removed
    -- in this commit, so opting out only matters when the cert
    -- carries no witnesses (in which case [stepJoin] degenerates
    -- to a state-overwrite without per-entry validation).
    let strictJoin ← match (← IO.getEnv "AENEAS_STRICT_JOIN") with
      | some "0" | some "false" => pure false
      | _ => pure true
    -- M9.7o-E5a: cert v2 was rejected and the flat-source translator
    -- path retired. `AENEAS_USE_LLBC_PROGRAM` is no longer consulted.
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
      let skipNames := findFlagsAll rest "--skip-decl"
      match findFlag rest "--out" with
      | some outPath =>
        let src := emitTranslatedCrate crateName tc skipNames
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
  | none => do
    IO.println usage
    return 1
