import AeneasCheck

/-!
M9.5d: C-style enum + match.

The fixture `enums_basic.rs` defines a 3-variant enum `Sign` (no
payload) and a `flip` function that pattern-matches on a `Sign` and
returns another `Sign`. This is the smallest enum shape that exercises:

* enum type-decl emission (`inductive Sign where | Pos | Neg | Zero`),
* the new `EvMatchArm` cert event,
* `SymVariant` as the RHS of an `EvAssign` (nullary-variant
  aggregate),
* per-arm body translation into a `match … with | … => ok …` shape,
* qualified constructor names (`Sign.Pos` not bare `Pos`).
-/

open AeneasCheck Json LLBCSharp Typecheck Translate Backends

def expectAccept (path : System.FilePath) : IO Unit := do
  let cc ← readCrateCert path
  match checkCrateCert cc with
  | .ok _ => IO.println s!"  ✓ {path} typechecks"
  | .error errs =>
    for e in errs do IO.eprintln s!"    {e}"
    throw <| IO.userError s!"expected accept, got reject: {path}"
  match replayCrate cc with
  | .ok _ => IO.println s!"  ✓ {path} replays"
  | .error msg =>
    IO.eprintln s!"    {msg}"
    throw <| IO.userError s!"expected replay, got error: {path}"

/-- Count events of a given shape across all functions in the cert. -/
def countEvents (cc : Raw.CrateCert) (pred : Raw.Event → Bool) : Nat :=
  cc.functions.foldl (init := 0) fun acc f =>
    acc + (f.events.foldl (init := 0) fun a e => if pred e then a + 1 else a)

def main : IO Unit := do
  IO.println "M9.5d enum + match tests:"
  expectAccept "tests/Direct/enums_basic.cert.json"
  -- Shape sanity: the cert must contain exactly 3 EvMatchArm events
  -- (one per arm of `flip`). Any fewer and the OCaml hook regressed;
  -- any more and a stray arm slipped in.
  let cc ← readCrateCert "tests/Direct/enums_basic.cert.json"
  let nArms := countEvents cc fun
    | .matchArm _ _ _ _ => true
    | _ => false
  if nArms = 3 then
    IO.println s!"  ✓ saw {nArms} EvMatchArm events"
  else
    throw <| IO.userError s!"expected 3 EvMatchArm events, saw {nArms}"
  -- Shape sanity: cert must declare a 3-variant enum named `Sign`.
  match cc.typeDecls.toList with
  | [td] =>
    if td.name = "Sign" then
      match td.kind with
      | .enum vs =>
        if vs.size = 3 then
          IO.println s!"  ✓ Sign has {vs.size} variants"
        else
          throw <| IO.userError s!"expected 3 variants, saw {vs.size}"
      | _ => throw <| IO.userError "expected Sign to be an enum"
    else
      throw <| IO.userError s!"expected typeDecl name 'Sign', saw '{td.name}'"
  | _ => throw <| IO.userError "expected exactly 1 typeDecl"
  -- End-to-end: translate + emit, then assert on the rendered source.
  -- We check the enum decl, the function signature, and each match
  -- arm. The standard Aeneas backend's exact param name `s` vs. the
  -- checker's `x1` is a cosmetic difference allowed per the M9.5d
  -- done criteria (the checker doesn't have local-name metadata
  -- yet; it derives names from indices).
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "enums_basic" tc
    let mustContain : List String := [
      -- Enum decl: `inductive Sign where | Pos | Neg | Zero`. We
      -- match the constructor lines separately so a reordering /
      -- formatting change shows up clearly.
      "inductive Sign where",
      "| Pos : Sign",
      "| Neg : Sign",
      "| Zero : Sign",
      -- Function signature: `def flip (x1 : Sign) : Result Sign := do`.
      "def flip (x1 : Sign) : Result Sign := do",
      -- Match scrutinee + the three arms in source order.
      "match x1 with",
      "| Sign.Pos => ok Sign.Neg",
      "| Sign.Neg => ok Sign.Pos",
      "| Sign.Zero => ok Sign.Zero"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "enums_basic output regressed"
      else
        IO.println s!"  ✓ contains: {c}"
  IO.println "all tests passed"
