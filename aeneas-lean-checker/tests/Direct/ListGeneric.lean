import AeneasCheck

/-!
M9.5k: generic recursive enum + generic recursive function — proves
M9.5i (generics) and M9.5j (Box-transparent recursion) compose
cleanly with no new translator surface.

Fixture `list_generic.rs` defines `GList<T> = GCons (T, Box<GList<T>>)
| GNil` plus `glist_len<T>(xs : GList<T>) -> u32`. Charon erases
`Box<T>` so the recursive payload appears as `GList T`; the generic
binder threads through inductive-decl + function-signature emission
unchanged.
-/

open AeneasCheck Json LLBCSharp Typecheck Translate Backends

def main : IO Unit := do
  IO.println "M9.5k generic recursive enum tests:"
  let cc ← readCrateCert "tests/Direct/list_generic.cert.json"
  match checkCrateCert cc with
  | .ok _ => IO.println "  ✓ list_generic.cert.json typechecks"
  | .error errs =>
    for e in errs do IO.eprintln s!"    {e}"
    throw <| IO.userError "expected accept"
  match replayCrate cc with
  | .ok _ => IO.println "  ✓ list_generic.cert.json replays"
  | .error msg => throw <| IO.userError s!"replay failed: {msg}"
  -- Cert sanity: the generic type-decl carries one type param.
  let glOpt := cc.typeDecls.toList.find? (·.name = "GList")
  match glOpt with
  | some td =>
    if td.typeParams.size = 1 then
      IO.println s!"  ✓ GList.typeParams = {td.typeParams}"
    else
      throw <| IO.userError
        s!"expected GList with 1 type param, saw {td.typeParams}"
  | none => throw <| IO.userError "expected typeDecl named 'GList'"
  -- The recursive walker carries a self-call (drives the
  -- `partial_fixpoint` trailer) and one type param on its signature.
  let lenOpt := cc.functions.toList.find?
    (·.fnName = "list_generic::glist_len")
  match lenOpt with
  | some f =>
    let selfCallCount : Nat := f.events.toList.foldl (init := 0) fun n ev =>
      match ev with
      | .call calleeId _ _ _ _ _ => if calleeId = f.fnId then n + 1 else n
      | _ => n
    if selfCallCount ≥ 1 then
      IO.println s!"  ✓ glist_len has {selfCallCount} self-recursive EvCall(s)"
    else
      throw <| IO.userError "expected ≥ 1 self-recursive EvCall"
  | none => throw <| IO.userError "expected 'list_generic::glist_len'"
  -- End-to-end: the emitted Lean must combine the M9.5i generic
  -- inductive shape (`(T : Type)` binder) with the M9.5j recursive +
  -- partial_fixpoint shape — and Box must remain invisible.
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "list_generic" tc
    let mustContain : List String := [
      "inductive GList (T : Type) where",
      "| GCons : T → GList T → GList T",
      "| GNil : GList T",
      "def glist_len {T : Type} (x1 : GList T) : Result Std.U32 := do",
      "match x1 with",
      "| GList.GCons x2 x3 =>",
      "let t0 ← (list_generic.glist_len x3)",
      "| GList.GNil => ok (0 : Std.U32)",
      "partial_fixpoint"
    ]
    let mustNotContain : List String := [
      -- Box must not leak in either the inductive or the signature.
      "Box GList",
      "Box (GList",
      "GList (Box",
      "structure Box",
      "inductive Box"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "list_generic output regressed"
      else
        IO.println s!"  ✓ contains: {c}"
    for c in mustNotContain do
      if (src.splitOn c).length ≥ 2 then
        IO.eprintln s!"  ✗ unexpected substring still present: {c}"
        IO.eprintln src
        throw <| IO.userError "list_generic regression: Box leaked"
      else
        IO.println s!"  ✓ absent: {c}"
  IO.println "all tests passed"
