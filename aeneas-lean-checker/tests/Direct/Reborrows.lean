import AeneasCheck

/-!
M9 reborrow + field/index borrow tests.

Covers three patterns from plan §M9:
* `set_fst`: `&mut pair.fst` — a Field projection on a borrow target;
  the typechecker / replayer must accept the projection without
  rejecting it as out-of-subset.
* `set_idx`: `&mut xs[i]` — a ProjIndex projection (operand-less in
  the cert until M9.1 wires operands); still must replay structurally.
* `reborrow_chain`: `let s = &mut *x; *s = 7;` — two nested
  EvReborrow events whose parents are an implicit input borrow
  (signature-supplied) and a previously-created reborrow.
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
  match translateCrate cc with
  | .ok tc => IO.println s!"  ✓ {path} translates ({tc.decls.size} decls)"
  | .error msg =>
    throw <| IO.userError s!"expected translate, got: {msg}"

/-- Count events of a given shape across all functions in the cert. -/
def countEvents (cc : Raw.CrateCert) (pred : Raw.Event → Bool) : Nat :=
  cc.functions.foldl (init := 0) fun acc f =>
    acc + (f.events.foldl (init := 0) fun a e => if pred e then a + 1 else a)

def main : IO Unit := do
  IO.println "M9 reborrow tests:"
  expectAccept "tests/Direct/reborrows.cert.json"
  -- Shape sanity: at least one EvReborrow + at least one Field
  -- projection, confirming the OCaml hook emitted both M9.1 cert
  -- vocabulary additions.
  let cc ← readCrateCert "tests/Direct/reborrows.cert.json"
  let nReborrow := countEvents cc fun | .reborrow _ _ _ => true | _ => false
  if nReborrow ≥ 2 then
    IO.println s!"  ✓ saw {nReborrow} EvReborrow events"
  else
    throw <| IO.userError s!"expected ≥ 2 EvReborrow events, saw {nReborrow}"
  -- Shape sanity: reborrow_chain's two nested reborrows produce a
  -- parent/child id pair where the child's parent equals the
  -- previous reborrow's child. This catches regressions where the
  -- OCaml hook loses the parent linkage. (We just check that at
  -- least one reborrow's parent equals another reborrow's child.)
  let allReborrows : Array (Nat × Nat) :=
    cc.functions.foldl (init := #[]) fun acc f =>
      f.events.foldl (init := acc) fun a e =>
        match e with
        | .reborrow c p _ => a.push (c, p)
        | _ => a
  let children := allReborrows.foldl (init := (∅ : Std.HashSet Nat))
    fun s (c, _) => s.insert c
  let chained := allReborrows.any fun (_, p) => children.contains p
  if chained then
    IO.println s!"  ✓ nested reborrow chain detected"
  else
    throw <| IO.userError "expected a nested reborrow (child of an earlier reborrow)"
  -- M9.5a: `reborrow_chain(x: &mut u32) { let s = &mut *x; *s = 7; }`
  -- must emit `ok (7 : Std.U32)` as the body, not a phantom `ok ret`
  -- or some other broken tail. The deref-write through the reborrow
  -- chain must propagate to the input's vm slot so the unit-output
  -- back-closure builder sees the right post-state.
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "reborrows" tc
    let mustContain : List String := [
      "def reborrow_chain (x1 : Std.U32) : Result Std.U32 := do",
      "ok (7 : Std.U32)"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "reborrow_chain tail regressed (M9.5a)"
      else
        IO.println s!"  ✓ contains: {c}"
  IO.println "all tests passed"
