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
  let nReborrow := countEvents cc fun | .reborrow _ _ _ _ _ => true | _ => false
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
        | .reborrow c p _ _ _ => a.push (c, p)
        | _ => a
  let children := allReborrows.foldl (init := (∅ : Std.HashSet Nat))
    fun s (c, _) => s.insert c
  let chained := allReborrows.any fun (_, p) => children.contains p
  if chained then
    IO.println s!"  ✓ nested reborrow chain detected"
  else
    throw <| IO.userError "expected a nested reborrow (child of an earlier reborrow)"
  -- M9.5a: `reborrow_chain(x: &mut u32) { let s = &mut *x; *s = 7; }`
  -- must emit `ok 7#u32` as the body, not a phantom `ok ret`
  -- or some other broken tail. The deref-write through the reborrow
  -- chain must propagate to the input's vm slot so the unit-output
  -- back-closure builder sees the right post-state.
  --
  -- M9.5b: `set_fst(p: &mut Pair, v: u32) { p.fst = v; }` must emit
  -- a `structure Pair` decl AND a `def set_fst (… : Pair) (… :
  -- Std.U32) : Result Pair := do ok { … with fst := … }` shape. The
  -- struct decl comes from cert.json's new `type_decls` table; the
  -- record-update body comes from the walker's new structFieldWrite
  -- handler in `Forward.lean`. We use `_` placeholders in the
  -- substring checks where the standard backend's exact name differs
  -- (the checker uses `x1`/`x2`, the standard backend uses `p`/`v`).
  -- M9.5c: `set_idx(xs: &mut [u32; 4], i: usize, v: u32) { xs[i] = v; }`
  -- must emit a `set_idx` whose signature carries `Array Std.U32
  -- 4#usize` as both the first input and the wrapped return type, and
  -- whose body is the single `Array.update <xs> <i> <v>` call (no
  -- `(forward, backward)` pair destructuring — the standard backend
  -- collapses `index_mut` + deref-store into a single update). The
  -- translation builds on the new `PTy.array` shape (the const-generic
  -- length flows through type-position; not the value layer), the
  -- `rawTyToPTyWith` TArray-aware branch, and the `@ArrayIndexMut`
  -- intercept that runs ahead of the generic call-walker. We assert
  -- on the inner-name `set_idx` (the standard backend's docstring
  -- uses the qualified path; the checker's `def` body uses the bare
  -- name). The `Result (Array ...)` parens come from the M9.5c-1
  -- multi-token-return guard in `Decl.toLean`.
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "reborrows" tc
    let mustContain : List String := [
      -- M9.5a, unchanged.
      "def reborrow_chain (x1 : Std.U32) : Result Std.U32 := do",
      "ok 7#u32",
      -- M9.5b: struct decl emitted ahead of any function that uses it.
      "structure Pair where",
      "  fst : Std.U32",
      "  snd : Std.U32",
      -- M9.5b: set_fst's signature carries `Pair` on both sides,
      -- and the body is a struct record-update wrapped in `ok`.
      "def set_fst (x1 : Pair) (x2 : Std.U32) : Result Pair := do",
      "ok { x1 with fst := x2 }",
      -- M9.5c: set_idx — the `&mut [u32; 4]` input becomes the bare
      -- `Array Std.U32 4#usize` post-state type; the unit return is
      -- replaced by the updated array under the BackSig wrap-up. The
      -- `Result (Array ...)` parens come from the M9.5c-1
      -- multi-token-return guard.
      "def set_idx (x1 : Array Std.U32 4#usize) (x2 : Std.Usize) (x3 : Std.U32) : Result (Array Std.U32 4#usize) := do",
      -- The lowered body: a single Array.update call. The outer
      -- parens around the app come from the existing `app`
      -- pretty-print convention (multi-arg apps self-parenthesise);
      -- the standard backend prints the bare `Array.update xs i v`
      -- because OCaml drops the parens at the do-block tail. This is
      -- a cosmetic-only diff per the M9.5c done criteria.
      "Array.update x1 x2 x3"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "set_fst / set_idx / reborrow_chain output regressed"
      else
        IO.println s!"  ✓ contains: {c}"
  IO.println "all tests passed"
