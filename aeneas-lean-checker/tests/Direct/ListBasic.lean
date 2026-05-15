import AeneasCheck

/-!
M9.5j: recursive enum + recursive function (`Box<T>` heap wrapper).

The fixture `list_basic.rs` defines a non-generic singly-linked list
`List = Cons (u32, Box<List>) | Nil` and a recursive walker
`list_len(xs : List) -> u32` that returns the length. The list's
recursive payload uses `Box<List>` (Rust's owned-heap-pointer), but
Charon erases `Box<T>` at the LLBC layer: the cert's `Cons` variant
carries `(U32, List)` — no Box wrapper survives — so the checker's
existing M9.5d-1 / M9.5e variant-field machinery handles the shape
unchanged. No Box-specific code path is needed.

This chunk exercises three concerns that earlier chunks didn't cover:

1. **Self-referential type declarations**: the `Cons` variant's
   payload contains `List` itself. The Pure-IR layer needs no special
   case for recursion — a `PTy.adt "List" #[]` reference embedded in
   `List`'s own field types just resolves to the same name, and
   Lean's `inductive` accepts that shape directly.
2. **Self-recursive function calls**: the recursive `list_len(*tail)`
   call surfaces as an `EvCall` with `fn = f.fnId` (i.e. the function
   refers to itself). The translator emits the call site using the
   namespace-qualified path `list_basic.list_len`, so no rewriting at
   the call site is needed.
3. **`partial_fixpoint` trailer**: the standard Aeneas backend
   appends `partial_fixpoint` after the do-block of any recursive
   function. The M9.5j `Decl.trailer` field carries this keyword and
   the pretty-printer emits it on its own line. Detection happens in
   `translateFunWith`: we scan events for any `Event.call` whose
   callee id matches the current function's id.

A fourth concern is the `Box<List>` payload's `*tail` deref in the
recursive call. The cert event is an `EvAssign` whose rhs is a
`SymMove` of `local 2` (where the `Cons` payload was just stashed)
with a trailing `[Deref]` projection — and the projection is
*ignored* by `lookupSymExpr`, which is exactly what we want for
Box-transparency: the inner `List` value is already what `vm[2]`
holds (because Box is invisible at the value layer).
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

def main : IO Unit := do
  IO.println "M9.5j Box + recursive enum tests:"
  expectAccept "tests/Direct/list_basic.cert.json"
  let cc ← readCrateCert "tests/Direct/list_basic.cert.json"
  -- Cert-level sanity: the crate has two type decls (`List` and the
  -- synthesised `Global` placeholder). Find the `List` entry by name
  -- so we don't depend on Charon's ordering.
  let listOpt := cc.typeDecls.toList.find? (·.name = "List")
  match listOpt with
  | some td =>
    if td.typeParams = #[] then
      IO.println s!"  ✓ List.typeParams = #[] (non-generic)"
    else
      throw <| IO.userError
        s!"expected List monomorphic, saw typeParams = {td.typeParams}"
    match td.kind with
    | .enum vs =>
      if vs.size = 2 then
        IO.println s!"  ✓ List has {vs.size} variants"
        -- The recursive `Cons` variant carries (U32, List) — *not*
        -- (U32, Box<List>) — because Charon erases Box at the LLBC
        -- layer. We don't dig into the opaque type strings here
        -- (that's brittle); the inductive-emission assertions below
        -- catch any Box leakage at the Lean surface.
        match vs[0]?, vs[1]? with
        | some vCons, some vNil =>
          if vCons.name = "Cons" && vCons.fields.size = 2 then
            IO.println s!"  ✓ Cons carries 2 payload fields"
          else
            throw <| IO.userError
              s!"expected Cons with 2 fields, saw '{vCons.name}' / {vCons.fields.size}"
          if vNil.name = "Nil" && vNil.fields.size = 0 then
            IO.println s!"  ✓ Nil is nullary"
          else
            throw <| IO.userError
              s!"expected Nil nullary, saw '{vNil.name}' / {vNil.fields.size}"
        | _, _ => throw <| IO.userError "expected exactly 2 variant entries"
      else
        throw <| IO.userError s!"expected 2 variants, saw {vs.size}"
    | _ => throw <| IO.userError "expected List to be an enum"
  | none => throw <| IO.userError "expected a typeDecl named 'List'"
  -- Function-level sanity: `list_len` should appear with `fnId = 0`
  -- and an EvCall in its events list whose callee id matches its own
  -- `fnId`. That self-call is the structural signal we use to emit
  -- the `partial_fixpoint` trailer.
  let lenOpt := cc.functions.toList.find? (·.fnName = "list_basic::list_len")
  match lenOpt with
  | some f =>
    let selfCallCount : Nat := f.events.toList.foldl (init := 0) fun n ev =>
      match ev with
      | .call calleeId _ _ _ _ _ => if calleeId = f.fnId then n + 1 else n
      | _ => n
    if selfCallCount ≥ 1 then
      IO.println s!"  ✓ list_len has {selfCallCount} self-recursive EvCall(s)"
    else
      throw <| IO.userError "expected at least one self-recursive EvCall in list_len"
  | none => throw <| IO.userError "expected a function named 'list_basic::list_len'"
  -- End-to-end: translate + emit, then assert on the rendered source.
  -- We check that the emitted Lean has the recursive inductive, the
  -- self-call, the match arms, and the `partial_fixpoint` trailer.
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "list_basic" tc
    let mustContain : List String := [
      -- Recursive inductive: `Cons`'s second payload field is the
      -- enclosing `List` itself. Box is invisible. The variant's
      -- trailing return type is the bare `List` (no type params).
      "inductive List where",
      "| Cons : Std.U32 → List → List",
      "| Nil : List",
      -- Function signature: monomorphic (no `{T : Type}` binder),
      -- input is `List`, return is `Result Std.U32`.
      "def list_len (x1 : List) : Result Std.U32 := do",
      -- Match on the input, with the Cons arm binding the head
      -- (`x2`) and tail (`x3`) payload fields, then making a
      -- self-recursive call on the tail.
      "match x1 with",
      "| List.Cons x2 x3 =>",
      "let t0 ← (list_basic.list_len x3)",
      "(core.num.U32.wrapping_add t0 (1 : Std.U32))",
      "| List.Nil => ok (0 : Std.U32)",
      -- The `partial_fixpoint` trailer, at column 0 on its own line.
      -- The standard Aeneas backend emits this for recursive defs.
      "partial_fixpoint"
    ]
    -- Negative assertions: pre-M9.5j the trailer was missing entirely
    -- and the recursive payload field would have leaked as a Box-
    -- wrapped shape if the transparency assumption hadn't held. Both
    -- would surface here.
    let mustNotContain : List String := [
      -- A Box-wrapped Cons payload would render as `Box List` or
      -- `Box (List)`. Neither should appear.
      "| Cons : Std.U32 → Box ",
      "Box List →",
      -- A struct-emission of Box (had Charon let it through) would
      -- introduce a `Box` type declaration. The shim doesn't define
      -- one and the cert should never request one.
      "structure Box",
      "inductive Box",
      -- The recursive call must qualify with the surrounding
      -- namespace; a bare `list_len x3` would (silently) re-bind to
      -- some outer name shadowed by the param naming, and would also
      -- regress the pre-M9.5j path for non-recursive nested calls.
      "let t0 ← (list_len x3)"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "list_basic output regressed"
      else
        IO.println s!"  ✓ contains: {c}"
    for c in mustNotContain do
      if (src.splitOn c).length ≥ 2 then
        IO.eprintln s!"  ✗ unexpected substring still present: {c}"
        IO.eprintln src
        throw <| IO.userError "list_basic regression: unwanted shape leaked"
      else
        IO.println s!"  ✓ absent: {c}"
  IO.println "all tests passed"
