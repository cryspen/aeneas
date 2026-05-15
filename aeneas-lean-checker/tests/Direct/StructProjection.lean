import AeneasCheck

/-!
M9.5n: struct field projection + nested-generic field type lowering.

The fixture `tests/Direct/issue-194.cert.json` carries:

* a generic struct `AVLNode<T> { value: T, left: Option<Box<AVLNode<T>>>,
  right: Option<Box<AVLNode<T>>> }` — exercises (a) nested generics in
  field types, (b) Box transparency, (c) stdlib-`Option` resolution
  with type-args;
* two getter functions whose bodies are pure field reads
  (`x.value` / `x.left`) — exercises lowering of cert
  `EvAssign { rhs = SymMove(local.[Field K]) }` to
  `PExpr.fieldAccess root fieldName`.

The pre-M9.5n checker had four bugs on this shape:
  1. field types missing type-args (`left : Option` instead of
     `Option (AVLNode T)`) due to `parseTAdtGenericTypes`'s
     `takeWhile (≠ ']')` truncating at the first nested `]`;
  2. spurious re-decl of `core::option::Option` (shadowing Lean
     stdlib's `Option`) and `alloc::alloc::Global`;
  3. field reads returning the WHOLE struct (`ok x1` instead of
     `ok x1.value`) — `lookupPlace` dropped projections;
  4. nested-generic ADT pretty-print `Option AVLNode T` instead of
     `Option (AVLNode T)`.

Each of M9.5n-1..M9.5n-5 fixes one of these; this test asserts the
post-fix shape on the rendered checker source.
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
  | .ok tc => IO.println s!"  ✓ {path} translates ({tc.decls.size} decls, {tc.structs.size} structs)"
  | .error msg =>
    throw <| IO.userError s!"expected translate, got: {msg}"

def main : IO Unit := do
  IO.println "M9.5n struct-projection tests:"
  expectAccept "tests/Direct/issue-194.cert.json"
  let cc ← readCrateCert "tests/Direct/issue-194.cert.json"
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "issue_194_recursive_struct_projector" tc
    let mustContain : List String := [
      -- BUG 1 fix: field types carry type-args, including the
      -- Box-transparent nesting `Option<Box<AVLNode<T>>>` → `Option (AVLNode T)`.
      "value : T",
      "left : Option (AVLNode T)",
      "right : Option (AVLNode T)",
      -- BUG 4 fix: function signatures use the threaded type-param.
      "def get_val {T : Type} (x1 : AVLNode T) : Result T := do",
      "def get_left {T : Type} (x1 : AVLNode T) : Result (Option (AVLNode T)) := do",
      -- BUG 4 fix: bodies project the right field with Lean
      -- dot-notation, no `ok (…)`-wrap around the field-access form.
      "ok x1.value",
      "ok x1.left"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "issue-194 output regressed"
      else
        IO.println s!"  ✓ contains: {c}"
    -- BUG 2 / BUG 3: stdlib ADTs (`Option`, `Global`) must NOT be
    -- re-emitted; they have Lean equivalents in scope via
    -- `open Aeneas Aeneas.Std`. A re-decl of `Option` would
    -- *shadow* the stdlib one and the field type `Option (AVLNode T)`
    -- would suddenly resolve to the local (now broken) decl.
    let mustNotContain : List String := [
      "def Global",
      "inductive Option",
      -- BUG 1 regression guard: a bare `Option` with no type-arg
      -- before a newline indicates `parseTAdtGenericTypes` came back
      -- empty. The substring discipline mirrors `tests/Direct/Slices.lean`.
      "left : Option\n",
      "right : Option\n",
      "Result Option\n",
      -- BUG 4 regression guard: `ok x1` (returning the whole struct)
      -- without a `.value` / `.left` would mean `lookupPlace`
      -- dropped the projection again.
      "do\n  ok x1\n"
    ]
    for c in mustNotContain do
      if (src.splitOn c).length ≥ 2 then
        IO.eprintln s!"  ✗ unexpected substring present: {c}"
        IO.eprintln src
        throw <| IO.userError "issue-194 output contains a forbidden substring"
      else
        IO.println s!"  ✓ absent: {c}"
  IO.println "all tests passed"
