import AeneasCheck

/-!
M9.5p: tuple + named-field struct aggregate construction.

The fixture `aggregates_basic.rs` defines two minimal pure functions:

* `mk_tuple(x: u32, y: u32) -> (u32, u32) { (x, y) }` — the body's
  `(x, y)` rvalue lowers to a Charon `Aggregate (AggregatedAdt, TTuple,
  [x, y])`. The M9.5p-1 OCaml hook emits an
  `EvAssign { rhs: SymTuple [x, y] }` for it; the M9.5p-2 Lean walker
  consumes the SymTuple, builds `PExpr.tuple [.var x1, .var x2]`, and
  the pretty-printer renders the tail as `ok (x1, x2)`. The return
  type — a `TAdt {id = TTuple; generics = {types = [U32; U32]; ...}}`
  in the cert signature — used to fall through to `PTy.unit`
  pre-M9.5p; the M9.5p-2 `rawTyToPTyWithVars` patch parses the inner
  types and produces `PTy.tuple [.lit u32, .lit u32]` which renders
  as `Result (Std.U32 × Std.U32)`.

* `mk_pair(x: u32, y: u32) -> Pair { Pair { x, y } }` — the body's
  `Pair { x, y }` named-field struct literal lowers to an
  `Aggregate (AggregatedAdt, TAdtId Pair, [x, y])`. The OCaml side
  looks up `Pair`'s `type_decl.kind = Struct fields` and pairs each
  operand with its surface field name (`x`, `y`); the result is an
  `EvAssign { rhs: SymRecord {adt_id = Pair; fields = [(x, x); (y, y)]} }`.
  The Lean walker lowers it to `PExpr.recordLit [(x, x1), (y, x2)]`,
  and the pretty-printer renders the tail as `ok { x := x1, y := x2 }`.

These two functions cover the full M9.5p surface: both aggregate kinds
in body position, and a non-trivial tuple return type in the signature.
Failure modes the assertions guard against:

  - `Result Unit` on `mk_tuple` (pre-M9.5p unit-fallback in
    `rawTyToPTyWithVars` for TTuple)
  - `ok x1` as a body on either function (pre-M9.5p, the walker
    didn't consume the SymTuple/SymRecord rhs and the M9.5o unit-
    fallback synthesised a bare arg ref instead)
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

def main : IO Unit := do
  IO.println "M9.5p aggregate tests:"
  expectAccept "tests/Direct/aggregates_basic.cert.json"
  let cc ← readCrateCert "tests/Direct/aggregates_basic.cert.json"
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "aggregates_basic" tc
    -- Param-name (`x1` / `x2` vs the Rust source's `x` / `y`) and
    -- literal-style (`(0 : Std.Usize)` vs `0#usize`) cosmetic diffs
    -- are allowed per the M9.5p done criteria.
    let mustContain : List String := [
      -- Tuple aggregate: signature carries a `Std.U32 × Std.U32` and
      -- the body emits the matching tuple literal.
      "def mk_tuple (x1 : Std.U32) (x2 : Std.U32) : Result (Std.U32 × Std.U32) := do",
      "ok (x1, x2)",
      -- Struct aggregate: signature carries `Result Pair` and the body
      -- emits the Lean record-literal shape with surface field names.
      "def mk_pair (x1 : Std.U32) (x2 : Std.U32) : Result Pair := do",
      "ok { x := x1, y := x2 }"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "aggregates_basic output regressed"
      else
        IO.println s!"  ✓ contains: {c}"
    -- Pre-M9.5p regression guards. If either of these substrings ever
    -- shows up again, the unit-fallback / single-arg-ok-wrap pre-fix
    -- shape has resurfaced.
    let mustNotContain : List String := [
      -- `mk_tuple`'s return slot must NOT be `Unit`. Pre-M9.5p
      -- `rawTyToPTyWithVars` collapsed every TTuple type to
      -- `PTy.unit`, regardless of inner types, so the function
      -- signature said `Result Unit := do ok x1`.
      "def mk_tuple (x1 : Std.U32) (x2 : Std.U32) : Result Unit",
      -- Bare `ok x1` as the body of either function would mean the
      -- walker dropped the aggregate rhs and fell through to the
      -- M9.5o unit-fallback that just refs the first arg. Catch the
      -- exact pre-M9.5p shape with the matching line ending.
      "ok x1\n\n",
      -- The standard backend's struct-literal whitespace omits the
      -- field-name colon (`{ x, y }`); we must not silently emit that
      -- (it parses differently in Lean and references the local
      -- bindings, not the surface field names).
      "ok { x1, x2 }"
    ]
    for c in mustNotContain do
      if (src.splitOn c).length ≥ 2 then
        IO.eprintln s!"  ✗ unexpected substring present: {c}"
        IO.eprintln src
        throw <| IO.userError "aggregates_basic output contains a forbidden substring"
      else
        IO.println s!"  ✓ absent: {c}"
  IO.println "all tests passed"
