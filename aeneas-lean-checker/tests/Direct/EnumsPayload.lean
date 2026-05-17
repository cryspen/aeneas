import AeneasCheck

/-!
M9.5e / M9.5f: payload-bearing enum + match-binding extraction
(M9.5e) and the inverse direction — variant *construction* on the
function body (M9.5f).

The fixture `enums_payload.rs` defines a 2-variant enum `NumOrZero`
where `Num` carries a `u32` payload and `Zero` is nullary. Three
public functions exercise the two directions:

* `value(x: NumOrZero) -> u32` — M9.5e: destructure via match,
  extract the payload in the `Num` arm, return zero in the `Zero` arm.
* `wrap(x: u32) -> NumOrZero` — M9.5f: construct `NumOrZero::Num(x)`
  on the RHS of an `Aggregate(AggregatedAdt(_, Some 0, None), [Move x])`
  rvalue. Tests payload-bearing variant construction.
* `zero() -> NumOrZero` — M9.5f: construct `NumOrZero::Zero` (nullary)
  in a *parameterless* function. Tests both the nullary-variant
  construction (`SymVariant { … ; fields = [] }`) and the zero-param
  function signature shape (`def zero : Result NumOrZero` — no
  parens, single space before `:`).

M9.5e-introduced surface area is unchanged; M9.5f extends the
`SymVariant` cert shape with a `fields` list (one cert sym-expr per
operand of the OCaml `Aggregate`), threads `tdm` through
`lookupSymExpr` for ctor-name qualification, and tweaks
`tailToResult` to wrap qualified-ctor `.app` heads in `ok`.
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
  IO.println "M9.5e/f payload-enum + match-binding + ctor tests:"
  expectAccept "tests/Direct/enums_payload.cert.json"
  -- Shape sanity: the cert must contain exactly 2 EvMatchArm events
  -- (one per arm of `value`).
  let cc ← readCrateCert "tests/Direct/enums_payload.cert.json"
  let nArms := countEvents cc fun
    | .matchArm _ _ _ _ => true
    | _ => false
  if nArms = 2 then
    IO.println s!"  ✓ saw {nArms} EvMatchArm events"
  else
    throw <| IO.userError s!"expected 2 EvMatchArm events, saw {nArms}"
  -- M9.5f shape sanity: at least 2 `SymVariant` rhss in EvAssigns
  -- (`wrap`'s `Num(x)` ctor and `zero`'s `Zero`). The translator
  -- routes each through [lookupSymExpr]'s ctor-qualification path.
  let nVariants := countEvents cc fun
    | .assign _ (.symVariant _ _ _ _) => true
    | _ => false
  if nVariants ≥ 2 then
    IO.println s!"  ✓ saw {nVariants} EvAssign-with-SymVariant events"
  else
    throw <| IO.userError
      s!"expected ≥ 2 EvAssign-with-SymVariant events, saw {nVariants}"
  -- M9.5f: at least one of those SymVariants carries a non-empty
  -- `fields` array (`wrap`'s `Num(x)`). This is the new shape M9.5f
  -- adds on top of M9.5d's nullary-only [SymVariant].
  let nPayloadVariants := countEvents cc fun
    | .assign _ (.symVariant _ _ _ fields) => fields.size > 0
    | _ => false
  if nPayloadVariants ≥ 1 then
    IO.println
      s!"  ✓ saw {nPayloadVariants} payload-bearing SymVariant event(s)"
  else
    throw <| IO.userError
      s!"expected ≥ 1 payload-bearing SymVariant, saw {nPayloadVariants}"
  -- Shape sanity: the cert must declare a 2-variant enum named
  -- `NumOrZero`, with variant 0 (`Num`) carrying exactly one payload
  -- field and variant 1 (`Zero`) carrying none. This is the data the
  -- Forward translator consults to pre-seed payload binders.
  let lp := cc.llbcProgram
  let bareNameOfQualified (q : String) : String :=
    match (q.splitOn "::").getLast? with
    | some n => n
    | none => q
  match lp.typeDecls.toList.filter (fun td => bareNameOfQualified td.itemMeta.name = "NumOrZero") with
  | [td] =>
    match td.kind with
    | .enum vs =>
      if vs.size = 2 then
        IO.println s!"  ✓ NumOrZero has {vs.size} variants"
        match vs[0]?, vs[1]? with
        | some vNum, some vZero =>
          if vNum.name = "Num" then
            if vNum.fields.size = 1 then
              IO.println s!"  ✓ Num carries {vNum.fields.size} payload field"
            else
              throw <| IO.userError
                s!"expected Num.fields.size = 1, saw {vNum.fields.size}"
          else
            throw <| IO.userError
              s!"expected variant 0 name 'Num', saw '{vNum.name}'"
          if vZero.name = "Zero" then
            if vZero.fields.size = 0 then
              IO.println s!"  ✓ Zero carries no payload"
            else
              throw <| IO.userError
                s!"expected Zero.fields.size = 0, saw {vZero.fields.size}"
          else
            throw <| IO.userError
              s!"expected variant 1 name 'Zero', saw '{vZero.name}'"
        | _, _ => throw <| IO.userError "expected exactly 2 variant entries"
      else
        throw <| IO.userError s!"expected 2 variants, saw {vs.size}"
    | _ => throw <| IO.userError "expected NumOrZero to be an enum"
  | _ => throw <| IO.userError "expected exactly 1 typeDecl named 'NumOrZero'"
  -- End-to-end: translate + emit, then assert on the rendered source.
  -- We check the enum decl (with payload-typed `Num`), the function
  -- signature, and each match arm — including the `Num x2 => ok x2`
  -- binding-extraction arm. The standard Aeneas backend uses `n` as
  -- the Rust source binder name; the cert doesn't carry that, so the
  -- checker synthesises `x2` from the LLBC local index (cosmetic
  -- difference allowed per M9.5e done criteria).
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "enums_payload" tc
    let mustContain : List String := [
      -- Enum decl: `inductive NumOrZero where | Num : Std.U32 → NumOrZero | Zero : NumOrZero`.
      -- M9.5e: the `Num` line carries the payload type arrow; `Zero` stays bare.
      "inductive NumOrZero where",
      "| Num : Std.U32 → NumOrZero",
      "| Zero : NumOrZero",
      -- value (M9.5e): match-binding extraction. Function signature
      -- takes a `NumOrZero`, returns a `Result Std.U32`; the `Num`
      -- arm binds `x2` and uses it on the RHS; the `Zero` arm
      -- returns the zero literal.
      "def value (x1 : NumOrZero) : Result Std.U32 := do",
      "match x1 with",
      "| NumOrZero.Num x2 => ok x2",
      "| NumOrZero.Zero => ok 0#u32",
      -- wrap (M9.5f): payload-bearing variant *construction*. The
      -- signature flips from `value`: a `Std.U32` in, a
      -- `Result NumOrZero` out (no parens around the ret type —
      -- it's a single token). The body is a single `ok` of the
      -- qualified ctor applied to the input.
      "def wrap (x1 : Std.U32) : Result NumOrZero := do",
      "ok (NumOrZero.Num x1)",
      -- zero (M9.5f): nullary-variant construction in a zero-param
      -- function. Signature uses *single* space before `:` (no
      -- params placeholder); body is a bare qualified ctor name
      -- after `ok` (no parens — `NumOrZero.Zero` is a single token).
      "def zero : Result NumOrZero := do",
      "ok NumOrZero.Zero"
    ]
    -- Also assert what we DON'T want — `wrap`'s body must not lose
    -- the `ok` wrapper, and `zero`'s signature must not have the
    -- double-space `zero  :` shape that the pre-M9.5f `Decl.toLean`
    -- produced for zero-param decls.
    let mustNotContain : List String := [
      -- Pre-M9.5f bug: `def zero  : Result …` (double space).
      "def zero  : Result",
      -- Pre-M9.5f bug: `wrap`'s body was a bare `(NumOrZero.Num x1)`
      -- without the leading `ok`. A grep for the line shape catches
      -- the regression cleanly.
      "do\n  (NumOrZero.Num"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "enums_payload output regressed"
      else
        IO.println s!"  ✓ contains: {c}"
    for c in mustNotContain do
      if (src.splitOn c).length ≥ 2 then
        IO.eprintln s!"  ✗ unexpected substring still present: {c}"
        IO.eprintln src
        throw <| IO.userError "enums_payload regression: pre-M9.5f shape leaked"
      else
        IO.println s!"  ✓ absent: {c}"
  IO.println "all tests passed"
