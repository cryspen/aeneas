import AeneasCheck

/-!
M9.5e: payload-bearing enum + match with binder extraction.

The fixture `enums_payload.rs` defines a 2-variant enum `NumOrZero`
where `Num` carries a `u32` payload and `Zero` is nullary. The
`value` function matches on `NumOrZero`, binds the payload `n` in
the `Num` arm, and returns it (returning `0` in the `Zero` arm).
This is the smallest payload-bearing enum shape that exercises:

* `EnumVariant.fields`: per-variant payload field info (M9.5e
  extends `EnumVariant` from M9.5d's nullary-only shape),
* `EnumDecl.toLean` with non-empty `fields`: emits
  `| Num : Std.U32 → NumOrZero` not `| Num : NumOrZero`,
* `PExpr.matchE` arms with per-arm binders (the Pure IR's arm
  shape becomes `(ctor, binders, body)`),
* the Forward translator's match-arm sub-walk pre-seeding
  `payloadBinders` so an `EvAssign { rhs = SymCopy(scrut.[Field K]) }`
  in the arm body resolves to the binder name introduced by the
  pattern (`x2` here; the standard backend uses the Rust source
  name `n`, a cosmetic difference).
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
  IO.println "M9.5e payload-enum + match-binding tests:"
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
  -- Shape sanity: the cert must declare a 2-variant enum named
  -- `NumOrZero`, with variant 0 (`Num`) carrying exactly one payload
  -- field and variant 1 (`Zero`) carrying none. This is the data the
  -- Forward translator consults to pre-seed payload binders.
  match cc.typeDecls.toList with
  | [td] =>
    if td.name = "NumOrZero" then
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
    else
      throw <| IO.userError s!"expected typeDecl name 'NumOrZero', saw '{td.name}'"
  | _ => throw <| IO.userError "expected exactly 1 typeDecl"
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
      -- Function signature: takes a `NumOrZero`, returns a `Result Std.U32`.
      "def value (x1 : NumOrZero) : Result Std.U32 := do",
      -- Match scrutinee + the two arms in source order. The `Num` arm
      -- binds `x2` and uses it on the RHS (the binding-extraction
      -- shape); the `Zero` arm returns the zero literal.
      "match x1 with",
      "| NumOrZero.Num x2 => ok x2",
      "| NumOrZero.Zero => ok (0 : Std.U32)"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "enums_payload output regressed"
      else
        IO.println s!"  ✓ contains: {c}"
  IO.println "all tests passed"
