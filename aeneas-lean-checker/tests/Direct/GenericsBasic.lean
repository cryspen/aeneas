import AeneasCheck

/-!
M9.5i: generics (type parameters on enums + functions).

The fixture `generics_basic.rs` defines a 2-variant generic enum
`MyOption<T>` (a `Some`/`None` mirror with payload-bearing `MySome`
and nullary `MyNone`), and a single generic function
`get<T>(x: MyOption<T>, default: T) -> T` that matches on the
input and returns the inner value or the default.

This exercises three new pieces of plumbing:

1. ADT type-parameter binders on the emitted `inductive` head
   (`inductive MyOption (T : Type) where | …`) — added in M9.5i-3's
   `EnumDecl.toLean` change.
2. Function type-parameter binders as *implicit* `{T : Type}`
   parameters before the value params — added in M9.5i-3's
   `Decl.toLean` change.
3. `TVar (Free K)` resolution: variant payload types in the cert
   come through as `(Generated_Types.TVar (Generated_Types.Free 0))`
   and the function signature's `default : T` arrives as a bare
   TVar. Both resolve to `.tyVar "T"` via M9.5i-4's
   `rawTyToPTyWithVars` plus the surrounding decl's `typeParams`
   list. The `MyOption<T>` input shape arrives as
   `TAdt { id = TAdtId 0; generics = { types = [TVar (Free 0)]; …} }`;
   the parser pulls the `types = [...]` block apart and recursively
   resolves each entry, yielding `.adt "MyOption" #[.tyVar "T"]`.
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
  IO.println "M9.5i generics tests:"
  expectAccept "tests/Direct/generics_basic.cert.json"
  let cc ← readCrateCert "tests/Direct/generics_basic.cert.json"
  -- Cert-level sanity: M9.5i-1's OCaml change makes `type_decls`
  -- carry a `type_params` list. For `MyOption<T>` we expect
  -- exactly one entry, `"T"`.
  match cc.typeDecls.toList with
  | [td] =>
    if td.name = "MyOption" then
      IO.println s!"  ✓ typeDecl name 'MyOption'"
    else
      throw <| IO.userError
        s!"expected typeDecl 'MyOption', saw '{td.name}'"
    if td.typeParams = #["T"] then
      IO.println s!"  ✓ MyOption.typeParams = #[\"T\"]"
    else
      throw <| IO.userError
        s!"expected MyOption.typeParams = #[\"T\"], saw {td.typeParams}"
    match td.kind with
    | .enum vs =>
      if vs.size = 2 then
        IO.println s!"  ✓ MyOption has {vs.size} variants"
        match vs[0]?, vs[1]? with
        | some vSome, some vNone =>
          if vSome.name = "MySome" && vSome.fields.size = 1 then
            IO.println s!"  ✓ MySome carries 1 payload field"
          else
            throw <| IO.userError
              s!"expected MySome with 1 field, saw '{vSome.name}' / {vSome.fields.size}"
          if vNone.name = "MyNone" && vNone.fields.size = 0 then
            IO.println s!"  ✓ MyNone is nullary"
          else
            throw <| IO.userError
              s!"expected MyNone nullary, saw '{vNone.name}' / {vNone.fields.size}"
        | _, _ => throw <| IO.userError "expected exactly 2 variant entries"
      else
        throw <| IO.userError s!"expected 2 variants, saw {vs.size}"
    | _ => throw <| IO.userError "expected MyOption to be an enum"
  | _ => throw <| IO.userError "expected exactly 1 typeDecl"
  -- Signature-level sanity: the cert's `signature.type_params`
  -- carries the function's type-parameter names. For `get<T>` we
  -- expect exactly `["T"]`.
  match cc.functions.toList with
  | [f] =>
    if f.signature.typeParams = #["T"] then
      IO.println s!"  ✓ get.signature.typeParams = #[\"T\"]"
    else
      throw <| IO.userError
        s!"expected get.signature.typeParams = #[\"T\"], saw {f.signature.typeParams}"
  | _ => throw <| IO.userError "expected exactly 1 function"
  -- End-to-end: translate + emit, then assert on the rendered
  -- source. We check that the emitted Lean matches the standard
  -- Aeneas backend's shape (up to the cosmetic differences
  -- described in the M9.5i done criteria: header line, missing
  -- docstring extras, renamed param names).
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "generics_basic" tc
    let mustContain : List String := [
      -- Inductive decl: the `(T : Type)` binder sits between the
      -- name and `where`. Each variant's signature ends in
      -- `MyOption T` (the fully-applied head) rather than the bare
      -- `MyOption` used for monomorphic enums.
      "inductive MyOption (T : Type) where",
      "| MySome : T → MyOption T",
      "| MyNone : MyOption T",
      -- Function signature: implicit `{T : Type}` binder before the
      -- value params; the input type `MyOption T` and return type
      -- `T` both flow from `TVar (Free 0)` resolution.
      "def get {T : Type} (x1 : MyOption T) (x2 : T) : Result T := do",
      -- Match arms: the `MySome` arm binds the payload (synthesised
      -- as `x3` by the translator's local-id naming convention);
      -- the `MyNone` arm returns the default param `x2`.
      "match x1 with",
      "| MyOption.MySome x3 => ok x3",
      "| MyOption.MyNone => ok x2"
    ]
    -- Assert what we DON'T want: pre-M9.5i, the variant payload
    -- types resolved to `Std.U32` (the catch-all) and the
    -- function signature carried no `{T : Type}` binder. A grep
    -- for those shapes catches the regression cleanly.
    let mustNotContain : List String := [
      -- Pre-M9.5i shape (TVar fell through to u32):
      "| MySome : Std.U32 → MyOption",
      "(x1 : MyOption) ",
      "(x2 : Std.U32) : Result Std.U32"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "generics_basic output regressed"
      else
        IO.println s!"  ✓ contains: {c}"
    for c in mustNotContain do
      if (src.splitOn c).length ≥ 2 then
        IO.eprintln s!"  ✗ unexpected substring still present: {c}"
        IO.eprintln src
        throw <| IO.userError "generics_basic regression: pre-M9.5i shape leaked"
      else
        IO.println s!"  ✓ absent: {c}"
  IO.println "all tests passed"
