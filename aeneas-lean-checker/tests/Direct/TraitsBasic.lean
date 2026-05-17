import AeneasCheck

/-!
M9.5l: minimal traits (declaration + impl + direct method call).

The fixture `traits_basic.rs` defines:
- `pub trait Numeric { fn value(&self) -> u32; }`
- `pub struct Tag;` (unit struct)
- `impl Numeric for Tag { fn value(&self) -> u32 { 42 } }`
- `pub fn use_numeric(t: Tag) -> u32 { t.value() }`

Charon monomorphises `t.value()` to a direct call of the impl
method (the cert's `EvCall` carries the qualified name
`traits_basic::{traits_basic::Numeric for traits_basic::Tag}::value`).
The Lean checker rewrites the callee name to the standard-Aeneas
form `Tag.Insts.Traits_basicNumeric.value` via the per-fn
`prettyName` table from the cert.

Standard backend's encoding:
- Trait → `structure Numeric (Self : Type) where value : Self → Result Std.U32`
- Unit struct → `@[reducible] def Tag := Unit`
- Impl method body → `def Tag.Insts.Traits_basicNumeric.value (...) : Result Std.U32 := …`
- Impl instance → `@[reducible] def Tag.Insts.Traits_basicNumeric : Numeric Tag := { value := … }`
- Caller body → `def use_numeric (...) : Result Std.U32 := do Tag.Insts.Traits_basicNumeric.value …`

We match this byte-for-byte modulo the explicitly-accepted cosmetic
drifts (parameter names `x1` vs `t`/`self`, the
`let x1_post ← …; ok x1_post` tail-call shape that compare_simple
also has, missing `Visibility: public` line on docstrings).
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
  IO.println "M9.5l minimal-traits tests:"
  expectAccept "tests/Direct/traits_basic.cert.json"
  let cc ← readCrateCert "tests/Direct/traits_basic.cert.json"
  -- Cert-level sanity (M9.7o-E5a: reads from `cc.llbcProgram` since
  -- the flat decl mirrors were retired).
  let lp := cc.llbcProgram
  let bareNameOfQualified (q : String) : String :=
    match (q.splitOn "::").getLast? with
    | some n => n
    | none => q
  -- LlbcProgram.typeDecls always includes the synthesised `Global`
  -- placeholder alongside user-declared ADTs. Find Tag by bare name.
  match lp.typeDecls.toList.filter (fun td => bareNameOfQualified td.itemMeta.name = "Tag") with
  | [td] =>
    IO.println s!"  ✓ typeDecl name 'Tag'"
    if td.isTupleStruct then
      IO.println s!"  ✓ Tag isTupleStruct = true (unit struct)"
    else
      throw <| IO.userError "expected Tag.isTupleStruct = true"
  | _ => throw <| IO.userError "expected exactly 1 typeDecl named 'Tag'"
  -- traitDecls carries Numeric with one method.
  match lp.traitDecls.toList with
  | [td] =>
    let b := bareNameOfQualified td.itemMeta.name
    if b = "Numeric" then
      IO.println s!"  ✓ traitDecl name 'Numeric'"
    else
      throw <| IO.userError s!"expected 'Numeric', saw '{b}'"
    if td.methods.size = 1 ∧ td.methods[0]!.name = "value" then
      IO.println s!"  ✓ Numeric has method 'value'"
    else
      throw <| IO.userError "expected Numeric.methods = [value]"
  | _ => throw <| IO.userError "expected exactly 1 traitDecl"
  -- traitImpls carries the Tag instance.
  match lp.traitImpls.toList with
  | [ti] =>
    if ti.traitDeclId = 0 ∧ ti.selfTypeDeclId = some 0 then
      IO.println s!"  ✓ trait impl resolves Numeric → Tag"
    else
      throw <| IO.userError
        s!"expected trait impl (traitDeclId=0, selfTypeDeclId=some 0), saw ({ti.traitDeclId}, {ti.selfTypeDeclId})"
  | _ => throw <| IO.userError "expected exactly 1 traitImpl"
  -- Per-function sanity: the impl-method body function carries the
  -- pre-computed prettyName; the caller `use_numeric` does not.
  let implFn := cc.functions.find? fun f => f.fnName.endsWith "::value"
  let useFn := cc.functions.find? fun f => f.fnName.endsWith "::use_numeric"
  match implFn with
  | some f =>
    if f.prettyName = some "Tag.Insts.Traits_basicNumeric.value" then
      IO.println s!"  ✓ impl method body prettyName = '...Traits_basicNumeric.value'"
    else
      throw <| IO.userError
        s!"expected impl method body prettyName, saw {f.prettyName}"
  | none => throw <| IO.userError "expected an impl-method-body function"
  match useFn with
  | some f =>
    if f.prettyName.isNone then
      IO.println s!"  ✓ use_numeric carries no prettyName (regular fn)"
    else
      throw <| IO.userError s!"expected use_numeric.prettyName = none"
  | none => throw <| IO.userError "expected a use_numeric function"
  -- End-to-end: translate + emit, then assert on the rendered source.
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "traits_basic" tc
    let mustContain : List String := [
      -- Trait decl: `structure Numeric (Self : Type) where value : Self → Result Std.U32`
      "structure Numeric (Self : Type) where",
      "value : Self → Result Std.U32",
      -- Unit-struct alias for Tag.
      "@[reducible]\ndef Tag := Unit",
      -- Impl method body's `def` header carries the standard-backend
      -- Lean name (the cert pretty_name).
      "def Tag.Insts.Traits_basicNumeric.value",
      -- Impl instance.
      "def Tag.Insts.Traits_basicNumeric : Numeric Tag :=",
      "value := Tag.Insts.Traits_basicNumeric.value",
      -- Caller dispatches through the pretty name, not the Charon
      -- `{traits_basic::Numeric for traits_basic::Tag}::value` form.
      "Tag.Insts.Traits_basicNumeric.value x1",
      -- Trait docstring (the standard backend's `Trait declaration:`
      -- prefix).
      "/-- Trait declaration: [traits_basic::Numeric]",
      -- Trait-impl docstring.
      "/-- Trait implementation: [traits_basic::{traits_basic::Numeric for traits_basic::Tag}]"
    ]
    -- Assert what we DON'T want: pre-M9.5l, the trait + impl were
    -- not emitted at all (the structure / instance / impl-method
    -- body would be missing), and `Tag` would render as
    -- `structure Tag where` rather than the unit alias.
    let mustNotContain : List String := [
      "structure Tag where",
      -- Pre-M9.5l-1: the &Self shared-borrow call took the &mut
      -- pair-bind path and emitted `(x1_post_v, x1_post_back)`.
      "let (x1_post_v, x1_post_back)",
      -- Pre-M9.5l: the call site rendered the Charon-style
      -- `traits_basic.{traits_basic.Numeric for traits_basic.Tag}.value`
      -- (with `{`/`}` braces that don't form a valid Lean identifier).
      "{traits_basic.Numeric for traits_basic.Tag}"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "traits_basic output regressed"
      else
        IO.println s!"  ✓ contains: {c}"
    for c in mustNotContain do
      if (src.splitOn c).length ≥ 2 then
        IO.eprintln s!"  ✗ unexpected substring still present: {c}"
        IO.eprintln src
        throw <| IO.userError "traits_basic regression: pre-M9.5l shape leaked"
      else
        IO.println s!"  ✓ absent: {c}"
  IO.println "all tests passed"
