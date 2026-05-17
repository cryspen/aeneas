import AeneasCheck

/-!
M9.5o: trait with a default method that recursively calls another
trait method.

The fixture `defaulted_method.rs` defines:
- `trait Trait { fn provided_method(&self) -> u32 { self.required_method() } fn required_method(&self) -> u32; }`
- `NoOverride` / `YesOverride` structs each implementing `Trait`.
- `main` exercises both impls.

The default method's body inside Charon references the trait's
`required_method` via `TraitClause@0::required_method` (Charon adds
an implicit `Self: Trait` clause to the default body's generics, and
the body resolves the method through that clause). The Lean
translator rewrites those refs to `<TraitName>Inst.<method>` using
the default body's trait-bound binder.

Known follow-up gap (out of M9.5o scope, flagged for M9.5p): `main`
mis-renders the `provided_method` calls and the
`min`/`assert!`-driven tail (no `lift`/`massert` lowering yet). We
only assert on the trait/default-method shape here.
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
  IO.println "M9.5o defaulted method tests:"
  expectAccept "tests/Direct/defaulted_method.cert.json"
  let cc ← readCrateCert "tests/Direct/defaulted_method.cert.json"
  -- Cert-level sanity (M9.7o-E5a: reads from `cc.llbcProgram`).
  let lp := cc.llbcProgram
  let cratesTrait := lp.traitDecls.find?
    (fun t => t.itemMeta.name = "defaulted_method::Trait")
  match cratesTrait with
  | none => throw <| IO.userError "expected a defaulted_method::Trait decl"
  | some td =>
    let bare := match (td.itemMeta.name.splitOn "::").getLast? with
      | some n => n | none => td.itemMeta.name
    IO.println s!"  ✓ traitDecl bare name = '{bare}'"
    if td.methods.size = 2 then
      let providedHasDefault :=
        td.methods.any (fun m => m.name = "provided_method" ∧ m.hasDefault)
      let requiredNoDefault :=
        td.methods.any (fun m => m.name = "required_method" ∧ ¬ m.hasDefault)
      if providedHasDefault then
        IO.println s!"  ✓ provided_method has hasDefault = true"
      else
        throw <| IO.userError "expected provided_method.hasDefault = true"
      if requiredNoDefault then
        IO.println s!"  ✓ required_method has hasDefault = false"
      else
        throw <| IO.userError "expected required_method.hasDefault = false"
    else
      throw <| IO.userError s!"expected 2 methods on Trait, saw {td.methods.size}"
  -- M9.7o-E5b: the standalone default-body function carries
  -- trait_clauses (Charon's implicit Self: Trait obligation) sourced
  -- from the LlbcProgram's matching `funDecl.signature.generics`.
  let providedDefault :=
    cc.functions.find? fun f => f.fnName = "defaulted_method::Trait::provided_method"
  match providedDefault with
  | some f =>
    match cc.llbcProgram.funDecls.find? (·.id == f.fnId) with
    | some lf =>
      if lf.signature.generics.types = #["Self"] then
        IO.println s!"  ✓ default body typeParams = ['Self']"
      else
        throw <| IO.userError s!"expected default typeParams = ['Self']"
      match lf.signature.generics.traitClauses.toList with
      | [c] =>
        if c.traitQualifiedName = "defaulted_method::Trait" ∧ c.typeParamIdx = 0 then
          IO.println s!"  ✓ default body carries Self: Trait clause"
        else
          throw <| IO.userError "expected Self: Trait clause"
      | _ => throw <| IO.userError "expected exactly 1 trait clause on default body"
    | none => throw <| IO.userError "expected a matching LlbcFunDecl for default body"
  | none =>
    throw <| IO.userError "expected a Trait::provided_method default body fn"
  -- End-to-end: translate + emit, then assert on the rendered source.
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "defaulted_method" tc
    let mustContain : List String := [
      -- Default body emits with `.default` suffix + trait-instance
      -- binder, and `(x1 : Self)` rather than `(x1 : Std.U32)`.
      "def Trait.provided_method.default {Self : Type} (TraitInst : Trait Self)",
      "(x1 : Self) : Result Std.U32",
      -- Body references the trait method through the bound instance.
      "TraitInst.required_method x1",
      -- Trait decl head.
      "structure Trait (Self : Type) where",
      -- Both struct impls render as Unit aliases.
      "@[reducible]\ndef NoOverride := Unit",
      "@[reducible]\ndef YesOverride := Unit",
      -- Impl method bodies + instance decls.
      "def NoOverride.Insts.Defaulted_methodTrait.required_method",
      "def YesOverride.Insts.Defaulted_methodTrait.required_method",
      "def NoOverride.Insts.Defaulted_methodTrait : Trait NoOverride :=",
      "def YesOverride.Insts.Defaulted_methodTrait : Trait YesOverride :="
    ]
    let mustNotContain : List String := [
      -- Pre-M9.5o the default body was emitted as a bare function
      -- with no `.default` suffix and a stray `Std.U32` `self` slot.
      "def Trait.provided_method {Self : Type} (x1 : Std.U32) : Result Std.U32",
      -- And the body referenced `TraitClause@0` literally.
      "TraitClause@0.required_method",
      -- The __UnknownSelf mangle should be absent (the impl Self
      -- resolves to a concrete ADT here, not a type variable).
      "__UnknownSelf"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "defaulted_method output regressed"
      else
        IO.println s!"  ✓ contains: {c}"
    for c in mustNotContain do
      if (src.splitOn c).length ≥ 2 then
        IO.eprintln s!"  ✗ unexpected substring still present: {c}"
        IO.eprintln src
        throw <| IO.userError "defaulted_method regression: pre-M9.5o shape leaked"
      else
        IO.println s!"  ✓ absent: {c}"
  IO.println "all tests passed"
