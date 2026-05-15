import AeneasCheck

/-!
M9.5o: blanket trait impl with a where-clause obligation.

The fixture `blanket_impl.rs` defines:
- `trait Trait1 {}`
- `trait Trait2 { fn foo() {} }` — `foo` is a default method.
- `impl<T: Trait1> Trait2 for T {}` — blanket impl.

Charon's cert carries the new M9.5o fields:
- `ctri_self_type_var = Some "T"` (Self is a type variable)
- `ctri_type_params = ["T"]` and `ctri_trait_clauses = [("blanket_impl::Trait1", 0)]`
- `ctm_has_default = true` on `Trait2::foo`

The Lean translator turns these into:
- `def Trait2.foo.default (Self : Type) : Result Unit := do ok ()`
- `def Trait2.Blanket.foo {T : Type} (Trait1Inst : Trait1 T) : Result Unit`
- `@[reducible] def Trait2.Blanket {T : Type} (Trait1Inst : Trait1 T) : Trait2 T := { foo := Trait2.Blanket.foo Trait1Inst }`

Pre-M9.5o the same fixture produced `__UnknownSelf.Insts.Blanket_implTrait2`
(no Self resolution), no trait-bound binders, no `.default` rename, and
a unit-body that emitted `ok 0#u32` instead of `ok ()`.
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
  IO.println "M9.5o blanket impl tests:"
  expectAccept "tests/Direct/blanket_impl.cert.json"
  let cc ← readCrateCert "tests/Direct/blanket_impl.cert.json"
  -- Cert-level sanity: trait_decls has two entries with the right names.
  match cc.traitDecls.toList with
  | [td1, td2] =>
    if td1.name = "Trait1" ∧ td2.name = "Trait2" then
      IO.println s!"  ✓ traitDecls names = [Trait1, Trait2]"
    else
      throw <| IO.userError s!"expected [Trait1, Trait2], saw [{td1.name}, {td2.name}]"
    -- Trait2.foo has hasDefault = true.
    match td2.methods.toList with
    | [m] =>
      if m.name = "foo" ∧ m.hasDefault then
        IO.println s!"  ✓ Trait2.foo has hasDefault = true"
      else
        throw <| IO.userError s!"expected Trait2.foo (default), saw {m.name} (default={m.hasDefault})"
    | _ => throw <| IO.userError "expected Trait2 to have 1 method"
  | _ => throw <| IO.userError "expected exactly 2 trait decls"
  -- Cert-level sanity: trait_impls has the blanket entry.
  match cc.traitImpls.toList with
  | [ti] =>
    if ti.prettyName = "Trait2.Blanket" then
      IO.println s!"  ✓ blanket impl prettyName = 'Trait2.Blanket'"
    else
      throw <| IO.userError s!"expected 'Trait2.Blanket', saw '{ti.prettyName}'"
    if ti.selfTypeVar = some "T" then
      IO.println s!"  ✓ blanket impl selfTypeVar = some 'T'"
    else
      throw <| IO.userError s!"expected selfTypeVar = some 'T', saw {ti.selfTypeVar}"
    if ti.typeParams = #["T"] then
      IO.println s!"  ✓ blanket impl typeParams = ['T']"
    else
      throw <| IO.userError s!"expected typeParams = ['T']"
    match ti.traitClauses.toList with
    | [c] =>
      if c.traitQualifiedName = "blanket_impl::Trait1" ∧ c.typeParamIdx = 0 then
        IO.println s!"  ✓ blanket impl trait clause = [Trait1 on T]"
      else
        throw <| IO.userError "expected single Trait1-on-T clause"
    | _ => throw <| IO.userError "expected exactly 1 trait clause on the impl"
  | _ => throw <| IO.userError "expected exactly 1 trait impl"
  -- End-to-end: translate + emit, then assert on the rendered source.
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "blanket_impl" tc
    let mustContain : List String := [
      -- Default method: explicit (Self : Type) binder, no trait
      -- instance binder (Trait2::foo's body doesn't use Self).
      "def Trait2.foo.default (Self : Type) : Result Unit",
      -- Default method body emits `ok ()` (was `ok 0#u32` pre-M9.5o).
      "  ok ()",
      -- Blanket impl method body carries the trait-clause binder.
      "def Trait2.Blanket.foo {T : Type} (Trait1Inst : Trait1 T) : Result Unit",
      -- Impl instance with both binders + correct Self type.
      "def Trait2.Blanket {T : Type} (Trait1Inst : Trait1 T) : Trait2 T :=",
      -- Method body forwards the trait-bound binder.
      "foo := Trait2.Blanket.foo Trait1Inst",
      -- Trait decls.
      "structure Trait1 (Self : Type) where",
      "structure Trait2 (Self : Type) where"
    ]
    let mustNotContain : List String := [
      -- The `__UnknownSelf` mangle is a pre-M9.5o symptom of the
      -- missing Self resolution for blanket impls.
      "__UnknownSelf",
      -- The unit-body bug: a `foo()` should never tail with a U32 zero.
      "ok 0#u32",
      -- Pre-M9.5o the default body was emitted at the wrong header.
      "def Trait2.foo {Self : Type} : Result Unit",
      -- Pre-M9.5o the impl decl had `: Trait2 Unit` (Self defaulted
      -- to Unit when selfTypeVar wasn't resolved).
      "def Trait2.Blanket : Trait2 Unit"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "blanket_impl output regressed"
      else
        IO.println s!"  ✓ contains: {c}"
    for c in mustNotContain do
      if (src.splitOn c).length ≥ 2 then
        IO.eprintln s!"  ✗ unexpected substring still present: {c}"
        IO.eprintln src
        throw <| IO.userError "blanket_impl regression: pre-M9.5o shape leaked"
      else
        IO.println s!"  ✓ absent: {c}"
  IO.println "all tests passed"
