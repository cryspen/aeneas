import AeneasCheck.Translate.Forward
import AeneasCheck.Translate.Loops

/-!
End-to-end pipeline:

    parse  cert.json  →  Raw.CrateCert
    typecheck         →  (errors)
    replay  trace     →  CheckedTrace
    translate         →  Pure.Decl
    emit              →  Lean source / Rust source (separate modules)
-/

namespace AeneasCheck.Translate

open AeneasCheck Raw Pure LLBCSharp

structure TranslatedCrate where
  decls : Array Decl
  /-- M9.5b: ADT struct decls, in cert order. Emitted before function
      decls in the same crate namespace. Empty for crates with no
      structs. -/
  structs : Array StructDecl := #[]
  /-- M9.5d: ADT enum decls, in cert order. Emitted alongside struct
      decls (before function decls). Empty for crates with no enums. -/
  enums : Array EnumDecl := #[]
  deriving Inhabited

/-- M9.5b: build the [TypeDeclMap] used by the per-function translator
    to resolve `TAdtId N` references to struct names + field names.
    Only struct decls populate entries; opaque/unknown kinds are
    skipped (so `Field K` projections through them fall back to the
    M11 non-struct paths). -/
def buildTypeDeclMap (cc : CrateCert) : TypeDeclMap := Id.run do
  let mut m : TypeDeclMap := {}
  for td in cc.typeDecls do
    match td.kind with
    | .struct fields =>
      let names : Array String := fields.map fun f =>
        match f.name with
        | some n => n
        | none => s!"field{f.idx}"
      m := m.insert td.id { name := td.name, fieldNames := names }
    | .enum variants =>
      -- M9.5d: register the enum so [parseTAdtId]-driven type
      -- resolution can produce a `.adt <name>` PTy for parameters
      -- / return types of `Sign`-shaped enums. The Forward
      -- translator needs the bare adt name to qualify the variant
      -- constructors. M9.5e: also record each variant's payload
      -- arity so the match-arm sub-walk can pre-seed payload
      -- binders (one per field) for the arm body.
      let counts : Array Nat := variants.map fun v => v.fields.size
      m := m.insert td.id
        { name := td.name, fieldNames := #[], variantFieldCounts := counts }
    | .opaque => ()
  return m

/-- M9.5b: lift a cert `TypeDecl` into a Pure `StructDecl`, when the
    decl is a struct. Returns `none` for opaque/unknown kinds (we
    silently skip those — M9.5c+ will surface them). Field types
    come through as opaque cert strings; we feed them through
    `rawTyToPTyWith` (defined in Forward.lean) to get a concrete
    Pure type. -/
def structDeclOfTypeDecl (tdm : TypeDeclMap) (crateName : String) (td : TypeDecl) :
    Option StructDecl :=
  match td.kind with
  | .struct fields =>
    -- M9.5i: pass the struct's `typeParams` into the field-type
    -- translator so a generic field type `T` resolves to
    -- `.tyVar "T"` rather than the placeholder.
    let pureFields : Array StructField := fields.map fun f =>
      { name :=
          match f.name with
          | some n => n
          | none => s!"field{f.idx}"
        ty := rawTyToPTyWithVars tdm td.typeParams f.ty }
    some
      { name := td.name
        qualifiedName := s!"{crateName}::{td.name}"
        fields := pureFields
        typeParams := td.typeParams }
  | .enum _ => none
  | .opaque => none

/-- M9.5d / M9.5e: lift a cert `TypeDecl` into a Pure `EnumDecl`,
    when the decl is an enum. M9.5e populates each variant's field
    list (was empty under M9.5d) so payload-bearing variants render
    with their parameter types (e.g. `| Num : Std.U32 → NumOrZero`).
    Returns `none` for non-enum kinds; struct decls go through
    [structDeclOfTypeDecl] instead. -/
def enumDeclOfTypeDecl (tdm : TypeDeclMap) (crateName : String) (td : TypeDecl) :
    Option EnumDecl :=
  match td.kind with
  | .enum variants =>
    -- M9.5i: pass the enum's `typeParams` into the field-type
    -- translator so a generic variant payload type like
    -- `MySome(T)` → `T` (i.e. `TVar (Free 0)` in the cert)
    -- resolves to `.tyVar "T"` rather than the placeholder.
    let pureVariants : Array EnumVariant := variants.map fun v =>
      let pureFields : Array StructField := v.fields.map fun f =>
        { name :=
            match f.name with
            | some n => n
            | none => s!"field{f.idx}"
          ty := rawTyToPTyWithVars tdm td.typeParams f.ty }
      { name := v.name, fields := pureFields }
    some
      { name := td.name
        qualifiedName := s!"{crateName}::{td.name}"
        variants := pureVariants
        typeParams := td.typeParams }
  | .struct _ => none
  | .opaque => none

/-- Translate a whole crate cert. Per-function metadata (signature,
    source span) is taken from the cert's `FunCert`, while the
    behavioural trace comes from the replayer's `CheckedTrace`.

    M9.5b: cert `type_decls` lift into `StructDecl`s; `LeanEmit`
    emits them before functions in the same namespace.

    M12.1: functions whose cert contains an `EvLoopInv` / `EvLoopEnd`
    pair are translated via `translateLoopFun`, which emits three
    decls (body / wrapper / top-level). Non-loop functions go through
    the M10 `translateFun` (one decl). -/
def translateCrate (cc : CrateCert) : Except String TranslatedCrate := do
  let traces ← replayCrate cc
  if traces.size ≠ cc.functions.size then
    throw s!"translate: replay produced {traces.size} traces, cert has {cc.functions.size} functions"
  -- M9.5b: derive the crate name from the first function's qualified
  -- name (everything before the first `::`). Fall back to "crate" if
  -- there are no functions; structs from such a crate end up in a
  -- `crate` namespace, which the emitter handles uniformly.
  let crateName : String :=
    match cc.functions.toList with
    | f :: _ => (f.fnName.splitOn "::").headD "crate"
    | [] => "crate"
  let tdm := buildTypeDeclMap cc
  let structs : Array StructDecl :=
    cc.typeDecls.filterMap (structDeclOfTypeDecl tdm crateName)
  let enums : Array EnumDecl :=
    cc.typeDecls.filterMap (enumDeclOfTypeDecl tdm crateName)
  let mut decls : Array Decl := #[]
  for i in [0:cc.functions.size] do
    let f := cc.functions[i]!
    match translateLoopFun f with
    | some loopDecls => decls := decls ++ loopDecls
    | none => decls := decls.push (translateFunWith tdm f traces[i]!)
  return { decls, structs, enums }

end AeneasCheck.Translate
