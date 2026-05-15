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
  deriving Inhabited

/-- M9.5b: lift a cert `TypeDecl` into a Pure `StructDecl`, when the
    decl is a struct. Returns `none` for opaque/unknown kinds (we
    silently skip those — M9.5c+ will surface them). The first
    function-cert with a matching qualified-name prefix donates its
    source span so the docstring can carry one; if no fn cert mentions
    the struct (it isn't used), we leave the span empty.

    Field types come through as opaque cert strings; we feed them
    through `rawTyToPTy` (defined in Forward.lean) to get a concrete
    Pure type. -/
def structDeclOfTypeDecl (crateName : String) (td : TypeDecl) : Option StructDecl :=
  match td.kind with
  | .struct fields =>
    let pureFields : Array StructField := fields.map fun f =>
      { name :=
          match f.name with
          | some n => n
          | none => s!"field{f.idx}"
        ty := rawTyToPTy f.ty }
    some
      { name := td.name
        qualifiedName := s!"{crateName}::{td.name}"
        fields := pureFields }
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
  let structs : Array StructDecl :=
    cc.typeDecls.filterMap (structDeclOfTypeDecl crateName)
  let mut decls : Array Decl := #[]
  for i in [0:cc.functions.size] do
    let f := cc.functions[i]!
    match translateLoopFun f with
    | some loopDecls => decls := decls ++ loopDecls
    | none => decls := decls.push (translateFun f traces[i]!)
  return { decls, structs }

end AeneasCheck.Translate
