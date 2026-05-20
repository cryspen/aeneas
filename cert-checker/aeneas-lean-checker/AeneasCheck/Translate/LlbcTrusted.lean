import AeneasCheck.Raw.LLBCProgram
import AeneasCheck.Raw.CertEvent

/-!
# LlbcTrusted — single point of trust for LLBC metadata

Every read of LLBC-derived metadata in the cert-walker goes through
this namespace. The cert events themselves are M10-verified
(soundness theorem `replayCrate_correspondence`), but the embedded
`llbc_program` field of the cert is *not* covered by the theorem —
it carries function signatures, per-local types, type-decl tables,
trait decls, and the LLBC body that the walker consults for static
information.

By routing every LLBC read through this file, we keep the trust
boundary visible and grep-able. A CI gate (`scripts/check-llbc-trust.sh`)
enforces that
`aeneas-lean-checker/AeneasCheck/Translate/{Forward,Loops,Driver}.lean`
contain zero raw `lf.<field>` / `cc.llbcProgram.<field>` reads.

See `documentation/plans/llbc-trust-removal-plan.md` for the staged
pathway (Z2 → Z3a → Z4a) that progressively replaces each accessor
here with a cert-derived equivalent.

## Trust classes

Each accessor's docstring tags one of:
* **load-bearing** — a wrong value from this accessor produces wrong
  (but possibly type-correct) emit. Soundness still holds, but the
  Rust model would semantically diverge from the source.
* **cosmetic** — affects readability only. Wrong values produce ugly
  but correct output.
-/

namespace AeneasCheck.Translate.LlbcTrusted

open AeneasCheck Raw

/-! ## `LlbcFunDecl` accessors -/

/-- load-bearing — function signature drives all sig-level shape
    (input types, output type, generics). -/
@[inline] def signatureOf (lf : LlbcFunDecl) : LlbcSignature := lf.signature

/-- load-bearing — per-local type drives placeholder synthesis,
    field-projection resolution, and the typed-fallback path. -/
@[inline] def localType (lf : LlbcFunDecl) (i : Nat) : Option LlbcTy :=
  lf.localsTypes[i]?

/-- load-bearing — whole-array consumers (Driver's `lookupLf`,
    Forward's `localTypes` seed map). -/
@[inline] def localsTypesArr (lf : LlbcFunDecl) : Array LlbcTy := lf.localsTypes

/-- cosmetic — per-local user name (`Charon.local.name`). Used to
    prefer `y` over the synthesised `x1` in emitted code. A wrong
    value here produces a slightly less readable model. -/
@[inline] def localName (lf : LlbcFunDecl) (i : Nat) : Option (Option String) :=
  lf.localsNames[i]?

/-- cosmetic — whole-array form of [localName]. -/
@[inline] def localsNamesArr (lf : LlbcFunDecl) : Array (Option String) :=
  lf.localsNames

/-- load-bearing — type-parameter names drive the implicit-binder
    rendering and the `tVar k` → `name` lookup in
    `llbcTyToPTyWithVars`. -/
@[inline] def typeParams (lf : LlbcFunDecl) : Array String :=
  lf.signature.generics.types

/-- load-bearing — the LLBC body. The Forward fallback pass (Bug 2)
    reads variant-binder names directly from the body shape; the
    walker also consults it to seed `vm` for unwritten locals. -/
@[inline] def bodyOf (lf : LlbcFunDecl) : Option LlbcBlock := lf.body

/-- cosmetic — qualified item name. Surfaces in docstrings and decl
    headers but doesn't change emitted semantics. -/
@[inline] def itemMetaNameOf (lf : LlbcFunDecl) : String := lf.itemMeta.name

/-- cosmetic — Charon's `attr_info.public` visibility bit. Threaded
    into the emitted `Decl.isPublic` so the docstring can carry the
    `Visibility: public` line. -/
@[inline] def itemMetaPublicOf (lf : LlbcFunDecl) : Bool := lf.itemMeta.isPublic

/-- load-bearing — function id. Used as a HashMap key (Driver's
    `lfById`). A collision here would mis-attribute a body. -/
@[inline] def idOf (lf : LlbcFunDecl) : Nat := lf.id

/-! ## `CrateCert.llbcProgram` accessors -/

/-- load-bearing — type-decl table. Drives all ADT lifting (structs,
    enums, opaques) and the `TypeDeclMap`. -/
@[inline] def typeDecls (cc : CrateCert) : Array LlbcTypeDecl :=
  cc.llbcProgram.typeDecls

/-- load-bearing — function-decl table. The per-function signature /
    body / locals all originate here. -/
@[inline] def funDecls (cc : CrateCert) : Array LlbcFunDecl :=
  cc.llbcProgram.funDecls

/-- load-bearing — trait-decl table. Drives trait-decl lifting and
    the default-method rename map. -/
@[inline] def traitDecls (cc : CrateCert) : Array LlbcTraitDecl :=
  cc.llbcProgram.traitDecls

/-- load-bearing — trait-impl table. Drives impl pretty-name
    computation and method body wiring. -/
@[inline] def traitImpls (cc : CrateCert) : Array LlbcTraitImpl :=
  cc.llbcProgram.traitImpls

/-- load-bearing (when introspected) — global-decl table. Opaque
    today (the Lean parser stores it as `Json`); kept here so any
    future consumer routes through the shim. -/
@[inline] def globalDecls (cc : CrateCert) : Lean.Json :=
  cc.llbcProgram.globalDecls

end AeneasCheck.Translate.LlbcTrusted
