import AeneasCheck.Raw.LLBCProgram
import AeneasSoundness.LLBCSharpPaper.Syntax

/-!
# Static-program lookup helpers over `cc.llbcProgram`

This is the M9.7-introduced module called out in plan §1.1 row 3 /
§1.3 commit A4. Cert v3 (M9.7) made the LLBC program self-contained
inside the cert; every per-event / per-function lemma that needs a
callee signature, a type-decl's field layout, or a trait-impl's
method table now goes through these helpers — *not* through the
retired flat `cc.typeDecls` / `FunCert.signature` etc.

The pairing primary key is `FunCert.fnId ≡ LlbcFunDecl.id`. The
checker's M9.7h `Consistency.checkLlbcVsCert` already verifies this
holds whenever `Replay.replayCrate cc = .ok`; Phase F's
`lookupFunDecl_total_of_replayCrate_ok` (M10.4b) discharges from it
that every replayed function has a matching `LlbcFunDecl`.

## Total vs. partial

These helpers return `Option`. Totality (every replayed function has a
matching decl) is *not* a property of the helpers themselves — it's a
consequence of `replayCrate` having succeeded, which is what M10.4b
proves.

## Source-of-truth boundary

Wherever the pre-cert-v3 plan reached into `FunCert.signature`
(opaque `FnSignature` string), the post-v3 plan reaches into
`(lookupFunDecl cc f).signature : LlbcSignature` — a structured
record with `inputs : Array LlbcTy`, `output : LlbcTy`,
`generics : LlbcGenericParams`. The per-event and per-function
soundness lemmas thread `lookupFunDecl cc f = some lfd` as a
hypothesis and project through `lfd.signature` / `lfd.localsTypes`.
-/

namespace AeneasSoundness.LLBCSharpPaper

open AeneasCheck.Raw

/-! ## Function-decl lookup -/

/-- Look up the `LlbcFunDecl` matching a `FunCert` by `fnId`.

    Returns `none` only when the `cc.llbcProgram.funDecls` table is
    missing an entry for `f.fnId`. M9.7h's `Consistency.checkLlbcVsCert`
    guarantees this never happens when `Replay.replayCrate cc = .ok`,
    so Phase E / F soundness lemmas can either take
    `lookupFunDecl cc f = some lfd` as a hypothesis or invoke the
    Phase-F totality preamble.
-/
def lookupFunDecl (cc : CrateCert) (f : FunCert) : Option LlbcFunDecl :=
  cc.llbcProgram.funDecls.find? fun d => d.id = f.fnId

/-- Compose `lookupFunDecl` with `.signature`. Convenience wrapper
    used by per-event lemmas that need only the structured signature
    (not the locals table or body). -/
def signatureOf (cc : CrateCert) (f : FunCert) : Option LlbcSignature :=
  (lookupFunDecl cc f).map (·.signature)

/-- Look up the per-local LLBC types of a `FunCert`'s body. Empty
    when the matched `LlbcFunDecl` has `body = none` (opaque /
    extern), `none` when there is no matching decl at all. -/
def localsTypesOf (cc : CrateCert) (f : FunCert) : Option (Array LlbcTy) :=
  (lookupFunDecl cc f).map (·.localsTypes)

/-- Look up a `FunCert` by `fnId` against the cert's own function
    table. Symmetric counterpart to `lookupFunDecl`; used when an
    `EvCall` event needs to discharge that its callee is itself a
    replayed function. -/
def lookupFunCert (cc : CrateCert) (fnId : Nat) : Option FunCert :=
  cc.functions.find? fun f => f.fnId = fnId

/-! ## Type-decl lookup -/

/-- Look up a `LlbcTypeDecl` by id (Charon's `TypeDeclId`). The
    primary lookup used by `EvMatchArm.adtId` and by per-event
    consistency checks. -/
def lookupTypeDecl (cc : CrateCert) (id : Nat) : Option LlbcTypeDecl :=
  cc.llbcProgram.typeDecls.find? fun d => d.id = id

/-- Look up a `LlbcTypeDecl` by its qualified name in
    `itemMeta.name`. Useful for sanity-checks; the primary key is
    the id form above. -/
def lookupTypeDeclByName (cc : CrateCert) (name : String) :
    Option LlbcTypeDecl :=
  cc.llbcProgram.typeDecls.find? fun d => d.itemMeta.name = name

/-! ## Trait-decl and trait-impl lookup -/

/-- Look up a `LlbcTraitDecl` by id. -/
def lookupTraitDecl (cc : CrateCert) (id : Nat) :
    Option LlbcTraitDecl :=
  cc.llbcProgram.traitDecls.find? fun d => d.id = id

/-- Look up a `LlbcTraitDecl` by its qualified name. -/
def lookupTraitDeclByName (cc : CrateCert) (name : String) :
    Option LlbcTraitDecl :=
  cc.llbcProgram.traitDecls.find? fun d => d.itemMeta.name = name

/-- Look up a `LlbcTraitImpl` by id. -/
def lookupTraitImpl (cc : CrateCert) (id : Nat) :
    Option LlbcTraitImpl :=
  cc.llbcProgram.traitImpls.find? fun i => i.id = id

/-- Look up a `LlbcTraitImpl` by its qualified name. -/
def lookupTraitImplByName (cc : CrateCert) (name : String) :
    Option LlbcTraitImpl :=
  cc.llbcProgram.traitImpls.find? fun i => i.itemMeta.name = name

/-! ## Signature-derived helpers used by Phase E

`signatureToInitialAbs` produces the function-entry region-abstraction
shapes from an `LlbcSignature`. Plan §5.2 risk #1: this is the helper
that makes Phase E's `Initial` definition pattern-match on the
structured `LlbcSignature` rather than parse an opaque string. The
full implementation lands in Phase E (M10.3a); this file exposes the
signature so the lemma is dispatchable.

For now the helper is the *identity-on-signature* projection: it
returns the `inputs` array as the per-input "abs-shape seed."
Refinement to actual paper-Fig.10 `A_in(ρ)` shapes is M10.3a's job.
-/

/-- M10.0d stub for Phase E's `signatureToInitialAbs`. Returns the
    signature's input types as a placeholder seed array; the real
    `A_in(ρ)` derivation lands in M10.3a. -/
def signatureInputTys (sig : LlbcSignature) : Array LlbcTy :=
  sig.inputs

end AeneasSoundness.LLBCSharpPaper
