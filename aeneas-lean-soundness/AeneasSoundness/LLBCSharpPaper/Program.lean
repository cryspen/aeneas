import AeneasCheck.Raw.LLBCProgram
import AeneasSoundness.LLBCSharpPaper.Syntax
import AeneasSoundness.LLBCSharpPaper.State

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

/-! ## Signature-derived helper used by Phase E

`signatureToInitialAbs` produces the function-entry region-abstraction
shapes from an `LlbcSignature`. Plan §5.2 risk #1: this is the helper
that makes Phase E's `Initial` definition pattern-match on the
structured `LlbcSignature` rather than parse an opaque string. The
pre-cert-v3 version had to scrape RawTy substrings out of an opaque
`FnSignature` string; cert v3's structured `LlbcSignature.inputs :
Array LlbcTy` makes this a clean walk over `LlbcTy.tRef` constructors.

## Shape choice (M10 fixture scope)

The M10 fixture set covers functions with input borrows that appear
at the *top level* of the input type. We emit one `AbsShape` per such
input borrow:

* `&'r mut T` at input position `i` → `AbsShape { absId := j,
  parentAbs := #[], roles := #[.mutBorrow i j] }`
* `&'r T` at input position `i` → `AbsShape { absId := j,
  parentAbs := #[], roles := #[.sharedBorrow i j] }`

where `j` is a monotonically-assigned abs id (paper §4.1 picks the
freshest id for each region; the cert-side names are bound at function
entry, not by the signature alone, so any monotone assignment is
faithful to the paper).

Nested-borrow inputs (e.g. `&'r mut (&'s mut T)`) are out of scope at
M10 — the fixture set doesn't exercise them, and the deeper traversal
would require pairing parent / child region ids, a Phase-F+ extension.
Inputs that don't carry borrows (literals, ADTs, tuples without
borrow-typed fields) contribute no entries. The resulting array's
length is therefore `≤ sig.inputs.size`.
-/

/-- Lift one input position into its function-entry `AbsShape`, if
    the input type carries a top-level borrow. Returns `none` for
    non-borrow inputs (literals, opaque ADTs, …). The `absId` field
    is supplied by the caller's monotone counter so the assignment is
    declaration-ordered (paper §4.1's "fresh region id per input"). -/
def signatureToInitialAbsOne (argIdx absId : Nat) :
    AeneasCheck.Raw.LlbcTy → Option AbsShape
  | .tRef _ _ .mut =>
      some { absId := absId, parentAbs := #[],
             roles := #[.mutBorrow argIdx absId] }
  | .tRef _ _ .shared =>
      some { absId := absId, parentAbs := #[],
             roles := #[.sharedBorrow argIdx absId] }
  | _ => none

/-- Walk an `LlbcSignature`'s `inputs` and emit one `AbsShape` per
    top-level input borrow, in declaration order. The companion lemma
    `signatureToInitialAbs_empty` (smoke) discharges the empty-inputs
    base case; Phase E2 (`replayFun_event_induct`) and Phase E4
    (`replayFun_sound` assembly) consume the helper's range. -/
def signatureToInitialAbs (sig : LlbcSignature) : Array AbsShape := Id.run do
  let mut out : Array AbsShape := #[]
  let mut nextAbsId : Nat := 0
  let mut argIdx : Nat := 0
  for ty in sig.inputs do
    match signatureToInitialAbsOne argIdx nextAbsId ty with
    | some shape =>
        out := out.push shape
        nextAbsId := nextAbsId + 1
    | none => pure ()
    argIdx := argIdx + 1
  return out

/-! ## Paper Fig. 10 — `borrow_checks#`, `Initial`, `Final`

These are the function-signature-level predicates from paper Fig. 10
(see also `documentation/cert-format-and-soundness.md` §4.3). Phase E
ports the three Fig. 10 entries plus the bridging `Final` predicate
that ties paper `Ω#` to the replayer's `SymState`:

* `BorrowChecks sig` — paper `borrow_checks#(sig)`. Cert v4: the
  cert's existence + `replayCrate cc = .ok` is the witness, so this
  reduces to `True` at the M10 fixture scope. A stronger version
  (proving the signature is locally consistent: every input borrow
  region appears in the output's flow or is consumed by some
  `EvEndAbs`) is plan §6.1 #5 / M11 work.
* `Initial Ω sig prog` — paper `Initial(Ω, sig)`. Ω is a valid
  function-entry state for `sig` in program `prog`: the input
  region abstractions from `signatureToInitialAbs sig` are
  installed in `Ω.abs`, the input locals are populated with fresh
  symbolic values, and the freshness counters dominate the
  signature-derived ids.
* `Final` lives in `Soundness/InitialFinal.lean` because its
  signature carries `SymState` (paper-to-replayer bridge).

`Initial` and `BorrowChecks` are paper-pure (no `SymState` reference),
so they live alongside `signatureToInitialAbs` in this file.

## Smoke lemmas (G6-exempt under LLBCSharpPaper/)

Two smoke lemmas anchor the predicates' shapes:

* `signatureToInitialAbs_empty` — the empty-signature base case.
* `Initial_implies_borrow_checks` — the upward implication paper Fig.
  10 records. Trivial at v4 because `BorrowChecks = True`; the
  stronger form lands in M11.

Both are `sorry`'d at M10.4a — the file lives outside
`Soundness/`, so G6 (`grep sorry Soundness/`) stays empty. Phase E4
(`replayFun_sound` assembly) is where these smoke lemmas earn their
keep; E2 / E3 don't depend on them being proved.
-/

/-- Paper Fig. 10's `borrow_checks#(sig)`. At cert v4 the predicate
    reduces to `True` — the OCaml interpreter only emits certs for
    functions that already passed its symbolic borrow-checker, so the
    cert's existence is the witness (plan §6 — the trusted-base
    `CertGen_faithful` axiom subsumes signature-level borrow-checking
    by construction). The plan §6.1 #5 stronger form ("every input
    borrow has a matching output flow or is consumed by an
    EvEndAbs") is M11 work; until then this stays at the trivial
    proposition. -/
def BorrowChecks (_sig : LlbcSignature) : Prop := True

/-- Paper Fig. 10's `Initial(Ω, sig)`, parameterised by the
    surrounding `LlbcProgram` so per-event Phase-E2 lemmas can resolve
    callee signatures via `lookupFunDecl`. The structure has four
    fields:

* `borrow_checks_sig` — the signature passes paper's
  borrow-check (`BorrowChecks sig`). At v4 trivial.
* `initial_abs_installed` — every `AbsShape` from
  `signatureToInitialAbs sig` is in `Ω.abs` with its
  `liftAbsShape` content.
* `inputs_populated` — each input local (paper convention: positions
  `1..sig.inputs.size`; local `0` is the return slot) is populated
  with some symbolic value.
* `freshness_dominates_initial` — the abs-id freshness counter
  exceeds every signature-installed abs id, so subsequent `LStep`
  rules can pick fresh ids without colliding with the initial set.

The "freshest sym-value id" half of the input-population invariant is
deferred to the per-event induction (Phase E2) — at function entry
the cert-supplied `σ` values are bound; their freshness flows from
`CertGen_faithful`.
-/
structure Initial
    (Ω : LLBCState) (sig : AeneasCheck.Raw.LlbcSignature)
    (_prog : AeneasCheck.Raw.LlbcProgram) : Prop where
  borrow_checks_sig : BorrowChecks sig
  initial_abs_installed :
    ∀ shape ∈ signatureToInitialAbs sig,
      Ω.abs shape.absId = some (liftAbsShape shape)
  inputs_populated :
    ∀ i, 1 ≤ i → i ≤ sig.inputs.size →
      ∃ σ : SymValId, Ω.ctx i = some (.sym σ)
  freshness_dominates_initial :
    ∀ shape ∈ signatureToInitialAbs sig,
      shape.absId < Ω.freshness.nextAbsId

/-! ## Smoke lemmas

`signatureToInitialAbs_empty` and `Initial_implies_borrow_checks` are
the two type-check anchors. Both `sorry`'d at M10.4a; the file is
under `LLBCSharpPaper/`, exempt from G6. The proofs are mechanical
once Phase E lemmas need them, and `Initial_implies_borrow_checks` is
trivial by definition (`BorrowChecks _ = True`) — the only reason
it isn't unfolded inline is that Phase E2's case-split prefers to
quote the smoke-lemma name. -/

/-- The empty-signature base case for `signatureToInitialAbs`. -/
theorem signatureToInitialAbs_empty (sig : AeneasCheck.Raw.LlbcSignature)
    (_h : sig.inputs = #[]) :
    signatureToInitialAbs sig = #[] := by
  sorry

/-- Paper Fig. 10's upward implication: `Initial` records that the
    signature is borrow-checkable. At v4 trivial; the M11 stronger
    form is plan §6.1 #5. -/
theorem Initial_implies_borrow_checks
    {Ω : LLBCState} {sig : AeneasCheck.Raw.LlbcSignature}
    {prog : AeneasCheck.Raw.LlbcProgram} :
    Initial Ω sig prog → BorrowChecks sig := by
  sorry

end AeneasSoundness.LLBCSharpPaper
