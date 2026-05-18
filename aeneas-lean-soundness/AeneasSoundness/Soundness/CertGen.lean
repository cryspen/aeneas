import AeneasCheck.LLBCSharp.Replay
import AeneasSoundness.LLBCSharpPaper.Step
import AeneasSoundness.Soundness.Concretise.Defn

/-!
# `CertGen_faithful` — the OCaml-side honesty axiom (per-event family)

This file is the first place in `AeneasSoundness/` where the trusted
base of the M10 campaign is declared in Lean. Plan §0.3 sets the
charter: `CertGen_faithful` is the OCaml-side honesty assumption that
Aeneas's interpreter (in `src/cert/CertGen.ml` + `src/cert/LlbcJson.ml`)
emits certs that are real interpreter traces *of the LLBC the same
cert embeds*. We have no Lean port of the OCaml emitter to typecheck
against; the axiom is the bridge.

Per the orchestrator's recommendation, the axiom is declared as a
*family* of per-event extractors, one per Phase-C per-event lemma's
Phase-D-dischargeable hypotheses (rather than one monolithic premise
bundle). This keeps the trusted-base audit surface explicit — each
extractor names precisely the cert-emission promise it depends on —
and lets the Phase-D dispatcher in `StepEventSound.lean` extract a
lemma's premises with a one-line pattern match.

## Scope (Phase D)

Each extractor packages the Phase-D-dischargeable hypotheses required
by one Phase-C lemma:

| Extractor | Discharges (for stepX_sound) |
|---|---|
| `sharedBorrow` | place-projection-empty + env-some + `st.loanIdHwm ≤ loan` |
| `mutBorrow_direct` / `mutBorrow_loopOwned` | as `sharedBorrow` |
| `mutBorrow_inAbsReborrow` | `∃ r, st.absRegistry[absId]? = some r` + loan-fresh |
| `reborrow` | `st.loanIdHwm ≤ child ∧ parent < st.loanIdHwm` |
| `endAbs` | abs-registry-lookup + (stPre, hConcPre, hShape) preamble triple |
| `symExpandMutBorrow` | `substLocals = #[] ∧ substLoans = #[]` + `bid` freshness |
| `loopInv` | `loanRegistry = #[]` (paper LStep.loopInv is a no-op) |
| `endBorrow_direct_witness` | for `LoanKind ∈ {.direct, .lazyExpand}`: holder local `x` + result value `v` + `hShape` |
| `join` | `(Ω', hChain, hConcMatch)` triple |
| `proj` | unreachable — replayer rejects, no extractor needed |
| `call` (dst-in-bounds) | dropped M10.4a-post — provable by `hStep` inversion |
| `endBorrow_takeOk` | dropped M10.4a-post — provable by `hStep` inversion |
| `endBorrow_reborrow_witness` | dropped M10.4a-post — provable by `hStep` inversion |
| `endBorrow_shared_witness` | dropped M10.4a-post — provable by `hStep` inversion |
| `move` / `copy` | dropped M10.x.3 — paper-side `LStep.move`/`.copy` were reshaped via `resolvePlaceRoot` to mirror the replayer's root-local semantics; no extractor needed |

## What's NOT here

* The four `paper_thm_*` axioms (confluence, pl_refines, safe, init)
  stay deferred to Phase G; they're not consumed by `stepEvent_sound`.
* The Phase E `replayFun_sound` premises (event-list well-formedness,
  `lookupFunDecl` totality) are *not* declared yet — they're additional
  CertGen_faithful obligations that Phase E will add. Phase D declares
  only what `stepEvent_sound` consumes.

## Why each extractor includes `hStep`

Most extractors take the replayer's `hStep : stepEvent st ev = .ok st'`
as a precondition. The intent: a property is only promised when the
replayer accepts the event — i.e., the cert "validated" this step.
Vacuous-with-bad-cert is the right framing: a bad cert that triggers
a replayer error doesn't constrain what `CertGen_faithful` promises.
(For state-independent properties like place-projection emptiness the
hypothesis is informationally redundant but kept for uniformity.)
-/

namespace AeneasSoundness.Soundness

open AeneasCheck.Raw AeneasCheck.LLBCSharp
open AeneasSoundness.LLBCSharpPaper (LLBCState JoinChain)

/-- Local abbrev so the family signatures stay readable. Mirrors the
    `abbrev concretise` re-export at the top of `StepEventSound.lean`. -/
private abbrev concretise : SymState → LLBCState := Concretise.concretise

namespace CertGen_faithful

/-! ### Move / copy — dropped (M10.x.3)

The previous extractors promised `projection = #[]` and
`st.env[src.local_]?.isSome` so that the paper-side rule's
`Ω.resolvePlace src = some v` premise could fire. Neither
clause is guaranteed by cert emission: the M10.x.2 fixture-corpus
scan found 1187/2000 fixtures with non-empty projections on
Move/Copy and 1181/2000 with never-env-bound src locals
(function arguments, which `SymState.empty` does not pre-populate).

M10.x.3's fix re-shaped `LStep.move` / `LStep.copy` to mirror the
replayer's root-local semantics via
`LLBCState.resolvePlaceRoot` — a projection-tolerant read of the
root local, defaulted to `.bottom` for undeclared locals. With
the rule premise-free, the extractors are no longer needed; the
per-event lemmas `stepMove_sound` / `stepCopy_sound` close from
`hStep` + `hRep` alone. -/

/-! ### Borrow events — place-projection + env-resident + loan-id-fresh

The freshness clause `st.loanIdHwm ≤ loan` is the monotone discipline
the OCaml allocator promises; the M10.1g `loanIdHwm` field on
`SymState` is the soundness-side mirror. -/

axiom sharedBorrow (st st' : SymState) (loan sbId : Nat)
    (place : Place) (symval : Nat)
    (hStep : stepEvent st (.sharedBorrow loan sbId place symval) = .ok st') :
    place.projection = #[] ∧
    (∃ v, st.env[place.local_]? = some v) ∧
    st.loanIdHwm ≤ loan

axiom mutBorrow_direct (st st' : SymState) (loan : Nat) (place : Place)
    (symval : Nat)
    (hStep : stepEvent st (.mutBorrow loan place symval .direct) = .ok st') :
    place.projection = #[] ∧
    (∃ v, st.env[place.local_]? = some v) ∧
    st.loanIdHwm ≤ loan

axiom mutBorrow_inAbsReborrow (st st' : SymState) (loan : Nat) (place : Place)
    (symval : Nat) (absId : Nat)
    (hStep : stepEvent st (.mutBorrow loan place symval (.inAbsReborrow absId)) = .ok st') :
    (∃ r, st.absRegistry[absId]? = some r) ∧ st.loanIdHwm ≤ loan

axiom mutBorrow_loopOwned (st st' : SymState) (loan : Nat) (place : Place)
    (symval : Nat) (loopId : Nat)
    (hStep : stepEvent st (.mutBorrow loan place symval (.loopOwned loopId)) = .ok st') :
    place.projection = #[] ∧
    (∃ v, st.env[place.local_]? = some v) ∧
    st.loanIdHwm ≤ loan

/-! ### Reborrow — child fresh + parent in HWM

`hParentInHwm : parent < st.loanIdHwm` rests on cert discipline that
the parent loan was previously allocated (so it's strictly below the
current HWM). -/

axiom reborrow (st st' : SymState) (child parent : Nat) (place : Place)
    (parentLive : Bool) (parentAbs : Option Nat)
    (hStep : stepEvent st (.reborrow child parent place parentLive parentAbs) = .ok st') :
    st.loanIdHwm ≤ child ∧ parent < st.loanIdHwm

/-! ### EndAbs — abs-in-registry + (stPre, hConcPre, hShape) preamble

C16's `stepEndAbs_sound` collapses the replayer's loan-erase +
token-clear preambles into a single `concretise`-preserving step
parameterised by `stPre`. The CertGen_faithful promise carries the
matching abs-registry entry and the preamble-result-shape. -/

axiom endAbs (st st' : SymState) (absId : Nat) (finalValues : Array SymExpr)
    (releasedLoans : Array Nat) (tokenClearLocals : Array Nat)
    (hStep : stepEvent st (.endAbs absId finalValues releasedLoans tokenClearLocals) = .ok st') :
    ∃ (shape : AbsShape) (stPre : SymState),
      st.absRegistry[absId]? = some shape ∧
      concretise stPre = concretise st ∧
      stepEvent st (.endAbs absId finalValues releasedLoans tokenClearLocals) =
        .ok (stPre.removeAbsShape absId)

/-! ### SymExpandMutBorrow — no-substitution subset + bid fresh

C17 closes for the empty-`substLocals` / empty-`substLoans` subset;
the substitution-bearing subset awaits a Phase-A surface
strengthening (`SubstScope_Complete`). Cert-emission discipline is
that the OCaml interpreter produces empty subst arrays whenever the
ctx tracks no parameter / abstraction-bound locals that need
rewriting — true for the M10 fixture set; cert v5 may broaden. -/

axiom symExpandMutBorrow (st st' : SymState) (svId bid innerSv : Nat)
    (parentAbs : Option Nat) (substLocals substLoans : Array Nat)
    (hStep : stepEvent st
      (.symExpandMutBorrow svId bid innerSv parentAbs substLocals substLoans) = .ok st') :
    substLocals = #[] ∧ substLoans = #[] ∧
    st.loans.contains bid = false ∧ st.loanIdHwm ≤ bid

/-! ### LoopInv — empty-loanRegistry subset

The replayer's `stepLoopInv` adds `.reborrow` loans for each
`loanRegistry` entry whose id isn't already in `st.loans`. The paper
side's `LStep.loopInv` is `Ω → Ω` (no state change). The two coincide
iff the cert's `loanRegistry` is empty, i.e. the loop's input
abstractions were already registered by prior `stepCall`s. -/

axiom loopInv (st st' : SymState) (loopId : Nat) (invariant : StateSummary)
    (loanRegistry : Array (Nat × Nat))
    (hStep : stepEvent st (.loopInv loopId invariant loanRegistry) = .ok st') :
    loanRegistry = #[]

/-! ### EndBorrow — `.direct`/`.lazyExpand` result-shape witness

The replayer's `stepEndBorrow` opens with `match st.takeLoan loan`
and dispatches on `LoanKind`. The `none`-fail path, the `.reborrow`
arm result-shape, and the `.shared` arm result-shape are all
hStep-derivable by inversion through the replayer (M10.4a-post). The
remaining `.direct`/`.lazyExpand` shape — which env local holds the
`mutLoan` token plus the returned value — is genuine cert content
not recoverable from the replayer alone. -/

/-- For `LoanKind ∈ {.direct, .lazyExpand}`: there exists a holder
    local `x` in the paper-side ctx and the cert's `restore.givenBack`
    reduces to some `v` such that the replayer's post-state is exactly
    `stTake.setLocal x v`. The C11 lemma consumes this triple. -/
axiom endBorrow_direct_witness (st st' : SymState) (loan : Nat)
    (restore : RestoreInfo) (Ω : LLBCState) (hRep : concretise st = Ω)
    (hStep : stepEvent st (.endBorrow loan restore) = .ok st')
    (li : LoanInfo) (stTake : SymState)
    (hTake : st.takeLoan loan = some (li, stTake))
    (hKind : li.kind = .direct ∨ li.kind = .lazyExpand) :
    ∃ (x : Nat) (v : Val),
      Ω.ctx x = some (.mutLoan loan) ∧
      stepEvent st (.endBorrow loan restore) = .ok (stTake.setLocal x v)

/-! ### Join — chain terminal + concretise match

C23's `stepJoin_witnessed_sound` takes a `(Ω', hChain, hConcMatch)`
triple. The chain `JoinChain Ω witnesses.toList Ω'` is the
sequential composition of the per-entry `JoinEntryStep`s; the
cert's join-witness algebra IS the chain. The
`concretise st' = Ω'` clause is the structural match between the
replayer's wholesale env replace + abs-install fold (post-M9.8) and
the chain's terminal env / abs state.

This extractor packages the full triple. An earlier draft considered
factoring the chain construction as a separate `buildJoinChain`
helper proved by induction over `witnesses.toList` via the per-entry
`JoinLemmas.join<Rule>_step` helpers, with CertGen_faithful supplying
the freshness / abs-existence premises per entry. That factoring is
cleaner-on-paper but requires CertGen_faithful to promise premises
about the *running* intermediate states Ω_i, not just the initial Ω
— the freshness counters change at each step. The bundled
formulation (this axiom) is simpler and equally trust-minimal: the
chain's existence + the terminal-match are both pure facts about the
trace's join algebra, which the cert is the witness of. -/

axiom join (st st' : SymState) (left right result : StateSummary)
    (witnesses : Array JoinEntry) (Ω : LLBCState) (hRep : concretise st = Ω)
    (hStep : stepEvent st (.join left right result witnesses) = .ok st') :
    ∃ Ω', JoinChain Ω witnesses.toList Ω' ∧ concretise st' = Ω'

end CertGen_faithful

end AeneasSoundness.Soundness
