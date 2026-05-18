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
| `sharedBorrow` / `mutBorrow_direct` / `mutBorrow_loopOwned` | dropped M10.x.4 — paper-side rules' `Ω.resolvePlace p = some v` premises were vestigial (the bound `v` was not in the post-state); freshness clauses are replayer-discharged via M10.x.2's reject paths |
| `reborrow` | dropped M10.x.4 — paper-side rule split into `LStep.reborrow` (tracked-parent) + `LStep.reborrow_untracked` (untracked-parent pre-add), mirroring the replayer's two-branch shape; `hChildFresh` is replayer-discharged via M10.x.2 |
| `mutBorrow_inAbsReborrow` | dropped M10.x.5 — paper-side rule's `Ω.abs absId = some r` premise was vestigial (the bound `r` was not in the post-state); HWM clause replayer-discharged via M10.x.2 |

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

/-! ### sharedBorrow / mutBorrow_direct / mutBorrow_loopOwned —
    dropped (M10.x.4)

The previous extractors promised
`place.projection = #[]`,
`∃ v, st.env[place.local_]? = some v`,
and `st.loanIdHwm ≤ loan`. The first two clauses were not
guaranteed by cert emission: the M10.x.2 fixture-corpus scan found
1187/2000 fixtures with non-empty projections on mut/shared borrows
and 1181/2000 with never-env-bound source locals (function arguments
not pre-populated by `SymState.empty`). M10.x.4 dropped the
existential `v` from `LStep.sharedBorrow` / `.mutBorrow_direct` /
`.mutBorrow_loopOwned` (the bound value was not used in the
post-state); the per-event lemmas now close from `hStep + hRep`
alone. The HWM-freshness clause is discharged from `hStep` via
M10.x.2's `stepMutBorrow` / `stepSharedBorrow` monotone-allocator
reject paths. -/

/-! ### mutBorrow_inAbsReborrow — dropped (M10.x.5)

The previous extractor promised `∃ r, st.absRegistry[absId]? = some r`
and `st.loanIdHwm ≤ loan`. The HWM clause is replayer-discharged via
M10.x.2's `stepMutBorrow` monotone-allocator reject path. The
abs-registry existential was vestigial in the paper rule: a pre-flight
scan of `tests/llbc/*.cert.json` found 112/783 fixtures where the
OCaml emitter references `inAbsReborrow.absId` for an ambient
function-input abstraction whose installation is *not* event-recorded
(the abs is part of the caller-side `&mut` argument; Consistency.lean's
`seenAbs` tolerates exactly this case). Keeping the existential would
have falsified `CertGen_faithful` on those certs. M10.x.5 drops the
`{r : RegionAbs}` binder + `Ω.abs absId = some r` premise from
`LStep.mutBorrow_inAbsReborrow` (same vestigial-existential pattern as
M10.x.4's drop for `.direct` / `.loopOwned` / `.sharedBorrow`): the
post-state `(Ω.bumpLoanId ℓ).bumpSymValId σ` never references `r`, so
the existence claim contributed nothing to the rule's operational
meaning. The per-event lemma closes from `hStep` + `hRep` alone. -/

/-! ### reborrow — dropped (M10.x.4)

The previous extractor promised `st.loanIdHwm ≤ child ∧
parent < st.loanIdHwm`. The child clause is replayer-discharged
via M10.x.2's `stepReborrow` reject path. The parent clause was
NOT replayer-discharged (95 fixtures emit a reborrow with parent
allocated inside an untracked abs); M10.x.4 splits the paper-side
`LStep.reborrow` rule into two constructors mirroring the replayer's
two branches (tracked-parent vs untracked-parent pre-add), so the
per-event lemma picks the matching constructor by `by_cases` on
`st.loans.contains parent`. No paper-side parent-HWM premise
remains. -/

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
