import AeneasSoundness.LLBCSharpPaper.Step

/-!
# Per-entry `JoinEntryStep` lemmas (M10.2r, C18-C22)

Phase-C bundle for the six `JoinRule` constructors. Each lemma names
the paper-side `JoinEntryStep` constructor that fires for one
`JoinEntry` rule, with the freshness / shape premises spelled out as
explicit parameters so the C23 assembly (`stepJoin_witnessed_sound`)
can chain them inside its `JoinChain` induction without re-deriving the
constructor signatures.

## Why one bundled commit instead of five

Plan §3.2 originally scheduled C18-C22 as five separate commits, each
holding one per-rule sub-soundness lemma; the §3.3 / §8.2 parallelism
discussion went further and recommended factoring them into five
sibling files so a 5-wide worktree batch could fire. That cadence
assumed the per-entry lemmas would bundle *replayer-correspondence*
(connecting `concretise st_i = Ω_i` for each entry's local update).
The replayer's `stepJoin`, however, performs a *wholesale* state
replacement — `newEnv := result.env.foldl …`, `prunedLoans := …` —
not per-entry incremental updates. There is no `stepJoinEntry`
function whose soundness a per-entry lemma could discharge.

The honest factoring is therefore:

* **Per-entry lemmas (this file)** — paper-side facts. Each is a
  thin wrapper over a `JoinEntryStep` constructor that lifts implicit
  arguments to explicit parameters so the assembly can quote the
  premises by name. ~5-10 LOC each; no proof difficulty.
* **C23 / `stepJoin_witnessed_sound`** — the substantive lemma.
  Inducts over `witnesses.toList`, applies the per-entry helpers
  below to build a `JoinChain`, and proves the chain's terminal
  state equals `concretise st'` where `st'` is the replayer's
  wholesale output. The "fresh abs" gap (plan §11.1 #1, §3.4 risk
  on join algebra) lands here.

The bundle adds zero `sorry`s: the per-entry lemmas are all
discharged by the matching `JoinEntryStep` constructor. The single
`sorry` on `stepJoin_witnessed_sound` in `StepEventSound.lean` stays
in place until C23 closes it.
-/

namespace AeneasSoundness.Soundness.JoinLemmas

open AeneasCheck.Raw
open AeneasSoundness.LLBCSharpPaper

/-- C18 / M10.2r — `Join-Same` (Fig. 11). Both branches agreed on the
    local's value; the result inherits without state change. Pure
    constructor witness; no premises. -/
theorem joinSame_step (Ω : LLBCState) (localId : LocalId) :
    JoinEntryStep Ω ⟨localId, .joinSame⟩ Ω :=
  JoinEntryStep.same

/-- C19 / M10.2r — `Join-Symbolic` (Fig. 11). Branches differed on a
    borrow-free value; a fresh symbolic value replaces the local. The
    `freshSv`-freshness premise is what `Valid.join`'s `JoinChain`
    existential supplies; `bumpSymValId` is the no-op `concretise`
    matches (`State.lean:144`). -/
theorem joinSymbolic_step (Ω : LLBCState) (localId : LocalId)
    (freshSv : SymValId) (hFresh : Ω.symValIdFresh freshSv) :
    JoinEntryStep Ω ⟨localId, .joinSymbolic freshSv⟩
      ((Ω.setLocal localId (.sym freshSv)).bumpSymValId freshSv) :=
  JoinEntryStep.symbolic hFresh

/-- C20 / M10.2r — `Collapse-Dup-MutBorrow` + `Join-MutBorrows`
    (Fig. 11). Both branches held `&mut` with different loan ids; the
    join introduces `l_fresh` inside a fresh region abstraction
    `abs`. Premises: `l_fresh` fresh and `abs.absId` fresh in `Ω`.

    M9.8 (cert v4): `abs` is now the full `AbsShape` carried by the
    cert, not just an `AbsId`. The post-state lifts the cert's
    shape via `liftAbsShape` (mirroring `LStep.call`'s use of the
    cert's `absSig`) rather than installing a hardcoded canonical
    role multiset. For well-formed certs the OCaml emitter writes
    `abs.roles = [mutBorrow l_left, mutBorrow l_right, mutLoan l_fresh]`
    and `abs.parentAbs = #[]`, so `liftAbsShape abs` reduces to
    the paper's canonical Fig. 11 region abstraction. The bridge
    to the replayer comes for free: `stepJoin` installs `abs` via
    `addAbsShape`, and `concretise st'.abs abs.absId = liftAbsShape abs`
    matches the paper-side post-state by construction. -/
theorem joinMutBorrows_step (Ω : LLBCState) (localId : LocalId)
    (l_left l_right l_fresh : LoanId) (abs : AbsShape)
    (hLoanFresh : Ω.loanIdFresh l_fresh)
    (hAbsFresh : Ω.absIdFresh abs.absId) :
    JoinEntryStep Ω ⟨localId, .joinMutBorrows l_left l_right l_fresh abs⟩
      (((Ω.setLocal localId (.mutBorrow l_fresh .bottom)).bumpLoanId l_fresh).bumpAbsId abs.absId
        |>.setAbs abs.absId (liftAbsShape abs)) :=
  JoinEntryStep.mutBorrows hLoanFresh hAbsFresh

/-- C21 / M10.2r — `Join-Var` (Fig. 11). A whole region abstraction
    is folded into the result; this rule is a marker. State unchanged
    at this entry — the surrounding `EvEndAbs` carries the absorbed
    abs's contents. -/
theorem joinVar_step (Ω : LLBCState) (localId : LocalId) :
    JoinEntryStep Ω ⟨localId, .joinVar⟩ Ω :=
  JoinEntryStep.var

/-- C22a / M10.2r — `Join-Bottom-Other` (Fig. 11). Left was `⊥`;
    right is wrapped into existing abstraction `abs`. Premise:
    `Ω.abs abs = some r` for some `r`. State unchanged at this
    entry. -/
theorem joinBottomOther_step (Ω : LLBCState) (localId : LocalId)
    (abs : AbsId) (r : RegionAbs) (hAbs : Ω.abs abs = some r) :
    JoinEntryStep Ω ⟨localId, .joinBottomOther abs⟩ Ω :=
  JoinEntryStep.bottomOther hAbs

/-- C22b / M10.2r — `Join-Other-Bottom` (Fig. 11). Mirror of
    `joinBottomOther_step`. -/
theorem joinOtherBottom_step (Ω : LLBCState) (localId : LocalId)
    (abs : AbsId) (r : RegionAbs) (hAbs : Ω.abs abs = some r) :
    JoinEntryStep Ω ⟨localId, .joinOtherBottom abs⟩ Ω :=
  JoinEntryStep.otherBottom hAbs

end AeneasSoundness.Soundness.JoinLemmas
