# Paper Proof Comparison — M10 LLBC# Soundness

This document tracks what the M10 campaign formalises in Lean
relative to the LLBC# paper. It is the place to record where the
Lean formalisation diverges from the paper, where the paper relies
on implicit assumptions that have to be made explicit on the way to
machine-checked proof, and where the M10 port omits or deviates from
the paper's surface for pragmatic / soundness-engineering reasons.

The document is a live record updated as new divergences surface.
The Lean source is the ground truth; this file is the explanation.

---

## 1. What we're proving (the theorem chain)

The campaign assembles a four-step chain from a `CrateCert` to PL
safety. All four theorems live under
`AeneasSoundness/Soundness/` and are statements about
the replayer (`AeneasCheck.LLBCSharp.Replay`), the cert (`AeneasCheck.Raw`), and the paper-side
operational model (`AeneasSoundness.LLBCSharpPaper`).

### 1.1 `stepEvent_sound` — per-event soundness (Phase D top-level)

```lean
theorem stepEvent_sound :
    ∀ (ev : Event) (st st' : SymState) (Ω : LLBCState),
      concretise st = Ω →
      stepEvent st ev = .ok st' →
      ∃ Ω', Valid ev Ω ∧ LStep Ω ev Ω' ∧ concretise st' = Ω'
```

Reads as: if the replayer's step succeeds and the pre-state
concretises to the paper state Ω, then the paper-side rule fires
and its post-state matches the replayer's post-state up to
`concretise`.

Discharged by Phase D via case-analysis on `ev`, delegating each
case to the Phase-C per-event lemma matching the constructor / hint.
Phase C ships 23 such lemmas (C1–C23 in the plan).

### 1.2 `replayFun_sound` — per-function soundness (Phase E)

```lean
theorem replayFun_sound :
  ∀ (cc : CrateCert) (f : FunCert) (lfd : LlbcFunDecl)
    (numLocals : Nat) (trace : CheckedTrace),
    f ∈ cc.functions →
    lookupFunDecl cc f = some lfd →
    Replay.replayFun numLocals f = .ok trace →
    ∃ Ω_in Ω_out,
      Initial(Ω_in, lfd.signature, cc.llbcProgram) ∧
      Ω_in ⟶_#* Ω_out ∧
      Final(Ω_out, lfd.signature, trace.finalState) ∧
      borrow_checks# (lfd.signature)
```

Induction on `f.events`, threading `stepEvent_sound`. The exit
check (no `.direct` loan live) maps to the paper's `borrow_checks#`
predicate (paper Fig. 10).

### 1.3 `replayCrate_implies_borrow_checks` — crate corollary (Phase F)

```lean
theorem replayCrate_implies_borrow_checks :
  ∀ (cc : CrateCert),
    Replay.replayCrate cc = .ok _ →
    ∀ f, f ∈ cc.functions →
      ∃ lfd, lookupFunDecl cc f = some lfd ∧ borrow_checks# (lfd.signature)
```

Quantifies `replayFun_sound` over `cc.functions`. The
`lookupFunDecl` totality is supplied by a Phase-F preamble derived
from the M9.7h consistency-pair check
(`Consistency.checkLlbcVsCert`).

### 1.4 `cert_implies_pl_safety` — user-visible payoff (Phase F final)

```lean
corollary cert_implies_pl_safety :
  ∀ (cc : CrateCert) (f : FunCert) (lfd : LlbcFunDecl),
    Replay.replayCrate cc = .ok _ →
    f ∈ cc.functions →
    lookupFunDecl cc f = some lfd →
    ∀ (Ω_pl : PLState) (n : ℕ),
      Initial_pl(Ω_pl, lfd.signature) →
      ¬ (Ω_pl ⊢ lfd.body ⟶_pl^n stuck)
```

The cert-checker tells you: every function in the crate is
PL-safe to execute. Composes `replayCrate_implies_borrow_checks` +
`paper_thm_4_1_safe` + `paper_thm_3_3_pl_refines`.

---

## 2. The trusted base

A `#print axioms cert_implies_pl_safety` at the end of Phase F lists
five domain axioms (plus Lean core). The four `paper_thm_*` axioms
are replaceable by Phase G (optional); `CertGen_faithful` is
forever trusted.

| Axiom | Source | Trusted forever? |
|---|---|---|
| `CertGen_faithful` | OCaml-side honesty (cert v3 broadened post-M9.7) | Yes |
| `paper_thm_3_1_confluence` | LLBC# paper, Theorem 3.1 (placeholder) | No — Phase G |
| `paper_thm_3_3_pl_refines` | LLBC# paper, Theorem 3.3 | No — Phase G |
| `paper_thm_4_1_safe` | LLBC# paper, Theorem 4.1 | No — Phase G |
| `paper_thm_4_2_init` | LLBC# paper, Theorem 4.2 | No — Phase G |

The user pays for the engineering benefit (every cert that passes
is a witness of safe execution) without paying the
Theorem-3.1 port cost. Phase G shrinks the base further; until
then the four paper theorems sit on the LLBC# authors' signed
proofs, which is well-established practice.

---

## 3. Implicit paper assumptions that surface as Lean side conditions

These are not mistakes in the paper. They are invariants the paper
assumes hold (often because they fall out of the surrounding
borrow-checker discipline) and that the Lean formalisation has to
articulate explicitly.

### 3.1 LoanTokenInvariant: unique `mutLoan` token holder

Paper Fig. 3's `Reorg-End-MutBorrow` rule has the premise

```
Ω.ctx x = some (.mutLoan ℓ)
```

with `x` quantified existentially over `LocalId`. The paper relies
on the implicit invariant that **exactly one** local holds the
`.mutLoan ℓ` token at any given time. The replayer's `stepEndBorrow`
scans `st.env.toList` and updates every matching entry; per the
invariant, this updates exactly one entry.

In Lean, we discharge this by taking a Phase-D-dischargeable
`hShape` hypothesis that pins the replayer's post-state to
`stTake.setLocal x v` plus a `hHolder : Ω.ctx x = some (.mutLoan loan)`
hypothesis lifting the holder local to the paper side. The
`LoanTokenInvariant` itself (the uniqueness fact) is intended to
land as a Phase-B `WellFormed` strengthening; Phase D will derive
both `hShape` and `hHolder` from it together with cert emission
discipline. See `StepEventSound.lean` C11–C13 for the contract.

### 3.2 Monotone freshness counters across the replayer

Paper `Ω#.freshness : NonceCounters` is monotone — `bumpLoanId`,
`bumpAbsId`, and `bumpSymValId` are defined as `max old (id+1)` and
no rule erases. The paper-side `LStep.endBorrow_*` constructors
explicitly leave freshness counters untouched.

The replayer, by contrast, stores its loan state as `Std.HashMap Nat
LoanInfo` and `takeLoan b` calls `loans.erase b`. If we derived
`(concretise st).freshness.nextLoanId := maxKeyPlusOne st.loans`,
the counter would *strictly shrink* when `b` was the maximum key —
violating the monotonicity the paper depends on.

This is a soundness-engineering question the paper doesn't address
(it works at the level of the abstract `Ω#`, not at any concrete
representation). The Lean formalisation resolves it via the
`loanIdHwm` field added to `SymState` at M10.1g; see §4.1 below.

---

## 4. Engineering divergences (Lean port adds structure the paper omits)

### 4.1 `SymState.loanIdHwm` — a monotone replayer-side high-water mark

**Where:** `aeneas-lean-checker/AeneasCheck/LLBCSharp/State.lean`,
M10.1g (`SymState.loanIdHwm : Nat := 0`).

**Why:** see §3.2. The paper's monotone `nextLoanId` is realised
on the replayer side by a dedicated field bumped only in `addLoan`
(via `max st.loanIdHwm (b + 1)`) and never touched by `takeLoan` /
`loans.erase`.

**Effect on the soundness lemmas:**
- `concretise.freshness.nextLoanId := st.loanIdHwm`
  (not `maxKeyPlusOne st.loans`; M10.1h).
- `concretise_addLoan` is unconditional (was previously conditional
  on `maxKeyPlusOne st.loans ≤ b`).
- `concretise_takeLoan` closes trivially: `takeLoan` doesn't touch
  `loanIdHwm`, and the soundness side erases the loan from the
  `loans` map but `loans` doesn't contribute to `concretise`'s
  output (loans live transitively inside `ctx`'s `mutLoan` tokens
  and inside `abs`).

**Faithfulness:** zero leakage into the replayer's checker logic.
No code path reads `loanIdHwm` for checker decisions (grep
confirmed at M10.1g time). G1–G4 stay green across the change.

### 4.2 `LLBCState.bumpSymValId` redefined as no-op

**Where:** `aeneas-lean-soundness/AeneasSoundness/LLBCSharpPaper/State.lean`,
M10.2f.

**Why:** several paper rules (`LStep.binop`, `LStep.call`,
`LStep.mutBorrow_*`, `LStep.symExpandMutBorrow`) conclude with
`(...).bumpSymValId σ`. The replayer does not track symbolic-value
ids — `concretise.freshness.nextSymValId := 0` unconditionally. If
the paper's `bumpSymValId` updated the field, every concrete
`LStep` step would diverge from `concretise st'` on the
`nextSymValId` field.

The paper's full model maintains `nextSymValId` for cert-side
monotonicity (every cert event picks a σ ≥ `nextSymValId`); this
is a *cert-emission* invariant that
`CertGen_faithful` already promises us. The soundness theorem
we want does not need to reprove it.

**Faithfulness:** the paper's model is *strictly stronger* than
what M10 soundness depends on. The no-op is a deliberate pruning
of a degree of freedom that the paper leaves free; the σ
parameter on each `LStep` constructor remains, so the rules still
take a σ premise that picks 0 when the soundness lemma instantiates.

### 4.3 `Valid.proj _ _ _ := False` (paper has no `LStep.proj` at M10)

**Where:** `LLBCSharpPaper/Valid.lean:110`.

**Why:** `Event.proj` is in the cert schema (legacy; revived in
M11+) but no Phase-A `LStep` rule fires on it. The replayer's
`Replay.lean:50` already rejects `.proj` events as a hard cert
violation under M10's coverage. Encoding `Valid (.proj …) := False`
keeps `Valid_iff_LStep_exists` vacuously consistent on the branch.

**Faithfulness:** the paper does not include `proj` events in its
M10 surface, so this is consistent with the paper's scope. Phase D's
`stepEvent_sound` case-split uses `False.elim` (or the replayer
rejection) on the `proj` branch.

### 4.4 Phase-D-dischargeable result-shape hypotheses (C2–C15)

**Pattern:** Phase-C per-event lemmas take extra hypotheses that
restrict the replayer's nondeterministic / loop-driven shape to
something matchable against an `LStep` constructor:

- `hPlaceProj : place.projection = #[]` — for `move`, `copy`,
  `sharedBorrow`, `mutBorrow_*` (the replayer's `placeRootLocal`
  ignores the projection chain; the paper's `Ω.resolvePlace` walks
  it).
- `hPlaceEnv : ∃ v, st.env[place.local_]? = some v` — for the same
  family (declared-local existence).
- `hLoanFresh : st.loanIdHwm ≤ loan` — paper's `Ω.loanIdFresh ℓ`.
- `hShape : stepEvent st ev = .ok <known-form>` — for endBorrow C11–C13,
  pinning the post-state without unrolling the env-scan loop.
- `hHolder : Ω.ctx x = some (.mutLoan ℓ)` — endBorrow holder
  uniqueness.
- `hParentInHwm : parent < st.loanIdHwm` — stepReborrow (C14): forces
  the paper-side `Ω.bumpLoanId parent` to be a no-op so the strict
  M9.6 pre-add-parent branch agrees with the simpler paper rule.
- `hAbsSigEmpty : absSig = #[]` — stepCall (C15a): restriction to the
  empty-absSig subset pending the M10.0m Phase-A revision.

**Faithfulness:** these are *not* extra trust. Each is intended to be
discharged in Phase D from either (a) a Phase-B `WellFormed`
strengthening, (b) the cert emission discipline carried by
`CertGen_faithful`, or (c) a future Phase-A revision (M10.0m). The
hypotheses are Phase-D's interface; Phase C delivers the lemmas
*conditional* on them, Phase D delivers the discharges.

---

## 5. Open Phase-A port gaps (incomplete vs the paper)

These are places where the current Lean port does not yet capture
what the paper says. They are flagged for the M10.0m Phase-A
revision and tracked in `.m10-soundness-progress.md` Blockers.

### 5.1 `LStep.call` does not install `absSig` in the post-state

**Where:** `LLBCSharpPaper/Step.lean:390-395`.

```lean
| call {Ω : LLBCState} {fn callId : Nat} {fnName : String}
    {args : Array SymExpr} {dst : Place} {regionAbs : Array AbsId}
    {absSig : Array AbsShape} {σ : SymValId} :
    Ω.symValIdFresh σ →
    LStep Ω (.call fn callId fnName args dst regionAbs absSig)
      ((Ω.setLocal dst.local_ (.sym σ)).bumpSymValId σ)
```

The constructor's own docstring (Step.lean:386-388) says:

> Post-state: for each `AbsShape r` in `absSig`, install
> `Ω.abs r.absId := some (RegionAbs.singleton ...)`; bump
> `nextAbsId` past every named abs. `dst` is written with a fresh
> symbolic value (the call result).

— but the implementation only writes the dst local. The replayer's
`stepCall` *does* fold `absSig` into `absRegistry`. So the two
sides diverge as soon as `absSig ≠ #[]`.

**The paper is correct.** The Lean port at M10.0g was incomplete.
The M10.0m revision (next session priority) fixes this.

### 5.2 `LStep.endAbs` cannot fire pre-M10.0m

**Where:** `LLBCSharpPaper/Step.lean:407-412`.

```lean
| endAbs {Ω : LLBCState} {abs : AbsId} {finalValues : Array SymExpr}
    {releasedLoans : Array LoanId} {tokenClearLocals : Array LocalId}
    {r : RegionAbs} :
    Ω.abs abs = some r →
    LStep Ω (.endAbs abs finalValues releasedLoans tokenClearLocals)
      (Ω.removeAbs abs)
```

The premise `Ω.abs abs = some r` requires the abs to have been
previously installed. Until §5.1 is fixed, no `LStep.call` ever
installs an abs, so this premise is universally `False` and C16
(`stepEndAbs_sound`) is vacuous. Conversely the replayer's
`stepEndAbs` does *not* erase from `absRegistry`, so `concretise
st'.abs = concretise st.abs ≠ Ω.removeAbs abs`. M10.0m must also
make `stepEndAbs` erase from `absRegistry` (a one-line replayer
change; no other code reads erased entries — grep-confirmed).

### 5.3 Other anticipated Phase-A revisions

Plan §11.3 and §14.1–14.3 anticipate three further M9.8 schema
bumps as Phase-C lemmas surface them:

- `EvJoin.JoinMutBorrows.absRoles` — the join rule may need an
  abs-role witness array in the cert payload.
- `EvLoopInv.fixpointWitness` — fixpoint witnessing the loop
  invariant.
- `EvCall.instSig` — the callee's instantiation signature, when the
  paper's E-Call requires it.

These are *cert-schema* extensions and would be M9.8-level work,
not Phase-A revisions. They are escalation-required per the
orchestration prompt §6.1 #4. None has surfaced as of Session 5.

---

## 6. Out-of-scope (deferred or M11+)

- **`EvProj` revival.** Plan §14.8 schedules this for M11+. M10
  treats `Event.proj` as a hard cert violation.
- **Phase G paper-theorem ports.** Theorems 3.1, 3.3, 4.1, 4.2 stay
  as `paper_thm_*` axioms through the M10 done condition (after #47).
  Phase G (M10.6a–p, +15 commits) is optional and may be deferred to
  M11+ per plan §7.1.
- **Non-empty-absSig C15 and dependents (C16, C17).** Blocked on
  M10.0m. Phase D will need to either restrict the soundness theorem
  to the empty-absSig fixture subset or land M10.0m first.

---

## 7. Document maintenance

Update this file when:

- A new Phase-C lemma surfaces a paper-vs-port mismatch.
- An M10.0m / future Phase-A revision lands (move the entry from §5
  to §4 with the resolution sketch).
- A `paper_thm_*` axiom is discharged by Phase G (move the entry
  from §2 to a §4 entry with the proof sketch reference).
- A new soundness-engineering choice (like `loanIdHwm`,
  `bumpSymValId` no-op) is added, with its rationale.

Keep entries terse but precise — file/line refs to the Lean source,
plus a one-paragraph explanation of *why* the divergence is sound.
This is the document a reader will reach for when asking "does the
Lean proof actually correspond to the paper proof, and where are
the joints?"
