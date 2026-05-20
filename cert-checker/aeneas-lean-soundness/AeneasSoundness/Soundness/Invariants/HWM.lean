import AeneasCheck.LLBCSharp.Replay

/-!
# HWM (High-Water-Mark) invariant on `SymState`

Plan §"Lean-side migration sequence" row 1 (M10.x.1). This file
states the trace-level invariant the M10.1g/i `loanIdHwm` and
`absIdHwm` fields were introduced to support: every loan id
currently in `SymState.loans` sits strictly below `loanIdHwm`, and
every abs id currently in `SymState.absRegistry` sits strictly
below `absIdHwm`. The HWMs are bumped (and never decreased) by
`addLoan` / `addAbsShape`; `takeLoan` / `removeAbsShape` shrink
`loans` / `absRegistry` and leave the HWM untouched, mirroring the
paper's monotone `NonceCounters` field.

## Scope (M10.x.1)

This commit only states + proves the structural invariant lemmas;
it does NOT consume any `CertGen_faithful.*` axiom. The downstream
M10.x.2 replayer strengthening + M10.x.4 / M10.x.5 / M10.x.7 axiom
drops invoke these lemmas to discharge "the loan id is fresh w.r.t.
the paper-side `freshness.nextLoanId`" (via the existing
`Concretise.concretise_freshness` bridge) without trusting the
OCaml emitter for it.

The replayer's `stepJoin` (`AeneasCheck.LLBCSharp.Step.lean:506`)
inserts loan ids from `result.liveLoans` into the post-state's
`loans` map *without* routing the insert through `addLoan`, so the
`loanBound` clause can be broken when the cert's join names a
fresh loan id not already in `st.loans`. The M10.x.10 join
campaign closes that gap; for M10.x.1 we factor the join case
behind a per-event admissibility predicate
(`eventRespectsHwm`) that the caller supplies as a structural
promise.

The two imperative-body events `endBorrow` (env-walk for-loop)
and `endAbs` (loan-erase + token-clear for-loops) take a
post-state "shape" precondition that pins `st'`'s
HWM-relevant fields to `stTake.loans` / `st.absRegistry.erase
absId`. The precondition is dischargeable by direct unfolding
in downstream consumers (or by extending the replayer's
contract in M10.x.9 / M10.x.6); this file does not consume any
imperative-body internals.

## Trust impact

Zero. This file adds only proved structural lemmas; no `axiom` /
`sorry` / `unsafe`. `tests/axioms.golden.txt` byte-for-byte
unchanged from the M10.x.0 tip.
-/

namespace AeneasSoundness.Soundness.Invariants

open AeneasCheck.LLBCSharp
open AeneasCheck.Raw

/-! ## Invariant statement -/

/-- Monotone-HWM bound invariant. The two clauses are independent
    (loans and absRegistry track different id families); we bundle
    them so per-event preservation is a single statement. -/
structure HwmInvariant (st : SymState) : Prop where
  /-- Every loan id currently in `st.loans` is strictly below the
      monotone `loanIdHwm`. -/
  loanBound : ∀ b, st.loans.contains b = true → b < st.loanIdHwm
  /-- Every abs id currently in `st.absRegistry` is strictly below
      the monotone `absIdHwm`. -/
  absBound  : ∀ a, st.absRegistry.contains a = true → a < st.absIdHwm

/-- Loan-only half of `HwmInvariant`. The downstream consumer
    `concretise_loopInvRegisterLoan` only needs the `loanBound`
    clause (the skip-branch of `loopInvRegisterLoan` requires
    `b ∈ st.loans → b < st.loanIdHwm`); the `absBound` clause
    is irrelevant. Splitting it out lets us prove a stronger
    preservation theorem (unconditional, no `eventRespectsHwm`
    promise needed for the loans-only events `join` / `endAbs`
    / `endBorrow` / `symExpandMutBorrow`) that Phase E threads
    through `replayFun_sound`. -/
structure LoanHwmInvariant (st : SymState) : Prop where
  /-- Every loan id currently in `st.loans` is strictly below the
      monotone `loanIdHwm`. Identical clause to
      `HwmInvariant.loanBound`. -/
  loanBound : ∀ b, st.loans.contains b = true → b < st.loanIdHwm

/-- Downcast: the loan half of `HwmInvariant` IS `LoanHwmInvariant`. -/
def HwmInvariant.toLoanHwm {st : SymState} (h : HwmInvariant st) :
    LoanHwmInvariant st :=
  ⟨h.loanBound⟩

namespace HwmInvariant

/-! ## Empty-state base case -/

/-- The freshly-initialised `SymState.empty n` satisfies the
    invariant vacuously (both `loans` and `absRegistry` are empty). -/
theorem empty (n : Nat) : HwmInvariant (SymState.empty n) := by
  refine ⟨?_, ?_⟩ <;> intro k hContains
  · simp [SymState.empty] at hContains
  · simp [SymState.empty] at hContains

/-! ## Mutator-level preservation helpers

One lemma per `SymState` mutator. Each per-event preservation
proof below dispatches to a chain of these. -/

/-- `setLocal` only mutates `env`; loans / absRegistry / HWMs
    unchanged. -/
theorem preserve_setLocal {st : SymState} (hInv : HwmInvariant st)
    (l : Nat) (v : Val) :
    HwmInvariant (st.setLocal l v) := by
  refine ⟨?_, ?_⟩
  · intro b hb; exact hInv.loanBound b hb
  · intro a ha; exact hInv.absBound a ha

/-- Rewriting `env` to any value is invisible to `HwmInvariant`. -/
theorem preserve_env_replace {st : SymState} (hInv : HwmInvariant st)
    (newEnv : Std.HashMap Nat Val) :
    HwmInvariant { st with env := newEnv } := by
  refine ⟨?_, ?_⟩
  · intro b hb; exact hInv.loanBound b hb
  · intro a ha; exact hInv.absBound a ha

/-- `addLoan b inner kind` bumps `loanIdHwm` to `max loanIdHwm
    (b+1)`. The new entry satisfies `b < b+1 ≤ max …`; existing
    entries inherit from the old HWM (≤ new HWM). -/
theorem preserve_addLoan {st : SymState} (hInv : HwmInvariant st)
    (b : Nat) (inner : Val) (kind : LoanKind) :
    HwmInvariant (st.addLoan b inner kind) := by
  refine ⟨?_, ?_⟩
  · intro b' hContains
    simp only [SymState.addLoan, Std.HashMap.contains_insert,
      Bool.or_eq_true, beq_iff_eq] at hContains
    rcases hContains with heq | hold
    · subst heq
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
    · exact Nat.lt_of_lt_of_le (hInv.loanBound _ hold) (Nat.le_max_left _ _)
  · intro a ha; exact hInv.absBound a ha

/-- `addAbsShape shape` bumps `absIdHwm` to `max absIdHwm
    (shape.absId+1)`. Mirrors `preserve_addLoan`. -/
theorem preserve_addAbsShape {st : SymState} (hInv : HwmInvariant st)
    (shape : AbsShape) :
    HwmInvariant (st.addAbsShape shape) := by
  refine ⟨?_, ?_⟩
  · intro b hb; exact hInv.loanBound b hb
  · intro a' hContains
    simp only [SymState.addAbsShape, Std.HashMap.contains_insert,
      Bool.or_eq_true, beq_iff_eq] at hContains
    rcases hContains with heq | hold
    · subst heq
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
    · exact Nat.lt_of_lt_of_le (hInv.absBound _ hold) (Nat.le_max_left _ _)

/-- `takeLoan b = some (li, st')` erases entry `b`. Bound on the
    remaining loans is inherited from `hInv`. -/
theorem preserve_takeLoan {st : SymState} (hInv : HwmInvariant st)
    {b : Nat} {li : LoanInfo} {st' : SymState}
    (hTake : st.takeLoan b = some (li, st')) :
    HwmInvariant st' := by
  unfold SymState.takeLoan at hTake
  split at hTake
  · cases hTake
  · simp only [Option.some.injEq, Prod.mk.injEq] at hTake
    obtain ⟨_, hs⟩ := hTake
    subst hs
    refine ⟨?_, ?_⟩
    · intro b' hContains
      simp only [Std.HashMap.contains_erase, Bool.and_eq_true,
        Bool.not_eq_true'] at hContains
      exact hInv.loanBound _ hContains.2
    · intro a ha; exact hInv.absBound a ha

/-- Raw `loans.erase b` (no `Option` wrapper). Used by
    `stepEndAbs`'s released-loan fold. -/
theorem preserve_loans_erase {st : SymState} (hInv : HwmInvariant st)
    (b : Nat) :
    HwmInvariant { st with loans := st.loans.erase b } := by
  refine ⟨?_, ?_⟩
  · intro b' hContains
    simp only [Std.HashMap.contains_erase, Bool.and_eq_true,
      Bool.not_eq_true'] at hContains
    exact hInv.loanBound _ hContains.2
  · intro a ha; exact hInv.absBound a ha

/-- `removeAbsShape absId` erases registry entry `absId`. -/
theorem preserve_removeAbsShape {st : SymState} (hInv : HwmInvariant st)
    (absId : Nat) :
    HwmInvariant (st.removeAbsShape absId) := by
  refine ⟨?_, ?_⟩
  · intro b hb; exact hInv.loanBound b hb
  · intro a' hContains
    simp only [SymState.removeAbsShape, Std.HashMap.contains_erase,
      Bool.and_eq_true, Bool.not_eq_true'] at hContains
    exact hInv.absBound _ hContains.2

/-- Rewriting only the `given` field of selected loans (without
    changing the loan-id key set) keeps the bound clause. Used by
    `stepSymExpandMutBorrow`. The hypothesis says the rewrite
    function preserves the contains-relation. -/
theorem preserve_loans_givenReplace {st : SymState}
    (hInv : HwmInvariant st)
    (newLoans : Std.HashMap Nat LoanInfo)
    (hContains : ∀ b, newLoans.contains b = st.loans.contains b) :
    HwmInvariant { st with loans := newLoans } := by
  refine ⟨?_, ?_⟩
  · intro b hb; rw [hContains] at hb; exact hInv.loanBound b hb
  · intro a ha; exact hInv.absBound a ha

end HwmInvariant

/-! ## `LoanHwmInvariant` — per-mutator preservation

Loan-half analogues of the `HwmInvariant.preserve_*` family. Each
of the nine mutators the replayer's `stepEvent` uses to touch
`st.loans` or `st.loanIdHwm` has a one-line preservation proof.
The `loopInvRegisterLoan` per-entry helper (the `.loopInv` event's
body) is the ninth.

Splitting the loan half out from the bundled `HwmInvariant`
buys us preservation of the loan clause across the four "shape-
leaking" events (`join` / `endBorrow` / `endAbs` /
`symExpandMutBorrow`) without consulting `eventRespectsHwm` — the
replayer mutators those events compose with do not introduce loan
ids ≥ `loanIdHwm`, but they may rearrange `absRegistry` in ways
the `HwmInvariant.absBound` clause is sensitive to.
-/

namespace LoanHwmInvariant

theorem preserve_setLocal {st : SymState} (hInv : LoanHwmInvariant st)
    (l : Nat) (v : Val) :
    LoanHwmInvariant (st.setLocal l v) :=
  ⟨fun b hb => hInv.loanBound b hb⟩

theorem preserve_env_replace {st : SymState} (hInv : LoanHwmInvariant st)
    (newEnv : Std.HashMap Nat Val) :
    LoanHwmInvariant { st with env := newEnv } :=
  ⟨fun b hb => hInv.loanBound b hb⟩

theorem preserve_addLoan {st : SymState} (hInv : LoanHwmInvariant st)
    (b : Nat) (inner : Val) (kind : LoanKind) :
    LoanHwmInvariant (st.addLoan b inner kind) := by
  refine ⟨?_⟩
  intro b' hContains
  simp only [SymState.addLoan, Std.HashMap.contains_insert,
    Bool.or_eq_true, beq_iff_eq] at hContains
  rcases hContains with heq | hold
  · subst heq
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
  · exact Nat.lt_of_lt_of_le (hInv.loanBound _ hold) (Nat.le_max_left _ _)

theorem preserve_addAbsShape {st : SymState} (hInv : LoanHwmInvariant st)
    (shape : AbsShape) :
    LoanHwmInvariant (st.addAbsShape shape) :=
  ⟨fun b hb => hInv.loanBound b hb⟩

theorem preserve_takeLoan {st : SymState} (hInv : LoanHwmInvariant st)
    {b : Nat} {li : LoanInfo} {st' : SymState}
    (hTake : st.takeLoan b = some (li, st')) :
    LoanHwmInvariant st' := by
  unfold SymState.takeLoan at hTake
  split at hTake
  · cases hTake
  · simp only [Option.some.injEq, Prod.mk.injEq] at hTake
    obtain ⟨_, hs⟩ := hTake
    subst hs
    refine ⟨?_⟩
    intro b' hContains
    simp only [Std.HashMap.contains_erase, Bool.and_eq_true,
      Bool.not_eq_true'] at hContains
    exact hInv.loanBound _ hContains.2

theorem preserve_loans_erase {st : SymState} (hInv : LoanHwmInvariant st)
    (b : Nat) :
    LoanHwmInvariant { st with loans := st.loans.erase b } := by
  refine ⟨?_⟩
  intro b' hContains
  simp only [Std.HashMap.contains_erase, Bool.and_eq_true,
    Bool.not_eq_true'] at hContains
  exact hInv.loanBound _ hContains.2

theorem preserve_removeAbsShape {st : SymState} (hInv : LoanHwmInvariant st)
    (absId : Nat) :
    LoanHwmInvariant (st.removeAbsShape absId) :=
  ⟨fun b hb => hInv.loanBound b hb⟩

/-- Rewriting only the `given` field of selected loans (or otherwise
    rewriting `st.loans` to a map whose key set is a sub-relation of
    the old key set) keeps the bound clause. The hypothesis says
    every key in the new loans map is in the old. Used by the
    `substLoansOne` fold (`symExpandMutBorrow`). -/
theorem preserve_loans_subKey {st : SymState}
    (hInv : LoanHwmInvariant st)
    (newLoans : Std.HashMap Nat LoanInfo)
    (hSub : ∀ b, newLoans.contains b = true → st.loans.contains b = true) :
    LoanHwmInvariant { st with loans := newLoans } := by
  refine ⟨?_⟩
  intro b hb
  exact hInv.loanBound _ (hSub _ hb)

end LoanHwmInvariant

/-! ## Loan-only fold helpers

Per-event mutator-chain helpers, mirroring the existing
`absSigFold_preserves` / `stepLoopInv_fold_preserves` /
`stepJoin_absInstall_preserves` family but tracking only the loan
clause. The four new helpers cover the four events that contain a
loans-bearing fold:

* `call` — `absSig.foldl SymState.addAbsShape` (vacuous on loans).
* `endAbs` — `released.foldl loansEraseIfPresent` (erase only).
* `symExpandMutBorrow` — `substLoans.foldl substLoansOne`
  (sub-key rewrite).
* `join` — `witnesses.foldlM joinChainFoldStep` (chain fold; per
  M10.x.10b stepJoinBody body, the loans map is invariant across
  the fold; only env / absRegistry are touched).

`loopInv` reuses the existing `stepLoopInv_fold_preserves` shape;
we add a `LoanHwm` analogue. -/

/-- `absSig.foldl SymState.addAbsShape` preserves the loan clause
    (vacuously: `addAbsShape` only mutates `absRegistry` / `absIdHwm`). -/
theorem absSigFold_preserves_LoanHwm
    (shapes : List AbsShape) (st : SymState) (hInv : LoanHwmInvariant st) :
    LoanHwmInvariant (shapes.foldl SymState.addAbsShape st) := by
  induction shapes generalizing st with
  | nil => simpa using hInv
  | cons s rest ih =>
    simp only [List.foldl_cons]
    exact ih _ (LoanHwmInvariant.preserve_addAbsShape hInv _)

/-- `released.foldl loansEraseIfPresent` preserves the loan clause:
    each step either erases one entry (sub-key) or no-ops. -/
theorem loansEraseIfPresentFold_preserves_LoanHwm
    (xs : List Nat) (st : SymState) (hInv : LoanHwmInvariant st) :
    LoanHwmInvariant (xs.foldl AeneasCheck.LLBCSharp.loansEraseIfPresent st) := by
  induction xs generalizing st with
  | nil => simpa using hInv
  | cons b rest ih =>
    simp only [List.foldl_cons]
    have hStep : LoanHwmInvariant
        (AeneasCheck.LLBCSharp.loansEraseIfPresent st b) := by
      unfold AeneasCheck.LLBCSharp.loansEraseIfPresent
      split
      · exact LoanHwmInvariant.preserve_loans_erase hInv b
      · exact hInv
    exact ih _ hStep

/-- Per-step substLoans helper: rewriting one loan's `given` field is
    a sub-key map operation. -/
theorem substLoansOne_subKey (svId bid : Nat)
    (loans : Std.HashMap Nat LoanInfo) (b : Nat) :
    ∀ b', (AeneasCheck.LLBCSharp.substLoansOne svId bid loans b).contains b'
            = true → loans.contains b' = true := by
  intro b' hb
  unfold AeneasCheck.LLBCSharp.substLoansOne at hb
  -- Pattern matches on loans[b]? then on .given then on if-cond.
  split at hb
  case h_2 => exact hb  -- loans[b]? = none → hb : loans.contains b' = true
  rename_i li hLook
  split at hb
  case h_2 => exact hb  -- li.given ≠ .sym _ → no rewrite
  rename_i k hGiven
  split at hb
  case isFalse => exact hb  -- k ≠ svId → no rewrite
  -- isTrue branch: loans.insert b _.
  simp only [Std.HashMap.contains_insert, Bool.or_eq_true,
    beq_iff_eq] at hb
  rcases hb with heq | hold
  · subst heq
    -- b is a key of `loans` because `loans[b]? = some li`.
    rw [Std.HashMap.contains_eq_isSome_getElem?, hLook]
    rfl
  · exact hold

/-- Auxiliary fold-style sub-key promotion for substLoansOne. -/
private theorem substLoansOneFold_subKey_aux (svId bid : Nat) :
    ∀ (xs : List Nat) (loans₀ : Std.HashMap Nat LoanInfo) (b : Nat),
      (xs.foldl (AeneasCheck.LLBCSharp.substLoansOne svId bid) loans₀).contains b
        = true → loans₀.contains b = true
  | [], _, _ => fun h => h
  | x :: rest, loans₀, b => by
      intro hb
      simp only [List.foldl_cons] at hb
      have hRest := substLoansOneFold_subKey_aux svId bid rest
        (AeneasCheck.LLBCSharp.substLoansOne svId bid loans₀ x) b hb
      exact substLoansOne_subKey svId bid loans₀ x b hRest

/-- `{ st with loans := substLoans.foldl substLoansOne st.loans }`
    preserves the loan clause: the fold only rewrites in-place loan
    entries (no new keys), so `contains` shrinks (or stays put). -/
theorem substLoansOneFold_preserves_LoanHwm
    (svId bid : Nat) (substLoans : List Nat) (st : SymState)
    (hInv : LoanHwmInvariant st) :
    LoanHwmInvariant { st with
      loans := substLoans.foldl
        (AeneasCheck.LLBCSharp.substLoansOne svId bid) st.loans } := by
  apply LoanHwmInvariant.preserve_loans_subKey hInv
  intro b hb
  exact substLoansOneFold_subKey_aux svId bid substLoans st.loans b hb

/-- `joinMutBorrowsStep` preserves the loan clause: it only mutates
    `absRegistry` (insert) and `env` (setLocal). -/
theorem joinMutBorrowsStep_preserves_LoanHwm {st : SymState}
    (hInv : LoanHwmInvariant st) (localId l_fresh : Nat) (absShape : AbsShape) :
    LoanHwmInvariant
      (AeneasCheck.LLBCSharp.joinMutBorrowsStep st localId l_fresh absShape) := by
  unfold AeneasCheck.LLBCSharp.joinMutBorrowsStep
  -- absRegistry-insert leaves loans / loanIdHwm unchanged; setLocal too.
  apply LoanHwmInvariant.preserve_setLocal
  -- The intermediate state's loans / loanIdHwm are syntactically
  -- `st.loans` / `st.loanIdHwm`.
  exact ⟨hInv.loanBound⟩

/-- Per-step `joinChainFoldStep` preserves the loan clause on `.ok`
    output. Case analysis on the rule:

      * `.joinSame` / `.joinVar` → return st (no change)
      * `.joinSymbolic _` → setLocal (no loans change)
      * `.joinMutBorrows _ _ _ _` → on the success branch, runs
        `joinMutBorrowsStep` (preserves)
      * `.joinBottomOther _` / `.joinOtherBottom _` → return st on
        success (no change)

    The fail branches are dispatched by the `.ok` hypothesis. -/
theorem joinChainFoldStep_preserves_LoanHwm {st st' : SymState}
    (hInv : LoanHwmInvariant st) (entry : JoinEntry)
    (hStep : AeneasCheck.LLBCSharp.joinChainFoldStep st entry = .ok st') :
    LoanHwmInvariant st' := by
  unfold AeneasCheck.LLBCSharp.joinChainFoldStep at hStep
  cases hRule : entry.rule with
  | joinSame =>
    rw [hRule] at hStep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    exact hInv
  | joinVar =>
    rw [hRule] at hStep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    exact hInv
  | joinSymbolic freshSv =>
    rw [hRule] at hStep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    exact LoanHwmInvariant.preserve_setLocal hInv _ _
  | joinMutBorrows _ _ l_fresh absShape =>
    rw [hRule] at hStep
    simp only [bind, Except.bind] at hStep
    by_cases hL : l_fresh < st.loanIdHwm
    · rw [if_pos hL] at hStep; cases hStep
    · rw [if_neg hL] at hStep
      by_cases hA : absShape.absId < st.absIdHwm
      · rw [if_pos hA] at hStep; cases hStep
      · rw [if_neg hA] at hStep
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
        subst hStep
        exact joinMutBorrowsStep_preserves_LoanHwm hInv _ _ _
  | joinBottomOther absId =>
    rw [hRule] at hStep
    by_cases hA : st.absRegistry.contains absId = true
    · simp only [hA, Bool.not_true, Bool.false_eq_true, if_false,
        Pure.pure, Except.pure, Except.ok.injEq] at hStep
      subst hStep
      exact hInv
    · simp only [Bool.not_eq_true] at hA
      simp only [hA, Bool.not_false, if_true] at hStep
      cases hStep
  | joinOtherBottom absId =>
    rw [hRule] at hStep
    by_cases hA : st.absRegistry.contains absId = true
    · simp only [hA, Bool.not_true, Bool.false_eq_true, if_false,
        Pure.pure, Except.pure, Except.ok.injEq] at hStep
      subst hStep
      exact hInv
    · simp only [Bool.not_eq_true] at hA
      simp only [hA, Bool.not_false, if_true] at hStep
      cases hStep

/-- Fold-version of `joinChainFoldStep_preserves_LoanHwm` over
    a `List JoinEntry`. -/
theorem joinChainFoldStepFold_preserves_LoanHwm :
    ∀ (xs : List JoinEntry) {st st' : SymState},
      LoanHwmInvariant st →
        xs.foldlM AeneasCheck.LLBCSharp.joinChainFoldStep st = .ok st' →
        LoanHwmInvariant st'
  | [], st, st', hInv, hFold => by
      simp only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] at hFold
      subst hFold
      exact hInv
  | x :: rest, st, st', hInv, hFold => by
      simp only [List.foldlM_cons, bind, Except.bind] at hFold
      cases hHead : AeneasCheck.LLBCSharp.joinChainFoldStep st x with
      | error _ => rw [hHead] at hFold; cases hFold
      | ok sMid =>
        rw [hHead] at hFold
        simp only at hFold
        have hMid := joinChainFoldStep_preserves_LoanHwm hInv x hHead
        exact joinChainFoldStepFold_preserves_LoanHwm rest hMid hFold

/-- The `stepLoopInv` body fold preserves the loan clause: each step
    either calls `addLoan` (preserving) or skips (preserving). Loan-
    only mirror of `stepLoopInv_fold_preserves`. -/
theorem stepLoopInv_fold_preserves_LoanHwm
    (xs : List (Nat × Nat)) (st : SymState) (hInv : LoanHwmInvariant st) :
    LoanHwmInvariant
      (xs.foldl AeneasCheck.LLBCSharp.loopInvRegisterLoan st) := by
  induction xs generalizing st with
  | nil => simpa using hInv
  | cons p rest ih =>
    simp only [List.foldl_cons]
    unfold AeneasCheck.LLBCSharp.loopInvRegisterLoan
    obtain ⟨b, _⟩ := p
    by_cases hC : st.loans.contains b = true
    · simp only [hC, if_true]
      exact ih _ hInv
    · simp only [hC, if_false]
      exact ih _ (LoanHwmInvariant.preserve_addLoan hInv b .bottom .reborrow)

/-- Per-entry `loopInvRegisterLoan` preserves the loan clause. Used
    directly by `Concretise/Lemmas.lean`'s `_foldl_aux` step. -/
theorem loopInvRegisterLoan_preserves_LoanHwm {st : SymState}
    (hInv : LoanHwmInvariant st) (entry : Nat × Nat) :
    LoanHwmInvariant (AeneasCheck.LLBCSharp.loopInvRegisterLoan st entry) := by
  unfold AeneasCheck.LLBCSharp.loopInvRegisterLoan
  obtain ⟨b, _⟩ := entry
  by_cases hC : st.loans.contains b = true
  · simp only [hC, if_true]; exact hInv
  · simp only [hC, if_false]
    exact LoanHwmInvariant.preserve_addLoan hInv b .bottom .reborrow

/-! ## Main per-event loan preservation theorem (`loanHwm_preserved_stepEvent`)

Unconditional 17-arm case-split: every event preserves the loan
clause. No `eventRespectsHwm` premise needed — the four shape-
leaking events (`join` / `endBorrow` / `endAbs` /
`symExpandMutBorrow`) all factor through mutators whose loan-
clause preservation has a structural proof above (and crucially,
the M10.x.10b checker simplification removed the live-loans
rebuild that previously broke loan-clause preservation in the
`.join` arm).

The corollary `loanHwm_preserved_stepEvent_mono` adds the
`loanIdHwm` monotonicity clause for downstream Phase E
trace-induction. -/

/-- Per-event preservation of `LoanHwmInvariant`. No `hShape`
    precondition. -/
theorem loanHwm_preserved_stepEvent
    {st st' : SymState} {e : Event} {strictJoin : Bool}
    (hInv : LoanHwmInvariant st)
    (hStep : stepEvent st e strictJoin = .ok st') :
    LoanHwmInvariant st' := by
  unfold stepEvent at hStep
  cases e with
  | mutBorrow loan place symval kindHint =>
    simp only [stepMutBorrow] at hStep
    by_cases hC : st.loans.contains loan = true
    · rw [if_pos hC] at hStep; cases hStep
    · rw [if_neg hC] at hStep
      by_cases hHwm : st.loanIdHwm > loan
      · rw [if_pos hHwm] at hStep; cases hStep
      · rw [if_neg hHwm] at hStep
        by_cases hB : placeRootLocal place ≥ st.numLocals
        · rw [if_pos hB] at hStep; cases hStep
        · rw [if_neg hB] at hStep
          cases kindHint with
          | direct =>
            simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
            subst hStep
            exact LoanHwmInvariant.preserve_addLoan
                    (LoanHwmInvariant.preserve_setLocal hInv _ _) _ _ _
          | inAbsReborrow _ =>
            simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
            subst hStep
            exact LoanHwmInvariant.preserve_addLoan hInv _ _ _
          | loopOwned _ =>
            simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
            subst hStep
            exact LoanHwmInvariant.preserve_addLoan
                    (LoanHwmInvariant.preserve_setLocal hInv _ _) _ _ _
  | sharedBorrow loan _sbId place _symval =>
    simp only [stepSharedBorrow] at hStep
    by_cases hC : st.loans.contains loan = true
    · rw [if_pos hC] at hStep; cases hStep
    · rw [if_neg hC] at hStep
      by_cases hHwm : st.loanIdHwm > loan
      · rw [if_pos hHwm] at hStep; cases hStep
      · rw [if_neg hHwm] at hStep
        by_cases hProj : place.projection.size ≠ 0
        · rw [if_pos hProj] at hStep; cases hStep
        · rw [if_neg hProj] at hStep
          by_cases hB : placeRootLocal place ≥ st.numLocals
          · rw [if_pos hB] at hStep; cases hStep
          · rw [if_neg hB] at hStep
            simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
            subst hStep
            exact LoanHwmInvariant.preserve_addLoan hInv _ _ _
  | assign dst rhs =>
    simp only [stepAssign, bind, Except.bind] at hStep
    cases hEval : evalSymExpr st rhs with
    | error _ => rw [hEval] at hStep; cases hStep
    | ok v =>
      rw [hEval] at hStep
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
      subst hStep
      exact LoanHwmInvariant.preserve_setLocal hInv _ _
  | move src dst =>
    simp only [stepMove] at hStep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    exact LoanHwmInvariant.preserve_setLocal
            (LoanHwmInvariant.preserve_setLocal hInv _ _) _ _
  | copy src dst =>
    simp only [stepCopy] at hStep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    exact LoanHwmInvariant.preserve_setLocal hInv _ _
  | endBorrow loan restore =>
    -- `stepEndBorrow` either fails or routes through `takeLoan` then
    -- only mutates env (or returns the post-takeLoan state). The loan
    -- clause survives because `takeLoan` erases (sub-key) and the env
    -- mutations don't touch `loans` / `loanIdHwm`.
    simp only [stepEndBorrow] at hStep
    cases hTake : st.takeLoan loan with
    | none => rw [hTake] at hStep; cases hStep
    | some pair =>
      obtain ⟨li, stTake⟩ := pair
      rw [hTake] at hStep
      simp only [bind, Except.bind] at hStep
      have hInvTake : LoanHwmInvariant stTake :=
        LoanHwmInvariant.preserve_takeLoan hInv hTake
      cases hEval : evalSymExpr stTake restore.givenBack with
      | error _ => rw [hEval] at hStep; cases hStep
      | ok v =>
        rw [hEval] at hStep
        simp only at hStep
        cases hKind : li.kind with
        | direct =>
          rw [hKind] at hStep
          simp only at hStep
          cases hHo : restore.holderLocal.orElse (fun () => findHolder stTake loan) with
          | none => rw [hHo] at hStep; simp only at hStep; cases hStep
          | some x =>
            rw [hHo] at hStep
            simp only at hStep
            cases hLk : stTake.env[x]? with
            | none =>
              rw [hLk] at hStep; simp only at hStep; cases hStep
            | some val =>
              rw [hLk] at hStep
              cases val with
              | bottom => simp only at hStep; cases hStep
              | sym _ => simp only at hStep; cases hStep
              | lit _ => simp only at hStep; cases hStep
              | mutBorrow _ _ => simp only at hStep; cases hStep
              | mutLoan b =>
                simp only at hStep
                by_cases hb : b = loan
                · simp only [hb, if_true, Pure.pure, Except.pure,
                    Except.ok.injEq] at hStep
                  subst hStep
                  exact LoanHwmInvariant.preserve_setLocal hInvTake _ _
                · simp only [hb, if_false] at hStep; cases hStep
        | lazyExpand =>
          rw [hKind] at hStep
          simp only at hStep
          -- Several branches lead to `.ok st`; aggregate.
          have leakOK : ∀ st_out : SymState, st_out = stTake →
              LoanHwmInvariant st_out := by
            intro _ hEq; rw [hEq]; exact hInvTake
          cases hHo : restore.holderLocal.orElse (fun () => findHolder stTake loan) with
          | none =>
            rw [hHo] at hStep
            simp only [show (LoanKind.lazyExpand == LoanKind.lazyExpand) = true from rfl,
              if_true, Pure.pure, Except.pure, Except.ok.injEq] at hStep
            exact leakOK st' hStep.symm
          | some x =>
            rw [hHo] at hStep
            simp only at hStep
            cases hLk : stTake.env[x]? with
            | none =>
              rw [hLk] at hStep
              simp only [show (LoanKind.lazyExpand == LoanKind.lazyExpand) = true from rfl,
                if_true, Pure.pure, Except.pure, Except.ok.injEq] at hStep
              exact leakOK st' hStep.symm
            | some val =>
              rw [hLk] at hStep
              cases val with
              | bottom =>
                simp only [show (LoanKind.lazyExpand == LoanKind.lazyExpand) = true from rfl,
                  if_true, Pure.pure, Except.pure, Except.ok.injEq] at hStep
                exact leakOK st' hStep.symm
              | sym _ =>
                simp only [show (LoanKind.lazyExpand == LoanKind.lazyExpand) = true from rfl,
                  if_true, Pure.pure, Except.pure, Except.ok.injEq] at hStep
                exact leakOK st' hStep.symm
              | lit _ =>
                simp only [show (LoanKind.lazyExpand == LoanKind.lazyExpand) = true from rfl,
                  if_true, Pure.pure, Except.pure, Except.ok.injEq] at hStep
                exact leakOK st' hStep.symm
              | mutBorrow _ _ =>
                simp only [show (LoanKind.lazyExpand == LoanKind.lazyExpand) = true from rfl,
                  if_true, Pure.pure, Except.pure, Except.ok.injEq] at hStep
                exact leakOK st' hStep.symm
              | mutLoan b =>
                simp only at hStep
                by_cases hb : b = loan
                · simp only [hb, if_true, Pure.pure, Except.pure,
                    Except.ok.injEq] at hStep
                  subst hStep
                  exact LoanHwmInvariant.preserve_setLocal hInvTake _ _
                · simp only [hb, if_false,
                    show (LoanKind.lazyExpand == LoanKind.lazyExpand) = true from rfl,
                    if_true, Pure.pure, Except.pure, Except.ok.injEq] at hStep
                  exact leakOK st' hStep.symm
        | reborrow =>
          rw [hKind] at hStep
          simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
          subst hStep
          exact hInvTake
        | shared =>
          rw [hKind] at hStep
          simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
          subst hStep
          exact hInvTake
  | assert cond expected =>
    simp only [bind, Except.bind] at hStep
    cases hA : stepAssert st cond expected with
    | error _ => rw [hA] at hStep; cases hStep
    | ok _ =>
      rw [hA] at hStep
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
      subst hStep
      exact hInv
  | panic =>
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    exact hInv
  | retn =>
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    exact hInv
  | binop op lhs rhs dst =>
    simp only [stepBinop, bind, Except.bind] at hStep
    cases hL : evalSymExpr st lhs with
    | error _ => rw [hL] at hStep; cases hStep
    | ok _ =>
      rw [hL] at hStep
      simp only at hStep
      cases hR : evalSymExpr st rhs with
      | error _ => rw [hR] at hStep; cases hStep
      | ok _ =>
        rw [hR] at hStep
        simp only at hStep
        by_cases hB : placeRootLocal dst ≥ st.numLocals
        · rw [if_pos hB] at hStep; cases hStep
        · rw [if_neg hB] at hStep
          simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
          subst hStep
          exact LoanHwmInvariant.preserve_setLocal hInv _ _
  | reborrow child parent place parentLive parentAbs =>
    simp only [stepReborrow] at hStep
    by_cases hC : st.loans.contains child = true
    · rw [if_pos hC] at hStep; cases hStep
    · rw [if_neg hC] at hStep
      by_cases hHwm : st.loanIdHwm > child
      · rw [if_pos hHwm] at hStep; cases hStep
      · rw [if_neg hHwm] at hStep
        by_cases hB : placeRootLocal place ≥ st.numLocals
        · rw [if_pos hB] at hStep; cases hStep
        · rw [if_neg hB] at hStep
          simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
          subst hStep
          by_cases hP : st.loans.contains parent = true
          · rw [if_pos hP]
            exact LoanHwmInvariant.preserve_addLoan hInv _ _ _
          · rw [if_neg hP]
            exact LoanHwmInvariant.preserve_addLoan
                    (LoanHwmInvariant.preserve_addLoan hInv _ _ _) _ _ _
  | call _fn _callId _fnName _args dst _regionAbs absSig =>
    simp only [stepCall] at hStep
    by_cases hB : placeRootLocal dst ≥ st.numLocals
    · rw [if_pos hB] at hStep; cases hStep
    · rw [if_neg hB] at hStep
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
      subst hStep
      have hListEq : absSig.foldl SymState.addAbsShape st =
                     absSig.toList.foldl SymState.addAbsShape st := by
        simp [Array.foldl_toList]
      have hFoldInv : LoanHwmInvariant (absSig.foldl SymState.addAbsShape st) := by
        rw [hListEq]; exact absSigFold_preserves_LoanHwm _ _ hInv
      exact LoanHwmInvariant.preserve_setLocal hFoldInv _ _
  | endAbs absId _finalValues releasedLoans tokenClearLocals =>
    -- Three-phase body: `loansEraseIfPresent` fold + `tokenClearOne`
    -- env fold + `removeAbsShape`. The `tokenClearOne` env fold
    -- mutates only `env`; the loan clause survives unconditionally.
    simp only [stepEndAbs, bind, Except.bind] at hStep
    cases hV : stepEndAbsValidate st absId releasedLoans with
    | error _ => rw [hV] at hStep; cases hStep
    | ok _ =>
      rw [hV] at hStep
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
      subst hStep
      -- Now `st' = stepEndAbsBody st absId releasedLoans tokenClearLocals`.
      unfold stepEndAbsBody
      -- Step 1: `released.foldl loansEraseIfPresent st` preserves.
      have hListEq : releasedLoans.foldl (init := st)
            AeneasCheck.LLBCSharp.loansEraseIfPresent =
          releasedLoans.toList.foldl
            AeneasCheck.LLBCSharp.loansEraseIfPresent st := by
        simp [Array.foldl_toList]
      have hStep1 : LoanHwmInvariant
          (releasedLoans.foldl (init := st)
            AeneasCheck.LLBCSharp.loansEraseIfPresent) := by
        rw [hListEq]
        exact loansEraseIfPresentFold_preserves_LoanHwm _ _ hInv
      -- Step 2: env-only fold (tokenClearOne); use preserve_env_replace.
      have hStep2 : LoanHwmInvariant
          ({ (releasedLoans.foldl (init := st)
                AeneasCheck.LLBCSharp.loansEraseIfPresent) with
              env := tokenClearLocals.foldl (init :=
                (releasedLoans.foldl (init := st)
                  AeneasCheck.LLBCSharp.loansEraseIfPresent).env)
                AeneasCheck.LLBCSharp.tokenClearOne } : SymState) :=
        LoanHwmInvariant.preserve_env_replace hStep1 _
      -- Step 3: removeAbsShape preserves.
      exact LoanHwmInvariant.preserve_removeAbsShape hStep2 _
  | proj _ _ _ => cases hStep
  | symExpandMutBorrow svId bid _innerSv _parentAbs substLocals substLoans =>
    -- Body: substLocals env-fold + substLoans loans-fold + addLoan.
    simp only [stepSymExpandMutBorrow] at hStep
    by_cases hC : st.loans.contains bid = true
    · rw [if_pos hC] at hStep; cases hStep
    · rw [if_neg hC] at hStep
      by_cases hHwm : st.loanIdHwm > bid
      · rw [if_pos hHwm] at hStep; cases hStep
      · rw [if_neg hHwm] at hStep
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
        subst hStep
        -- Step 1: env fold (env-only).
        have hEnv := hInv -- before env fold; loans untouched.
        -- Build intermediate states.
        let newEnv := substLocals.foldl (init := st.env)
                        (AeneasCheck.LLBCSharp.substLocalsOne svId bid)
        let newLoans := substLoans.foldl (init := st.loans)
                        (AeneasCheck.LLBCSharp.substLoansOne svId bid)
        -- Show the intermediate state {st with env := newEnv, loans := newLoans}
        -- has LoanHwmInvariant.
        have hLoans : LoanHwmInvariant ({ st with loans := newLoans } : SymState) := by
          have hListEq : substLoans.foldl
              (AeneasCheck.LLBCSharp.substLoansOne svId bid) (init := st.loans) =
            substLoans.toList.foldl
              (AeneasCheck.LLBCSharp.substLoansOne svId bid) st.loans := by
            simp [Array.foldl_toList]
          have hP := substLoansOneFold_preserves_LoanHwm svId bid
                       substLoans.toList st hInv
          rw [show newLoans = substLoans.foldl (init := st.loans)
                (AeneasCheck.LLBCSharp.substLoansOne svId bid) from rfl,
              hListEq]
          exact hP
        have hMid : LoanHwmInvariant
            ({ st with env := newEnv, loans := newLoans } : SymState) := by
          -- env-replacement on the loans-rewritten state.
          exact ⟨hLoans.loanBound⟩
        exact LoanHwmInvariant.preserve_addLoan hMid _ _ _
  | join _left _right _result witnesses =>
    -- `stepJoin` = strict-check + chain-fold. The strict-check has no
    -- state effect; the chain-fold preserves loan clause (per
    -- `joinChainFoldStepFold_preserves_LoanHwm`).
    simp only [stepJoin, bind, Except.bind] at hStep
    cases hCheck : stepJoinStrictCheck _left _right _result witnesses with
    | error _ => rw [hCheck] at hStep; cases hStep
    | ok _ =>
      rw [hCheck] at hStep
      simp only at hStep
      -- hStep: stepJoinBody st _result witnesses = .ok st'.
      unfold stepJoinBody at hStep
      have hList : witnesses.foldlM (init := st)
                    AeneasCheck.LLBCSharp.joinChainFoldStep =
                   witnesses.toList.foldlM
                    AeneasCheck.LLBCSharp.joinChainFoldStep st := by
        simp [Array.foldlM_toList]
      rw [hList] at hStep
      exact joinChainFoldStepFold_preserves_LoanHwm witnesses.toList hInv hStep
  | loopInv _loopId _invariant loanRegistry =>
    -- `stepLoopInv`: body folds `loopInvRegisterLoan` over loanRegistry.
    simp only [stepEvent, Pure.pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    have hListEq : loanRegistry.foldl (init := st)
        AeneasCheck.LLBCSharp.loopInvRegisterLoan =
      loanRegistry.toList.foldl AeneasCheck.LLBCSharp.loopInvRegisterLoan st := by
      simp [Array.foldl_toList]
    rw [hListEq]
    exact stepLoopInv_fold_preserves_LoanHwm _ _ hInv
  | loopEnd _loopId =>
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    exact hInv
  | matchArm _scrutinee _adtId _variantId _variantName =>
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    exact hInv

/-! ## Per-event admissibility for the `.join` case

`stepJoin` (`AeneasCheck.LLBCSharp.Step.lean:506`) inserts each
`b ∈ result.liveLoans` into the post-state's `loans` map *without*
routing the insert through `addLoan`, so a freshly-named loan id
that isn't already in `st.loans` will land in `st'.loans` while
`st'.loanIdHwm = st.loanIdHwm`. The `loanBound` clause can break
in that case. The cert-side promise that closes the gap (M10.x.10):
every loan id in `result.liveLoans` is either already in
`st.loans` (no fresh insert) or strictly below the current HWM
(fresh insert lands inside the existing bound). We express that
promise as a per-event predicate; all 16 other events are
unconditional. -/

/-! ## Loop-helpers for the fold-bearing events

`stepCall` / `stepJoin` / `stepEndAbs` / `stepLoopInv` build the
post-state by folding a list of mutators (or by walking an `Array`
via `Array.foldl`, which we unfold to `List.foldl` before invoking
the helper). Each helper has a one-cons-step structural induction. -/

/-- `absSig.foldl SymState.addAbsShape st` preserves the invariant. -/
theorem absSigFold_preserves
    (shapes : List AbsShape) (st : SymState) (hInv : HwmInvariant st) :
    HwmInvariant (shapes.foldl SymState.addAbsShape st) := by
  induction shapes generalizing st with
  | nil => simpa using hInv
  | cons s rest ih =>
    simp only [List.foldl_cons]
    exact ih _ (HwmInvariant.preserve_addAbsShape hInv _)

/-- Monotonicity for the `addAbsShape` fold: each step bumps
    `absIdHwm` via `max`; `loanIdHwm` is untouched. -/
theorem absSigFold_hwm_mono
    (shapes : List AbsShape) (st : SymState) :
    st.loanIdHwm ≤ (shapes.foldl SymState.addAbsShape st).loanIdHwm ∧
    st.absIdHwm ≤ (shapes.foldl SymState.addAbsShape st).absIdHwm := by
  induction shapes generalizing st with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons s rest ih =>
    simp only [List.foldl_cons]
    have hStep : st.loanIdHwm ≤ (st.addAbsShape s).loanIdHwm ∧
                 st.absIdHwm  ≤ (st.addAbsShape s).absIdHwm := by
      refine ⟨?_, ?_⟩
      · simp [SymState.addAbsShape]
      · simp [SymState.addAbsShape]; exact Nat.le_max_left _ _
    have := ih (st.addAbsShape s)
    exact ⟨Nat.le_trans hStep.1 this.1, Nat.le_trans hStep.2 this.2⟩

/-- The `stepLoopInv` body folds a conditional `addLoan` over the
    `loanRegistry`. Each step either calls `addLoan` (preserving)
    or skips (preserving). -/
theorem stepLoopInv_fold_preserves
    (xs : List (Nat × Nat)) (st : SymState) (hInv : HwmInvariant st) :
    HwmInvariant
      (xs.foldl
        (fun (s : SymState) (p : Nat × Nat) =>
          if ¬ s.loans.contains p.1 = true then
            s.addLoan p.1 .bottom .reborrow
          else s) st) := by
  induction xs generalizing st with
  | nil => simpa using hInv
  | cons p rest ih =>
    simp only [List.foldl_cons]
    by_cases h : ¬ st.loans.contains p.1 = true
    · simp only [h]
      exact ih _ (HwmInvariant.preserve_addLoan hInv _ _ _)
    · simp only [h]
      exact ih _ hInv

/-- Monotonicity for the `stepLoopInv` body fold. -/
theorem stepLoopInv_fold_hwm_mono
    (xs : List (Nat × Nat)) (st : SymState) :
    st.loanIdHwm ≤
      (xs.foldl
        (fun (s : SymState) (p : Nat × Nat) =>
          if ¬ s.loans.contains p.1 = true then
            s.addLoan p.1 .bottom .reborrow
          else s) st).loanIdHwm ∧
    st.absIdHwm ≤
      (xs.foldl
        (fun (s : SymState) (p : Nat × Nat) =>
          if ¬ s.loans.contains p.1 = true then
            s.addLoan p.1 .bottom .reborrow
          else s) st).absIdHwm := by
  induction xs generalizing st with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons p rest ih =>
    simp only [List.foldl_cons]
    by_cases h : ¬ st.loans.contains p.1 = true
    · simp only [h]
      have hStep : st.loanIdHwm ≤ (st.addLoan p.1 .bottom .reborrow).loanIdHwm ∧
                   st.absIdHwm  ≤ (st.addLoan p.1 .bottom .reborrow).absIdHwm := by
        refine ⟨?_, ?_⟩
        · simp [SymState.addLoan]; exact Nat.le_max_left _ _
        · simp [SymState.addLoan]
      have := ih (st.addLoan p.1 .bottom .reborrow)
      exact ⟨Nat.le_trans hStep.1 this.1, Nat.le_trans hStep.2 this.2⟩
    · simp only [h]
      exact ih _

/-- The `stepJoin` abs-install fold: a witness with
    `joinMutBorrows _ _ _ absShape` rule triggers `addAbsShape`;
    every other rule is a no-op. Mono lemma below. -/
theorem stepJoin_absInstall_preserves
    (witnesses : List JoinEntry) (st : SymState) (hInv : HwmInvariant st) :
    HwmInvariant
      (witnesses.foldl
        (fun (s : SymState) (entry : JoinEntry) =>
          match entry.rule with
          | .joinMutBorrows _ _ _ absShape => s.addAbsShape absShape
          | _ => s) st) := by
  induction witnesses generalizing st with
  | nil => simpa using hInv
  | cons w rest ih =>
    simp only [List.foldl_cons]
    cases hw : w.rule with
    | joinMutBorrows _ _ _ absShape =>
      exact ih _ (HwmInvariant.preserve_addAbsShape hInv _)
    | joinSame => exact ih _ hInv
    | joinSymbolic _ => exact ih _ hInv
    | joinVar => exact ih _ hInv
    | joinBottomOther _ => exact ih _ hInv
    | joinOtherBottom _ => exact ih _ hInv

/-- Monotonicity for the `stepJoin` abs-install fold. -/
theorem stepJoin_absInstall_hwm_mono
    (witnesses : List JoinEntry) (st : SymState) :
    st.loanIdHwm ≤
      (witnesses.foldl
        (fun (s : SymState) (entry : JoinEntry) =>
          match entry.rule with
          | .joinMutBorrows _ _ _ absShape => s.addAbsShape absShape
          | _ => s) st).loanIdHwm ∧
    st.absIdHwm ≤
      (witnesses.foldl
        (fun (s : SymState) (entry : JoinEntry) =>
          match entry.rule with
          | .joinMutBorrows _ _ _ absShape => s.addAbsShape absShape
          | _ => s) st).absIdHwm := by
  induction witnesses generalizing st with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons w rest ih =>
    simp only [List.foldl_cons]
    cases hw : w.rule with
    | joinMutBorrows _ _ _ absShape =>
      have hStep : st.loanIdHwm ≤ (st.addAbsShape absShape).loanIdHwm ∧
                   st.absIdHwm  ≤ (st.addAbsShape absShape).absIdHwm := by
        refine ⟨?_, ?_⟩
        · simp [SymState.addAbsShape]
        · simp [SymState.addAbsShape]; exact Nat.le_max_left _ _
      have := ih (st.addAbsShape absShape)
      exact ⟨Nat.le_trans hStep.1 this.1, Nat.le_trans hStep.2 this.2⟩
    | joinSame => exact ih _
    | joinSymbolic _ => exact ih _
    | joinVar => exact ih _
    | joinBottomOther _ => exact ih _
    | joinOtherBottom _ => exact ih _

/-! ## Per-mutator monotonicity (HWMs only grow)

These attest that no mutator ever decreases the HWM. The non-`addLoan`
non-`addAbsShape` mutators leave the HWMs *equal*; the additive
ones bump via `max`. -/

theorem setLocal_loanIdHwm (st : SymState) (l : Nat) (v : Val) :
    (st.setLocal l v).loanIdHwm = st.loanIdHwm := rfl

theorem setLocal_absIdHwm (st : SymState) (l : Nat) (v : Val) :
    (st.setLocal l v).absIdHwm = st.absIdHwm := rfl

theorem addLoan_loanIdHwm_le (st : SymState) (b : Nat) (inner : Val)
    (kind : LoanKind) :
    st.loanIdHwm ≤ (st.addLoan b inner kind).loanIdHwm := by
  simp [SymState.addLoan]; exact Nat.le_max_left _ _

theorem addLoan_absIdHwm (st : SymState) (b : Nat) (inner : Val)
    (kind : LoanKind) :
    (st.addLoan b inner kind).absIdHwm = st.absIdHwm := rfl

theorem addAbsShape_loanIdHwm (st : SymState) (shape : AbsShape) :
    (st.addAbsShape shape).loanIdHwm = st.loanIdHwm := rfl

theorem addAbsShape_absIdHwm_le (st : SymState) (shape : AbsShape) :
    st.absIdHwm ≤ (st.addAbsShape shape).absIdHwm := by
  simp [SymState.addAbsShape]; exact Nat.le_max_left _ _

theorem removeAbsShape_loanIdHwm (st : SymState) (a : Nat) :
    (st.removeAbsShape a).loanIdHwm = st.loanIdHwm := rfl

theorem removeAbsShape_absIdHwm (st : SymState) (a : Nat) :
    (st.removeAbsShape a).absIdHwm = st.absIdHwm := rfl

/-! ## Imperative-body shape preconditions

The replayer's `stepEndBorrow` (env-walk `for` loop with `mut newEnv`)
and `stepEndAbs` (loan-erase + token-clear `for` loops) build their
post-state by mutating `env` and `loans` through imperative
constructs. The full `StepEventSound.lean` consumers
(`stepEndBorrow_direct_sound` at line 557 / `stepEndAbs_sound` at
line 792) already factor the imperative-body inversion behind
"post-state shape" hypotheses (`hShape : stepEvent st _ = .ok
(stTake.setLocal x v)` / `(stPre.removeAbsShape absId)`). We mirror
that pattern: the `hwm_preserved_stepEvent` theorem below takes an
event-level admissibility predicate that, for the two imperative
events, names the intermediate `stTake` / `stPre` state and
provides the post-state shape. Discharging the predicate is
downstream of M10.x.1 (M10.x.6 for `endAbs` via the
`Concretise/Lemmas.lean` preamble-commute refactor; M10.x.9 for
`endBorrow` via the cert v6 `RestoreInfo.holderLocal` field). -/

/-- Per-event admissibility predicate for `hwm_preserved_stepEvent`.

  * `.join`: cert's `result.liveLoans` fit within the current HWM
    (or are already in `st.loans`). Closed in M10.x.10.
  * `.endBorrow`: post-state shape is `{ stTake with env := _ }`
    where `stTake` is `st.takeLoan loan` result, OR the post-state
    is `stTake` itself. Closed in M10.x.9 via `holderLocal`.
  * `.endAbs`: post-state has form `(stPre.removeAbsShape absId)`
    where `stPre`'s `loans` is `st.loans` minus the released set
    and `stPre`'s env is a token-clear rewrite of `st.env`; HWMs
    are `st`'s. Closed in M10.x.6 via the preamble-commute
    refactor.
  * All other 14 events: trivially `True`. -/
def eventRespectsHwm (st st' : SymState) : Event → Prop
  | .endBorrow loan _ =>
      ∃ (li : LoanInfo) (stTake : SymState) (envFinal : Std.HashMap Nat Val),
        st.takeLoan loan = some (li, stTake) ∧
        st' = { stTake with env := envFinal }
  | .endAbs absId _ _ _ =>
      ∃ (stPre : SymState),
        st' = stPre.removeAbsShape absId ∧
        st.loanIdHwm = stPre.loanIdHwm ∧
        st.absIdHwm  = stPre.absIdHwm ∧
        (∀ b, stPre.loans.contains b = true → st.loans.contains b = true) ∧
        (∀ a, stPre.absRegistry.contains a = true → st.absRegistry.contains a = true)
  | .symExpandMutBorrow _ bid _ _ _ _ =>
      ∃ (stPre : SymState) (inner : Val),
        st' = stPre.addLoan bid inner .lazyExpand ∧
        st.loanIdHwm = stPre.loanIdHwm ∧
        st.absIdHwm  = stPre.absIdHwm ∧
        (∀ b, stPre.loans.contains b = true → st.loans.contains b = true) ∧
        (∀ a, stPre.absRegistry.contains a = true → st.absRegistry.contains a = true)
  | .join _ _ _ _ =>
      -- Caller proves HwmInvariant + monotonicity directly. The
      -- M10.x.10 join campaign will replace this with a structural
      -- predicate once `stepJoin` consumes `JoinEntryDelta`.
      HwmInvariant st' ∧ st.loanIdHwm ≤ st'.loanIdHwm ∧ st.absIdHwm ≤ st'.absIdHwm
  | .loopInv _ _ _ =>
      -- Same shape as `.join`: the replayer's body folds a
      -- conditional `addLoan` over `loanRegistry`, which preserves
      -- the invariant by `stepLoopInv_fold_preserves`, but the
      -- `mut`/`for` desugaring makes inline invocation tedious.
      -- Caller discharges directly (or via the
      -- `stepLoopInv_fold_preserves` helper).
      HwmInvariant st' ∧ st.loanIdHwm ≤ st'.loanIdHwm ∧ st.absIdHwm ≤ st'.absIdHwm
  | _ => True

/-! ## Main per-event preservation theorem -/

/-- Per-event preservation of `HwmInvariant` plus monotonicity of
    the two HWM counters. Three of the 17 events (`join`,
    `endBorrow`, `endAbs`) consume the shape information their
    imperative bodies leak; the remaining 14 events impose no
    precondition beyond `hInv`. -/
theorem hwm_preserved_stepEvent
    {st st' : SymState} {e : Event} {strictJoin : Bool}
    (hInv : HwmInvariant st)
    (hShape : eventRespectsHwm st st' e)
    (hStep : stepEvent st e strictJoin = .ok st') :
    HwmInvariant st' ∧ st.loanIdHwm ≤ st'.loanIdHwm ∧ st.absIdHwm ≤ st'.absIdHwm := by
  unfold stepEvent at hStep
  cases e with
  | mutBorrow loan place symval kindHint =>
    simp only [stepMutBorrow] at hStep
    by_cases hC : st.loans.contains loan = true
    · rw [if_pos hC] at hStep; cases hStep
    · rw [if_neg hC] at hStep
      -- M10.x.2: HWM monotone-allocator strengthening; both branches dispatch.
      by_cases hHwm : st.loanIdHwm > loan
      · rw [if_pos hHwm] at hStep; cases hStep
      · rw [if_neg hHwm] at hStep
        by_cases hB : placeRootLocal place ≥ st.numLocals
        · rw [if_pos hB] at hStep; cases hStep
        · rw [if_neg hB] at hStep
          cases kindHint with
          | direct =>
            simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
            subst hStep
            refine ⟨HwmInvariant.preserve_addLoan
                      (HwmInvariant.preserve_setLocal hInv _ _) _ _ _, ?_, ?_⟩
            · exact Nat.le_trans (Nat.le_of_eq (setLocal_loanIdHwm _ _ _).symm)
                      (addLoan_loanIdHwm_le _ _ _ _)
            · simp [addLoan_absIdHwm, setLocal_absIdHwm]
          | inAbsReborrow _ =>
            simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
            subst hStep
            refine ⟨HwmInvariant.preserve_addLoan hInv _ _ _, ?_, ?_⟩
            · exact addLoan_loanIdHwm_le _ _ _ _
            · simp [addLoan_absIdHwm]
          | loopOwned _ =>
            simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
            subst hStep
            refine ⟨HwmInvariant.preserve_addLoan
                      (HwmInvariant.preserve_setLocal hInv _ _) _ _ _, ?_, ?_⟩
            · exact Nat.le_trans (Nat.le_of_eq (setLocal_loanIdHwm _ _ _).symm)
                      (addLoan_loanIdHwm_le _ _ _ _)
            · simp [addLoan_absIdHwm, setLocal_absIdHwm]
  | sharedBorrow loan _sbId place _symval =>
    simp only [stepSharedBorrow] at hStep
    by_cases hC : st.loans.contains loan = true
    · rw [if_pos hC] at hStep; cases hStep
    · rw [if_neg hC] at hStep
      -- M10.x.2: HWM monotone-allocator strengthening.
      by_cases hHwm : st.loanIdHwm > loan
      · rw [if_pos hHwm] at hStep; cases hStep
      · rw [if_neg hHwm] at hStep
        -- M10.x.2: projection-empty strengthening.
        by_cases hProj : place.projection.size ≠ 0
        · rw [if_pos hProj] at hStep; cases hStep
        · rw [if_neg hProj] at hStep
          by_cases hB : placeRootLocal place ≥ st.numLocals
          · rw [if_pos hB] at hStep; cases hStep
          · rw [if_neg hB] at hStep
            simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
            subst hStep
            refine ⟨HwmInvariant.preserve_addLoan hInv _ _ _, ?_, ?_⟩
            · exact addLoan_loanIdHwm_le _ _ _ _
            · simp [addLoan_absIdHwm]
  | assign dst rhs =>
    simp only [stepAssign, bind, Except.bind] at hStep
    cases hEval : evalSymExpr st rhs with
    | error _ => rw [hEval] at hStep; cases hStep
    | ok v =>
      rw [hEval] at hStep
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
      subst hStep
      refine ⟨HwmInvariant.preserve_setLocal hInv _ _, ?_, ?_⟩
      · simp [setLocal_loanIdHwm]
      · simp [setLocal_absIdHwm]
  | move src dst =>
    simp only [stepMove] at hStep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    refine ⟨HwmInvariant.preserve_setLocal
              (HwmInvariant.preserve_setLocal hInv _ _) _ _, ?_, ?_⟩
    · simp [setLocal_loanIdHwm]
    · simp [setLocal_absIdHwm]
  | copy src dst =>
    simp only [stepCopy] at hStep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    refine ⟨HwmInvariant.preserve_setLocal hInv _ _, ?_, ?_⟩
    · simp [setLocal_loanIdHwm]
    · simp [setLocal_absIdHwm]
  | endBorrow loan restore =>
    -- Imperative body; consume `hShape`.
    simp only [eventRespectsHwm] at hShape
    obtain ⟨li, stTake, envFinal, hTake, hSt'⟩ := hShape
    subst hSt'
    have hInvTake : HwmInvariant stTake :=
      HwmInvariant.preserve_takeLoan hInv hTake
    have hStTakeHwm : st.loanIdHwm = stTake.loanIdHwm ∧
                      st.absIdHwm  = stTake.absIdHwm := by
      unfold SymState.takeLoan at hTake
      split at hTake
      · cases hTake
      · simp only [Option.some.injEq, Prod.mk.injEq] at hTake
        obtain ⟨_, hs⟩ := hTake
        subst hs
        exact ⟨rfl, rfl⟩
    refine ⟨HwmInvariant.preserve_env_replace hInvTake _, ?_, ?_⟩
    · exact Nat.le_of_eq hStTakeHwm.1
    · exact Nat.le_of_eq hStTakeHwm.2
  | assert cond expected =>
    -- `stepAssert` returns `.error` or `.ok ()`; outer code returns `st`.
    simp only [bind, Except.bind] at hStep
    cases hA : stepAssert st cond expected with
    | error _ => rw [hA] at hStep; cases hStep
    | ok _ =>
      rw [hA] at hStep
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
      subst hStep
      exact ⟨hInv, Nat.le_refl _, Nat.le_refl _⟩
  | panic =>
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    exact ⟨hInv, Nat.le_refl _, Nat.le_refl _⟩
  | retn =>
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    exact ⟨hInv, Nat.le_refl _, Nat.le_refl _⟩
  | binop op lhs rhs dst =>
    simp only [stepBinop, bind, Except.bind] at hStep
    cases hL : evalSymExpr st lhs with
    | error _ => rw [hL] at hStep; cases hStep
    | ok _ =>
      rw [hL] at hStep
      simp only at hStep
      cases hR : evalSymExpr st rhs with
      | error _ => rw [hR] at hStep; cases hStep
      | ok _ =>
        rw [hR] at hStep
        simp only at hStep
        by_cases hB : placeRootLocal dst ≥ st.numLocals
        · rw [if_pos hB] at hStep; cases hStep
        · rw [if_neg hB] at hStep
          simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
          subst hStep
          refine ⟨HwmInvariant.preserve_setLocal hInv _ _, ?_, ?_⟩
          · simp [setLocal_loanIdHwm]
          · simp [setLocal_absIdHwm]
  | reborrow child parent place parentLive parentAbs =>
    simp only [stepReborrow] at hStep
    by_cases hC : st.loans.contains child = true
    · rw [if_pos hC] at hStep; cases hStep
    · rw [if_neg hC] at hStep
      -- M10.x.2: HWM monotone-allocator strengthening on the child id.
      by_cases hHwm : st.loanIdHwm > child
      · rw [if_pos hHwm] at hStep; cases hStep
      · rw [if_neg hHwm] at hStep
        by_cases hB : placeRootLocal place ≥ st.numLocals
        · rw [if_pos hB] at hStep; cases hStep
        · rw [if_neg hB] at hStep
          simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
          subst hStep
          by_cases hP : st.loans.contains parent = true
          · rw [if_pos hP]
            refine ⟨HwmInvariant.preserve_addLoan hInv _ _ _, ?_, ?_⟩
            · exact addLoan_loanIdHwm_le _ _ _ _
            · simp [addLoan_absIdHwm]
          · rw [if_neg hP]
            have hInv1 := HwmInvariant.preserve_addLoan hInv parent .bottom .reborrow
            refine ⟨HwmInvariant.preserve_addLoan hInv1 _ _ _, ?_, ?_⟩
            · exact Nat.le_trans (addLoan_loanIdHwm_le _ _ _ _)
                      (addLoan_loanIdHwm_le _ _ _ _)
            · simp [addLoan_absIdHwm]
  | call _fn _callId _fnName _args dst _regionAbs absSig =>
    simp only [stepCall] at hStep
    by_cases hB : placeRootLocal dst ≥ st.numLocals
    · rw [if_pos hB] at hStep; cases hStep
    · rw [if_neg hB] at hStep
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
      subst hStep
      have hListEq : absSig.foldl SymState.addAbsShape st =
                     absSig.toList.foldl SymState.addAbsShape st := by
        simp [Array.foldl_toList]
      have hFoldInv : HwmInvariant (absSig.foldl SymState.addAbsShape st) := by
        rw [hListEq]; exact absSigFold_preserves _ _ hInv
      have hFoldMono := absSigFold_hwm_mono absSig.toList st
      rw [← hListEq] at hFoldMono
      refine ⟨HwmInvariant.preserve_setLocal hFoldInv _ _, ?_, ?_⟩
      · rw [setLocal_loanIdHwm]; exact hFoldMono.1
      · rw [setLocal_absIdHwm]; exact hFoldMono.2
  | endAbs absId _finalValues _released _tokenClearLocals =>
    -- Imperative body; consume `hShape`.
    simp only [eventRespectsHwm] at hShape
    obtain ⟨stPre, hSt', hLoanEq, hAbsEq, hLoanSub, hAbsSub⟩ := hShape
    subst hSt'
    -- HwmInvariant on stPre: stPre.loans ⊆ st.loans, so the bound
    -- inherited from hInv; similarly for absRegistry.
    have hInvPre : HwmInvariant stPre := by
      refine ⟨?_, ?_⟩
      · intro b hb
        have := hInv.loanBound _ (hLoanSub _ hb)
        rw [hLoanEq] at this; exact this
      · intro a ha
        have := hInv.absBound _ (hAbsSub _ ha)
        rw [hAbsEq] at this; exact this
    refine ⟨HwmInvariant.preserve_removeAbsShape hInvPre _, ?_, ?_⟩
    · rw [removeAbsShape_loanIdHwm]; exact Nat.le_of_eq hLoanEq
    · rw [removeAbsShape_absIdHwm]; exact Nat.le_of_eq hAbsEq
  | proj _ _ _ => cases hStep
  | symExpandMutBorrow _svId _bid _innerSv _parentAbs _substLocals _substLoans =>
    -- Imperative body (two for-loops over substLocals/substLoans);
    -- consume `hShape`.
    simp only [eventRespectsHwm] at hShape
    obtain ⟨stPre, inner, hSt', hLoanEq, hAbsEq, hLoanSub, hAbsSub⟩ := hShape
    subst hSt'
    have hInvPre : HwmInvariant stPre := by
      refine ⟨?_, ?_⟩
      · intro b hb
        have := hInv.loanBound _ (hLoanSub _ hb)
        rw [hLoanEq] at this; exact this
      · intro a ha
        have := hInv.absBound _ (hAbsSub _ ha)
        rw [hAbsEq] at this; exact this
    refine ⟨HwmInvariant.preserve_addLoan hInvPre _ _ _, ?_, ?_⟩
    · rw [hLoanEq]; exact addLoan_loanIdHwm_le _ _ _ _
    · simp [hAbsEq, addLoan_absIdHwm]
  | join _left _right _result _witnesses =>
    -- Caller fully discharges via `eventRespectsHwm`.
    simp only [eventRespectsHwm] at hShape
    exact hShape
  | loopInv _loopId _invariant _loanRegistry =>
    -- Caller fully discharges via `eventRespectsHwm` (see
    -- `stepLoopInv_fold_preserves` / `stepLoopInv_fold_hwm_mono`
    -- for the toolkit).
    simp only [eventRespectsHwm] at hShape
    exact hShape
  | loopEnd _loopId =>
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    exact ⟨hInv, Nat.le_refl _, Nat.le_refl _⟩
  | matchArm _scrutinee _adtId _variantId _variantName =>
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hStep
    subst hStep
    exact ⟨hInv, Nat.le_refl _, Nat.le_refl _⟩

/-! ## Trace-level corollary

`Replay.replayFun` initialises `SymState.empty numLocals` and
folds `stepEvent` over the cert's event array. Each step preserves
`HwmInvariant` modulo `eventRespectsHwm`; the base case is
`HwmInvariant.empty`. We expose the trace-level invariant as an
inductive `WitnessedChain`: a series of stepEvent successes from
`st₀` to `st_n` whose per-step admissibility witnesses are
embedded. The closing theorem `hwm_replayFun` is then a direct
induction. -/

/-- Inductive chain of stepEvent successes with embedded
    per-step admissibility witnesses. Mirrors `LLBCSharpPaper.JoinChain`
    in structure (nil + cons), but for the replayer-side `SymState`
    rather than the paper-side `LLBCState`. -/
inductive WitnessedChain (strictJoin : Bool) :
    SymState → SymState → Prop
  | nil {st : SymState} : WitnessedChain strictJoin st st
  | cons {st sNext stFin : SymState} {e : Event}
      (hStep : stepEvent st e strictJoin = .ok sNext)
      (hAdm : eventRespectsHwm st sNext e)
      (hRest : WitnessedChain strictJoin sNext stFin) :
      WitnessedChain strictJoin st stFin

/-- Trace-level preservation. Walking a `WitnessedChain` from a
    state with `HwmInvariant` lands in a state still satisfying
    `HwmInvariant` with non-decreasing HWMs. -/
theorem hwm_chain
    {strictJoin : Bool} {st₀ stFin : SymState}
    (hInv : HwmInvariant st₀)
    (hChain : WitnessedChain strictJoin st₀ stFin) :
    HwmInvariant stFin ∧
    st₀.loanIdHwm ≤ stFin.loanIdHwm ∧
    st₀.absIdHwm  ≤ stFin.absIdHwm := by
  induction hChain with
  | nil => exact ⟨hInv, Nat.le_refl _, Nat.le_refl _⟩
  | cons hStep hAdm _ ih =>
    have hPres := hwm_preserved_stepEvent hInv hAdm hStep
    have ihR := ih hPres.1
    refine ⟨ihR.1, Nat.le_trans hPres.2.1 ihR.2.1,
            Nat.le_trans hPres.2.2 ihR.2.2⟩

/-- The headline corollary: any `WitnessedChain` originating from
    `SymState.empty n` (i.e. the replayer's entry state) lands in
    a state satisfying `HwmInvariant`. Specialisation of
    `hwm_chain` against the empty-state base case. -/
theorem hwm_replayFun
    {strictJoin : Bool} (n : Nat) {stFin : SymState}
    (hChain : WitnessedChain strictJoin (SymState.empty n) stFin) :
    HwmInvariant stFin ∧
    (SymState.empty n).loanIdHwm ≤ stFin.loanIdHwm ∧
    (SymState.empty n).absIdHwm  ≤ stFin.absIdHwm :=
  hwm_chain (HwmInvariant.empty n) hChain

end AeneasSoundness.Soundness.Invariants
