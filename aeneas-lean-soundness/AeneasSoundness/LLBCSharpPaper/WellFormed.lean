import AeneasSoundness.LLBCSharpPaper.State
import AeneasSoundness.LLBCSharpPaper.Program

/-!
# LLBC# paper-side well-formedness

Plan §1.1 row 4 / §1.3 commit A5: the structural invariants that
every reachable `Ω#` satisfies, plus a static-program counterpart for
`cc.llbcProgram`.

## What we cover at M10.0e

This is the *baseline* port. We commit to the *shape* of the
invariants and provide:

* Value-level helpers (`Val.directLoans`, `Val.directBorrows`,
  `Val.directLoanIds`, `Val.directBorrowIds`) that walk a single
  `Val` and return the loan / borrow ids directly visible at its
  top level — *not* recursing into nested borrow / aggregate
  payloads. The full nested traversal lands in Phase C alongside
  the lemmas that need it (plan §3.4 calls these out as additions
  to `LoanTokenInvariant`).
* `RegionAbs.WellFormed`: the abs's role multiset is nodup.
* `LLBCState.WellFormed`: a structure with named fields recording
  the shallow invariants we can state without the nested-value
  traversal: freshness monotonicity (every populated abs id and
  every loan id observed in `ctx` is < its `freshness.next*`
  counter), and a placeholder slot for the per-event Phase-C
  strengthenings.
* `LlbcProgram.WellFormed`: typeDecl ids are unique, trait-impls
  reference declared trait-decls, fun-decls' ids are unique.

The slots labelled `-- TODO M10.<Cxx>` are placeholders for the
Phase-C lemmas that strengthen this baseline; per plan §3.4 / §11.2,
the `LoanTokenInvariant` (and its paper-side mirror) accumulate as
specific events need them. Each strengthening adds one field; we
land them one-at-a-time so the Phase-C audit trail is precise.

## Extrinsic, not intrinsic

Per plan §11.1 #4 we commit to the extrinsic form: `WellFormed` is a
`Prop`, separate from `LLBCState`. Theorems that need it carry it as
a hypothesis. This matches the replayer's extrinsic style and keeps
the per-event lemma signatures linear in their premise count.
-/

namespace AeneasSoundness.LLBCSharpPaper

open AeneasCheck.Raw

/-! ## Value-level direct-ids helpers

These look only at the top-level constructor of a `Val`; they do
*not* recurse into `mutBorrow`'s `inner` payload or into the
`adt` / `tuple` / `record` fields. Phase C adds the deep versions
when a lemma needs them (the deep traversal must work around
Val's nested-inductive `Array Val` shape; we defer that recursion
hazard until it's actually load-bearing).
-/

namespace Val

/-- The loan id of `v` if `v` is a `mutLoan` / `sharedLoan` at its
    top level; `none` otherwise. Does *not* recurse. -/
def directLoanId : Val → Option LoanId
  | .mutLoan ℓ    => some ℓ
  | .sharedLoan ℓ => some ℓ
  | _             => none

/-- The borrow's loan id if `v` is a `mutBorrow` / `sharedBorrow` at
    its top level; `none` otherwise. Does *not* recurse into
    `inner`. -/
def directBorrowId : Val → Option LoanId
  | .mutBorrow ℓ _    => some ℓ
  | .sharedBorrow ℓ _ => some ℓ
  | _                 => none

end Val

/-! ## RegionAbs well-formedness -/

namespace RegionAbs

/-- A region abstraction is well-formed when its role multiset has
    no duplicate `(role, loanId)` entries (the paper's `A_in(ρ)` is
    a *set*; multiset is the carrier, nodup is the invariant). -/
def WellFormed (a : RegionAbs) : Prop :=
  a.roles.Nodup

end RegionAbs

/-! ## LLBCState well-formedness -/

namespace LLBCState

/-- Baseline well-formedness over `Ω#`. The fields below are the
    shallow invariants — they don't recurse into nested `Val`
    structure. Phase-C lemmas that need deeper invariants (e.g.
    "each `mutLoan ℓ` token appears exactly once in `ctx ∪ abs`")
    add new fields here as needed, with a Phase-C commit naming
    the strengthening.

    Per plan §11.1 #4 the predicate is extrinsic — `LLBCState`
    itself does not carry a `WellFormed` proof.
-/
structure WellFormed (Ω : LLBCState) : Prop where
  /-- Every populated abs id is below the freshness counter — i.e.
      the freshness counter is a monotone upper bound on issued ids. -/
  abs_below_next : ∀ a, (Ω.abs a).isSome → a < Ω.freshness.nextAbsId
  /-- Every loan id directly observed at a local in `ctx` is below
      the loan-id freshness counter. (Direct-only; the deep version
      that traverses borrow-payload values lands in Phase C as a
      separate field if needed.) -/
  loan_below_next_direct :
    ∀ x v ℓ, Ω.ctx x = some v →
      v.directLoanId = some ℓ ∨ v.directBorrowId = some ℓ →
        ℓ < Ω.freshness.nextLoanId
  /-- Each populated region abstraction is well-formed in isolation
      (no duplicate role entries). -/
  abs_wf : ∀ a r, Ω.abs a = some r → RegionAbs.WellFormed r

/-! ### Smoke / starter lemma

`LLBCState.empty.WellFormed` — the empty state is trivially
well-formed. Used by Phase B's `concretise_wellFormed_smoke`.
-/

theorem empty_WellFormed : WellFormed LLBCState.empty := by
  refine ⟨?_, ?_, ?_⟩
  · intro a h
    simp [LLBCState.empty] at h
  · intro x v ℓ hctx _
    simp [LLBCState.empty] at hctx
  · intro a r h
    simp [LLBCState.empty] at h

end LLBCState

/-! ## LlbcProgram well-formedness

These are the *static* well-formedness conditions on the embedded
`cc.llbcProgram`. They are *not* implied by `replayCrate` succeeding;
the checker's `Typecheck.checkLlbcVsCert` (M9.7h) discharges them at
parse time. Phase F's `typecheck_implies_wellFormedInit` (M10.4a)
threads this hypothesis into the initial-state well-formedness.
-/

/-- A trait-impl `i`'s `traitDeclId` resolves to some declared
    trait-decl in `lp.traitDecls`. -/
def WellFormedProgram.TraitImplRefsResolve (lp : LlbcProgram) : Prop :=
  ∀ i ∈ lp.traitImpls,
    ∃ td ∈ lp.traitDecls, td.id = i.traitDeclId

/-- All `typeDecls` ids are pairwise distinct. -/
def WellFormedProgram.TypeDeclIdsUnique (lp : LlbcProgram) : Prop :=
  ∀ i j, i < lp.typeDecls.size → j < lp.typeDecls.size →
    lp.typeDecls[i]!.id = lp.typeDecls[j]!.id → i = j

/-- All `funDecls` ids are pairwise distinct. -/
def WellFormedProgram.FunDeclIdsUnique (lp : LlbcProgram) : Prop :=
  ∀ i j, i < lp.funDecls.size → j < lp.funDecls.size →
    lp.funDecls[i]!.id = lp.funDecls[j]!.id → i = j

/-- All `traitDecls` ids are pairwise distinct. -/
def WellFormedProgram.TraitDeclIdsUnique (lp : LlbcProgram) : Prop :=
  ∀ i j, i < lp.traitDecls.size → j < lp.traitDecls.size →
    lp.traitDecls[i]!.id = lp.traitDecls[j]!.id → i = j

/-- Static program well-formedness: id-set hygiene + reference
    resolution. The conjunction is structured rather than a single
    big `And` so Phase F can discharge fields one at a time. -/
structure WellFormedProgram (lp : LlbcProgram) : Prop where
  type_ids_unique : WellFormedProgram.TypeDeclIdsUnique lp
  fun_ids_unique : WellFormedProgram.FunDeclIdsUnique lp
  trait_ids_unique : WellFormedProgram.TraitDeclIdsUnique lp
  trait_impl_refs : WellFormedProgram.TraitImplRefsResolve lp

/-- The empty program is well-formed. Used by Phase B's smoke
    lemma when the cert's `cc.llbcProgram` is `LlbcProgram.empty`
    (back-compat slot from cert v2). -/
theorem WellFormedProgram.empty : WellFormedProgram LlbcProgram.empty := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i _ hi _ _
    simp [LlbcProgram.empty] at hi
  · intro i _ hi _ _
    simp [LlbcProgram.empty] at hi
  · intro i _ hi _ _
    simp [LlbcProgram.empty] at hi
  · intro i hi
    simp [LlbcProgram.empty] at hi

end AeneasSoundness.LLBCSharpPaper
