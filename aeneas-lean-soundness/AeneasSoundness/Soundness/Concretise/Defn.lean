import AeneasCheck.LLBCSharp.State
import AeneasCheck.Raw.CertEvent
import AeneasSoundness.LLBCSharpPaper.State
import AeneasSoundness.LLBCSharpPaper.Syntax
import AeneasSoundness.LLBCSharpPaper.WellFormed

/-!
# Concretisation `concretise : SymState → LLBCState`

Plan §2.1 / §1.3 commits B1+B2. Lifts the replayer-side `SymState`
into the paper-side `LLBCState`. The lift is *lossy* — every
replayer abstraction the paper retains gets a faithful image, but
ADT / tuple / record values (which the M9.5d/f/p collapse already
approximates on the replayer side) project to `Val.opaq`.

## Scope (M10.1a + M10.1b)

* `liftVal` — value-grammar lift `LLBCSharp.Val → LLBCSharpPaper.Val`.
* `liftEnv` — env `HashMap` → `LocalId → Option Val#`.
* `liftAbsRoleEntry` / `liftAbsShape` / `liftAbsRegistry` — abs-shape
  lift from `AbsRoleEntry` → `(Role × LoanId)` and the surrounding
  registry into `AbsId → Option RegionAbs`.
* `maxKeyPlusOne` — generic "next-fresh-id" helper over a
  `Std.HashMap Nat _`.
* `concretise` — the full entry point.

## Freshness counters

The paper's `NonceCounters` are monotone upper bounds. The replayer
doesn't track them explicitly; we synthesise:

* `nextLoanId := maxKeyPlusOne st.loans`
* `nextAbsId  := maxKeyPlusOne st.absRegistry`
* `nextSymValId := 0` — the replayer doesn't track sym-value ids;
  the cert provides them and `CertGen_faithful` enforces
  monotonicity. Phase C lemmas that need `Ω.symValIdFresh σ` for
  an event-supplied σ discharge from this axiom rather than from
  the replayer-side state.

## Abs registry — `unknown` placeholder deferred

Plan §2.3 risk #2 anticipates abs ids the cert references before
`EvCall` populates them (`EvMutBorrow … .inAbsReborrow absId` is
the trigger). The plan recommends an `Unknown` placeholder
constructor in `LLBCState.abs`'s codomain. We do *not* introduce
that variant in M10.1b — instead, `liftAbsRegistry` returns `none`
for those abs ids, and Phase C lemmas case on `Ω.abs absId = none`
where needed. If a per-event lemma genuinely cannot dispatch
without an opaque-but-existent abs, we'll add `RegionAbs.unknown`
in a follow-up; the rewrite is local.

## Soundness sanity

`empty_concretise`: `concretise (SymState.empty 0) = LLBCState.empty`.
The smoke lemma M10.1c builds on.
-/

namespace AeneasSoundness.Soundness.Concretise

open AeneasCheck.LLBCSharp
open AeneasCheck.Raw (AbsShape AbsRoleEntry)
open AeneasSoundness.LLBCSharpPaper
  (LLBCState NonceCounters RegionAbs Role LoanId AbsId)

/-! ## Value-grammar lift -/

/-- Lift a replayer `Val` into the paper-side `Val#`. The replayer's
    `Val` is a 5-constructor subset of the paper's 11-constructor
    `Val#`; the lift is a structural recursion that maps each
    constructor to its paper counterpart. -/
def liftVal : AeneasCheck.LLBCSharp.Val → AeneasSoundness.LLBCSharpPaper.Val
  | .sym n        => .sym n
  | .lit l        => .lit l
  | .mutLoan b    => .mutLoan b
  | .mutBorrow b inner => .mutBorrow b (liftVal inner)
  | .bottom       => .bottom

/-! ## Env lift -/

/-- Lift the env `HashMap` into the paper's total `LocalId → Option
    Val#`. Locals not in the map go to `none` (declared but unmapped
    is the same as undeclared at this layer); locals mapped to
    `.bottom` stay `Some bottom`. -/
def liftEnv (env : Std.HashMap Nat AeneasCheck.LLBCSharp.Val) :
    AeneasSoundness.LLBCSharpPaper.LocalId →
      Option AeneasSoundness.LLBCSharpPaper.Val :=
  fun l => (env[l]?).map liftVal

/-! ## Abs lift -/

/-- Lift a single `AbsRoleEntry` into the paper's `(Role × LoanId)`
    pair. Drops the `argIdx` decoration (the paper's `A_in(ρ)` has
    role + loan id only). -/
def liftAbsRoleEntry : AbsRoleEntry → (Role × LoanId)
  | .mutBorrow _ ℓ          => (.mutBorrow, ℓ)
  | .mutLoan ℓ              => (.mutLoan, ℓ)
  | .sharedBorrow _ sbId    => (.sharedBorrow, sbId)

/-- Lift a single `AbsShape` into a paper-side `RegionAbs`. The
    role multiset is built from the shape's `roles` array, dropping
    arg-position info; `parents` carries through unchanged. -/
def liftAbsShape (shape : AbsShape) : RegionAbs :=
  { roles := (shape.roles.toList.map liftAbsRoleEntry : Multiset (Role × LoanId))
    parents := shape.parentAbs }

/-- Lift the abs registry into the paper's `AbsId → Option
    RegionAbs`. Abs ids not in the registry lift to `none` (per
    plan §2.3 risk #2; the `RegionAbs.unknown` placeholder is
    deferred). -/
def liftAbsRegistry (registry : Std.HashMap Nat AbsShape) :
    AbsId → Option RegionAbs :=
  fun a => (registry[a]?).map liftAbsShape

/-! ## Freshness helper -/

/-- `maxKeyPlusOne m` returns the smallest `Nat` strictly greater
    than every key in `m`. Empty maps yield `0`. Used to seed the
    paper's `NonceCounters` from the replayer's HashMap-keyed
    state. -/
def maxKeyPlusOne {α : Type} (m : Std.HashMap Nat α) : Nat :=
  m.fold (fun acc k _ => max acc (k + 1)) 0

/-- `maxKeyPlusOne` on the empty hashmap is `0`. Used by
    `empty_concretise`. -/
@[simp]
theorem maxKeyPlusOne_empty {α : Type} :
    maxKeyPlusOne (∅ : Std.HashMap Nat α) = 0 := by
  rw [maxKeyPlusOne, Std.HashMap.fold_eq_foldl_toList]
  simp

/-! ## Concretise -/

/-- Full concretisation. Lifts:

    * `env` → `ctx` via `liftEnv`.
    * `absRegistry` → `abs` via `liftAbsRegistry`.
    * Freshness counters from `maxKeyPlusOne` over `loans` /
      `absRegistry`; `nextSymValId := 0` (cert-provided ids whose
      monotonicity rides on `CertGen_faithful`).

    `loans` does *not* contribute its own `LLBCState` field — its
    `.direct` entries already live in `ctx` as `mutLoan` tokens
    (via `liftVal`); `.reborrow` / `.lazyExpand` entries are carried
    inside their parent's abs (which is in `absRegistry`). -/
def concretise (st : SymState) : LLBCState :=
  { ctx := liftEnv st.env
    abs := liftAbsRegistry st.absRegistry
    freshness :=
      { nextLoanId   := maxKeyPlusOne st.loans
        nextAbsId    := maxKeyPlusOne st.absRegistry
        nextSymValId := 0 } }

/-! ## Smoke lemma

The empty replayer state lifts to the empty paper state. Used by
M10.1c (`concretise_wellFormed_smoke`) and as a sanity probe that
the structure projections agree.
-/

theorem empty_concretise (n : Nat) :
    concretise (SymState.empty n) = LLBCState.empty := by
  unfold concretise SymState.empty LLBCState.empty
  refine LLBCState.mk.injEq .. |>.mpr ⟨?_, ?_, ?_⟩
  · funext l; unfold liftEnv; simp
  · funext a; unfold liftAbsRegistry; simp
  · simp

/-- Plan §2.2 B3 (M10.1c). The concretisation of the empty
    replayer state is a well-formed LLBC# state. Phase B's
    vertical-slice smoke lemma: it confirms the type contract
    `concretise ; WellFormed` closes for the trivial case. The
    full `concretise_wellFormed` (over arbitrary `SymState`) is
    Phase C territory (one field at a time, in the strengthenings
    each per-event lemma demands). -/
theorem concretise_wellFormed_smoke :
    LLBCState.WellFormed (concretise (SymState.empty 0)) := by
  rw [empty_concretise]
  exact LLBCState.empty_WellFormed

end AeneasSoundness.Soundness.Concretise
