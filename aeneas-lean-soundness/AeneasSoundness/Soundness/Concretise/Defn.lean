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

/-! ### `maxKeyPlusOne` and `insert`

The load-bearing lemma used by `concretise_addLoan` (Phase B `M10.1f`):
inserting a fresh key `k` (i.e. `maxKeyPlusOne m ≤ k`) into `m` bumps
`maxKeyPlusOne` to exactly `k + 1`. The proof goes via
`Std.HashMap.toList_insert_perm` + `List.Perm.foldl_eq`
(`max` is right-commutative on `Nat`), plus two structural facts about
folding `max` over a list:

* `foldl_max_succ_mono`: starting accumulator grows monotonically through the fold.
* `foldl_max_succ_le`: the fold result is bounded above by `max acc B`
  whenever every key in the list is ≤ `B - 1`.
-/

/-- Folding `max acc (k'+1)` over a list is monotone in the starting
    accumulator. Auxiliary for `maxKeyPlusOne_insert_fresh`. -/
private theorem foldl_max_succ_mono {α : Type}
    (xs : List (Nat × α)) (acc₁ acc₂ : Nat) (h : acc₁ ≤ acc₂) :
    xs.foldl (fun acc p => max acc (p.1 + 1)) acc₁ ≤
      xs.foldl (fun acc p => max acc (p.1 + 1)) acc₂ := by
  induction xs generalizing acc₁ acc₂ with
  | nil => simpa
  | cons p ps ih =>
    simp only [List.foldl_cons]
    apply ih
    -- max is monotone in both args: max acc₁ x ≤ max acc₂ x.
    rcases Nat.lt_or_ge acc₁ (p.1 + 1) with h₁ | h₁
    · -- acc₁ < p.1 + 1, so max acc₁ (p.1+1) = p.1 + 1.
      rw [Nat.max_eq_right (Nat.le_of_lt h₁)]
      exact Nat.le_max_right _ _
    · -- p.1 + 1 ≤ acc₁, so max acc₁ (p.1+1) = acc₁.
      rw [Nat.max_eq_left h₁]
      exact le_trans h (Nat.le_max_left _ _)

/-- The starting accumulator is a lower bound on the fold result. -/
private theorem le_foldl_max_succ {α : Type}
    (xs : List (Nat × α)) (acc : Nat) :
    acc ≤ xs.foldl (fun acc p => max acc (p.1 + 1)) acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons]
    exact le_trans (Nat.le_max_left _ _) (ih _)

/-- If every key in `xs` is bounded by `k`, the fold stays bounded by `B`
    whenever the starting accumulator is bounded by `B` and `k + 1 ≤ B`. -/
private theorem foldl_max_succ_le_aux {α : Type}
    (xs : List (Nat × α)) (B : Nat)
    (hKeys : ∀ p ∈ xs, p.1 + 1 ≤ B) :
    ∀ (acc : Nat), acc ≤ B →
      xs.foldl (fun acc p => max acc (p.1 + 1)) acc ≤ B := by
  induction xs with
  | nil => intro acc hacc; simpa
  | cons p ps ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    have hp : p.1 + 1 ≤ B := hKeys p List.mem_cons_self
    have hps : ∀ q ∈ ps, q.1 + 1 ≤ B := fun q hq =>
      hKeys q (List.mem_cons_of_mem _ hq)
    apply ih hps
    exact Nat.max_le.mpr ⟨hacc, hp⟩

/-- If every key in `xs` is bounded by `k`, the fold is bounded by
    `max acc (k+1)`. -/
private theorem foldl_max_succ_le {α : Type}
    (xs : List (Nat × α)) (k acc : Nat)
    (hKeys : ∀ p ∈ xs, p.1 + 1 ≤ k + 1) :
    xs.foldl (fun acc p => max acc (p.1 + 1)) acc ≤ max acc (k + 1) := by
  apply foldl_max_succ_le_aux xs (max acc (k + 1))
  · intro p hp
    exact le_trans (hKeys p hp) (Nat.le_max_right _ _)
  · exact Nat.le_max_left _ _

/-- Bound for every key in the toList of a hashmap: every `(j+1)` is
    ≤ `maxKeyPlusOne m`. Auxiliary for `maxKeyPlusOne_insert_fresh`. -/
private theorem succ_le_maxKeyPlusOne_of_mem_toList {α : Type}
    (m : Std.HashMap Nat α) (p : Nat × α) (hp : p ∈ m.toList) :
    p.1 + 1 ≤ maxKeyPlusOne m := by
  unfold maxKeyPlusOne
  rw [Std.HashMap.fold_eq_foldl_toList]
  -- We show that for any prefix accumulator `acc`, if `p` is in the
  -- remaining list, then `p.1 + 1 ≤ foldl ... acc list`.
  suffices h : ∀ (xs : List (Nat × α)) (acc : Nat),
      p ∈ xs → p.1 + 1 ≤ xs.foldl (fun acc q => max acc (q.1 + 1)) acc by
    exact h m.toList 0 hp
  intro xs acc hpx
  induction xs generalizing acc with
  | nil => cases hpx
  | cons q qs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hpx with heq | htail
    · subst heq
      exact le_trans (Nat.le_max_right _ _) (le_foldl_max_succ qs _)
    · exact ih _ htail

/-- If every key in `m` is < `k+1` (equivalently, `maxKeyPlusOne m ≤ k`),
    then inserting `(k, v)` bumps `maxKeyPlusOne` to exactly `k + 1`. -/
theorem maxKeyPlusOne_insert_fresh {α : Type} (m : Std.HashMap Nat α)
    (k : Nat) (v : α) (hFresh : maxKeyPlusOne m ≤ k) :
    maxKeyPlusOne (m.insert k v) = k + 1 := by
  -- Step 1: rewrite via `fold_eq_foldl_toList`, then use the permutation
  -- of `(m.insert k v).toList` with `(k, v) :: m.toList.filter (¬k == ·.1)`.
  unfold maxKeyPlusOne
  rw [Std.HashMap.fold_eq_foldl_toList]
  have hPerm :
      (m.insert k v).toList.Perm (⟨k, v⟩ :: m.toList.filter (¬k == ·.1)) :=
    Std.HashMap.toList_insert_perm (m := m) (k := k) (v := v)
  -- Use `Perm.foldl_eq'` (Std variant taking an explicit comm argument).
  -- `max` is commutative + associative on `Nat`, hence the fold step
  -- `fun acc p => max acc (p.1 + 1)` is right-commutative.
  have hCommMax : ∀ (a b c : Nat), max (max a b) c = max (max a c) b := by
    intro a b c
    rw [Nat.max_assoc, Nat.max_comm b c, ← Nat.max_assoc]
  have hFoldEq :
      (m.insert k v).toList.foldl (fun acc (p : Nat × α) => max acc (p.1 + 1)) 0 =
      ((⟨k, v⟩ :: m.toList.filter (¬k == ·.1)) : List (Nat × α)).foldl
        (fun acc (p : Nat × α) => max acc (p.1 + 1)) 0 :=
    hPerm.foldl_eq'
      (f := fun acc (p : Nat × α) => max acc (p.1 + 1))
      (by intro x _ y _ z; simp [hCommMax]) 0
  rw [hFoldEq]
  -- Step 2: simplify the cons.
  simp only [List.foldl_cons, Nat.zero_max]
  -- Step 3: show every key in the filtered tail is ≤ k (from hFresh).
  have hAll : ∀ p ∈ m.toList.filter (fun p => ¬k == p.1), p.1 + 1 ≤ k + 1 := by
    intro p hp
    have hpMem : p ∈ m.toList := (List.mem_filter.mp hp).1
    have hp_bound : p.1 + 1 ≤ maxKeyPlusOne m :=
      succ_le_maxKeyPlusOne_of_mem_toList m p hpMem
    exact Nat.le_succ_of_le (le_trans hp_bound hFresh)
  -- Step 4: upper bound: fold ≤ max (k+1) (k+1) = k+1.
  have hUB : (m.toList.filter (fun p => ¬k == p.1)).foldl
      (fun acc p => max acc (p.1 + 1)) (k + 1) ≤ k + 1 := by
    have := foldl_max_succ_le
      (m.toList.filter (fun p => ¬k == p.1)) k (k + 1) hAll
    simpa [Nat.max_self] using this
  -- Step 5: lower bound: starting accumulator ≤ fold.
  have hLB : k + 1 ≤
      (m.toList.filter (fun p => ¬k == p.1)).foldl
        (fun acc p => max acc (p.1 + 1)) (k + 1) :=
    le_foldl_max_succ _ _
  exact Nat.le_antisymm hUB hLB

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
