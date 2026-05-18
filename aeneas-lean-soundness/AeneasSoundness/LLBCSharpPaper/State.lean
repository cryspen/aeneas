import AeneasSoundness.LLBCSharpPaper.Syntax

/-!
# LLBC# paper-side state: `LLBCState` (Ω#)

This is plan §1.1 row 2 / §1.3 commit A3 — the paper's `Ω#` state.
An `LLBCState` is a triple `(ctx, abs, freshness)` per paper §4.1:

* `ctx : LocalId → Option Val` — per-local current value (Option
  rather than total to encode "this local has not been declared").
* `abs : AbsId → Option RegionAbs` — per-abstraction-id contents;
  populated by `EvCall.absSig` on the replayer side.
* `freshness : NonceCounters` — monotone counters for fresh loan /
  symbolic-value / abs id generation.

## Representation choice

We use function-typed maps (`Nat → Option _`) rather than
`Std.HashMap` so the per-event soundness lemmas can reason about
extensional equality (`hCtx : st1.ctx = st2.ctx`) without the
HashMap-permutation tax. This is the standard mathlib idiom for
finite-domain functions, and works cleanly with `funext` /
`Function.update`-style proofs.

`Function.update` is provided via the lakefile's Mathlib dep
(`Mathlib.Logic.Function.Basic`); the soundness package hard-depends
on Mathlib for `Multiset` anyway, so this is free. We re-export the
relevant operations as `LLBCState.setLocal` / `setAbs` so the
paper-side syntax is self-contained.

## Place resolution

`Ω(p)` resolves a place into a value by walking the place's
projection chain. For the direct-borrow subset:

* `local x` resolves to `ctx x`.
* `*` (deref) inside `borrow^m ℓ v` resolves to `v` (i.e. derefing a
  mut borrow yields its inner value).
* `.field i` on a record / adt / tuple resolves to the i'th field.

Per the M9.5d/f/p coarse-abstraction policy (`Val.opaq`), derefing or
projecting into an `.opaq` returns `.opaq`. Phase C lemmas avoid
introspecting `.opaq` values; the place-resolution function is the
single point where the coarse abstraction is acknowledged.
-/

namespace AeneasSoundness.LLBCSharpPaper

open AeneasCheck.Raw (Place ProjElem)

/-! ## Freshness counters -/

/-- Monotone counters used by `LStep` rules that introduce fresh
    identifiers. Each `LStep` rule that consumes an id checks the
    cert's named id (`ℓ`, `σ`, `abs`) is ≥ the counter and bumps the
    counter past it. -/
structure NonceCounters where
  nextLoanId : Nat := 0
  nextAbsId : Nat := 0
  nextSymValId : Nat := 0
  deriving Inhabited

/-! ## LLBCState (Ω#) -/

/-- Paper `Ω#`. Three fields per §4.1:

* `ctx` — per-local current value. `none` means "the local is not
  declared in this state" (distinct from `some Val.bottom`, which
  means "declared but uninitialised / moved out").
* `abs` — per-abstraction-id contents. `none` means "no abstraction
  with this id has been created"; once an `EvCall` ships its
  `absSig`, an entry lands here.
* `freshness` — monotone next-available counters.
-/
structure LLBCState where
  ctx : LocalId → Option Val
  abs : AbsId → Option RegionAbs
  freshness : NonceCounters
  deriving Inhabited

namespace LLBCState

/-- The empty state — all locals undeclared, no abstractions, all
    freshness counters at 0. -/
def empty : LLBCState :=
  { ctx := fun _ => none
    abs := fun _ => none
    freshness := {} }

/-! ## Reads -/

/-- `Ω(x)` for a local id. Returns `none` if the local is undeclared
    (distinct from `some .bottom`). -/
def getLocal (Ω : LLBCState) (x : LocalId) : Option Val :=
  Ω.ctx x

/-- `Ω(abs)` for an abstraction id. -/
def getAbs (Ω : LLBCState) (a : AbsId) : Option RegionAbs :=
  Ω.abs a

/-! ## Writes -/

/-- Set the value at a local. -/
def setLocal (Ω : LLBCState) (x : LocalId) (v : Val) : LLBCState :=
  { Ω with ctx := Function.update Ω.ctx x (some v) }

/-- Declare a local with a starting value (alias for `setLocal`; the
    distinction matters only at the function-prologue level). -/
def declareLocal (Ω : LLBCState) (x : LocalId) (v : Val) : LLBCState :=
  Ω.setLocal x v

/-- Mark a local as undeclared (rare; only used by `EvEndAbs` on
    abstraction-owned bindings). -/
def clearLocal (Ω : LLBCState) (x : LocalId) : LLBCState :=
  { Ω with ctx := Function.update Ω.ctx x none }

/-- Install a region abstraction. -/
def setAbs (Ω : LLBCState) (a : AbsId) (r : RegionAbs) : LLBCState :=
  { Ω with abs := Function.update Ω.abs a (some r) }

/-- Remove a region abstraction (used by `LStep.endAbs`). -/
def removeAbs (Ω : LLBCState) (a : AbsId) : LLBCState :=
  { Ω with abs := Function.update Ω.abs a none }

/-- M10.x.6 (paper-side mirror of the replayer's `tokenClearOne`). The
    `LStep.endAbs` rule's post-state folds this over each
    `tokenClearLocals` entry: if the slot holds a `Val.mutLoan _` token
    it gets rewritten to `.bottom`; non-mutLoan slots (including
    `none`) are unchanged. The conditional matches the replayer's
    `match newEnv[l]? with | some (.mutLoan _) => ... | _ => ...`
    arm-for-arm, with `liftVal` preserving the `.mutLoan` constructor
    so the per-step commute closes by case analysis. -/
def clearMutLoanToken (Ω : LLBCState) (x : LocalId) : LLBCState :=
  match Ω.ctx x with
  | some (.mutLoan _) => Ω.setLocal x .bottom
  | _ => Ω

/-! ## Freshness -/

/-- Bump `nextLoanId` past `ℓ`. Idempotent if `ℓ < nextLoanId`. -/
def bumpLoanId (Ω : LLBCState) (ℓ : LoanId) : LLBCState :=
  { Ω with freshness :=
      { Ω.freshness with nextLoanId := max Ω.freshness.nextLoanId (ℓ + 1) } }

/-- Bump `nextAbsId` past `a`. -/
def bumpAbsId (Ω : LLBCState) (a : AbsId) : LLBCState :=
  { Ω with freshness :=
      { Ω.freshness with nextAbsId := max Ω.freshness.nextAbsId (a + 1) } }

/-- Bump `nextSymValId` past `σ`. The replayer doesn't track
    sym-value ids — `concretise` sets `nextSymValId := 0` and
    `CertGen_faithful` carries the cert-side monotonicity guarantee.
    To preserve `concretise st' = Ω'` across `LStep` constructors
    that pick a fresh sym-value id, this is a no-op at the paper
    level: Phase C M10.2f's stepBinop_sound is the first lemma to
    rely on this. -/
def bumpSymValId (Ω : LLBCState) (_σ : SymValId) : LLBCState := Ω

/-- `ℓ` is fresh in `Ω` iff `nextLoanId ≤ ℓ`. -/
def loanIdFresh (Ω : LLBCState) (ℓ : LoanId) : Prop :=
  Ω.freshness.nextLoanId ≤ ℓ

/-- `σ` is fresh in `Ω`. -/
def symValIdFresh (Ω : LLBCState) (σ : SymValId) : Prop :=
  Ω.freshness.nextSymValId ≤ σ

/-- `a` is fresh in `Ω`. -/
def absIdFresh (Ω : LLBCState) (a : AbsId) : Prop :=
  Ω.freshness.nextAbsId ≤ a

/-! ## Place resolution `Ω(p) ⇒ v`

The paper's place resolution walks the projection chain on the
current value. For the direct-borrow subset:

* Empty projection: `Ω(local x) = Ω.ctx x`.
* `deref` on `borrow^m ℓ v`: drops the borrow tag, yields `v`.
* `deref` on `borrow^s ℓ v`: same.
* `field i` on `record fs`: looks up `fs[i]` by field id.
* `field i` on `adt _ fs` / `tuple fs`: indexes into the array.
* `field i` on `.opaq`: stays `.opaq` (coarse-abstraction policy).
* Deref / field on any other value: undefined (returns `none`); a
  well-formed cert never asks.
-/

/-- Walk a single projection step. -/
def stepProj (v : Val) : ProjElem → Option Val
  | .deref =>
      match v with
      | .mutBorrow _ inner => some inner
      | .sharedBorrow _ inner => some inner
      | .opaq => some .opaq
      | _ => none
  | .field i =>
      match v with
      | .record fs =>
          (fs.find? (fun (j, _) => j = i)).map Prod.snd
      | .adt _ fs => fs[i]?
      | .tuple fs => fs[i]?
      | .opaq => some .opaq
      | _ => none
  | .ptrMetadata => none
  | .projIndex => none
  | .subslice => none

/-- Resolve a projection chain starting from `v`. Fails on the first
    ill-typed step. -/
def resolveProj (v : Val) : List ProjElem → Option Val
  | [] => some v
  | p :: ps =>
      match stepProj v p with
      | none => none
      | some v' => resolveProj v' ps

/-- `Ω(p)` — full place resolution. -/
def resolvePlace (Ω : LLBCState) (p : Place) : Option Val :=
  match Ω.getLocal p.local_ with
  | none => none
  | some v => resolveProj v p.projection.toList

/-- Projection-tolerant root-local read. Returns the value at
    `p.local_` defaulted to `.bottom` when the local is undeclared.

    Mirrors the replayer's `placeRootLocal + getLocal` semantics for
    `E-Move` / `E-Copy`: those events operate on the root local
    regardless of the projection chain, and treat undeclared locals
    as `.bottom` (via `Std.HashMap.getD`). M10.x.3 replaced
    `LStep.move` / `LStep.copy`'s `resolvePlace`-based premise with
    a premise-free formulation that reads via `resolvePlaceRoot`;
    the change discharged the `CertGen_faithful.move` / `.copy`
    extractors at the soundness boundary. -/
def resolvePlaceRoot (Ω : LLBCState) (p : Place) : Val :=
  (Ω.getLocal p.local_).getD .bottom

end LLBCState

end AeneasSoundness.LLBCSharpPaper
