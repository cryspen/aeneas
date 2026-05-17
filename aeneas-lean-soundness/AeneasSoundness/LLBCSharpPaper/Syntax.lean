import Mathlib.Data.Multiset.Basic
import AeneasCheck.Raw.Places
import AeneasCheck.Raw.Literal

/-!
# LLBC# paper-side syntax: values, places, and region abstractions

This is the M10 Phase-A port of paper Fig. 2 + §4.1's value grammar
and region-abstraction skeleton (plan §1.1 row 1). The four axioms in
`Soundness/StepEventSound.lean` (`LLBCState`, `concretise`, `Valid`,
`LStep`) are progressively replaced over M10.0b–k; this file lands the
value grammar that `LLBCState` (M10.0c) and `LStep` (M10.0f–i) consume.

## Scope

The grammar covers the direct-borrow subset proved sound by this
campaign (plan §0 / §11.1 #8):

* Borrows and loans — mut + shared, with explicit loan ids and an
  inner value on the borrow side (the value that flows back on end).
* Symbolic values (paper `σ_n`), literals, `⊥`.
* Structured ADT / tuple / record aggregates for paper-completeness.
  The `concretise` map (Phase B) projects these to `.opaq` for the
  events we prove sound; the structured cases remain for the optional
  Phase G LLBC port.
* `.opaq` — the deliberate lossy projection target for the
  M9.5d/f/p ADT/tuple/record collapse.

## Re-use of the checker's `Place` / `Lit`

`Place#` and literal payloads are structurally identical to the
checker's `AeneasCheck.Raw.Place` / `AeneasCheck.Raw.Lit`; we alias
rather than redefine. The `ty : RawTy` field on `Place` is irrelevant
to `LStep` (typing is upstream) but is preserved for round-trip
fidelity with the cert.

## Region abstractions

Per plan §1.4 risk #1, this file commits to the **extrinsic,
multiset-based** representation: `RegionAbs.roles : Multiset
(Role × LoanId)`. Mathlib's `Multiset` plays well with `simp` /
`decide` on small cases and gives order-insensitive equality "for
free" (paper §4.1's `A_in(ρ)` is a *set* of role entries, not a
sequence).
-/

namespace AeneasSoundness.LLBCSharpPaper

open AeneasCheck.Raw (Lit Place ProjElem)

/-! ## Identifier abbreviations

The paper uses `ℓ` for loan ids, `σ` for symbolic-value ids, unnamed
ids for region abstractions, etc. We give them self-documenting type
aliases so signatures read close to the paper.
-/

/-- Loan id (paper `ℓ`). -/
abbrev LoanId := Nat

/-- Region-abstraction id. -/
abbrev AbsId := Nat

/-- Symbolic-value id (paper `σ_n`). -/
abbrev SymValId := Nat

/-- Local-variable id within a function's `ctx`. -/
abbrev LocalId := Nat

/-- Variant id within an ADT decl. -/
abbrev VariantId := Nat

/-- Field id within a struct/record decl. -/
abbrev FieldId := Nat

/-! ## Place (re-exported from `AeneasCheck.Raw.Place`)

The paper's `Place#` is structurally identical to the checker's flat
`Place`; we expose the checker's name directly to avoid the
French-quote-escaped identifier hazard (`«Place#»` would be needed at
every use site otherwise). Paper-side modules `open AeneasCheck.Raw
(Place ProjElem)` and write `Place` / `ProjElem` straight through.
-/

/-! ## Val# — the LLBC# value grammar (paper Fig. 2 + §4.1) -/

/-- Paper `Val#`. Constructors:

* `sym σ` — symbolic value (`σ_n`).
* `lit l` — concrete literal constant.
* `mutLoan ℓ` — the *loan side* `loan^m ℓ` of a mut borrow.
* `mutBorrow ℓ v` — the *borrow side* `borrow^m ℓ v`; `inner = v` is
  the value that flows back to the loan side on end.
* `sharedLoan ℓ` — `loan^s ℓ`.
* `sharedBorrow ℓ v` — `borrow^s ℓ v`.
* `bottom` — paper `⊥`; uninitialized / moved-out.
* `adt variantId fields` — a structured ADT constructor application.
* `tuple fields` — a tuple aggregate.
* `record fields` — a struct/record aggregate; entries are
  `(fieldId, value)` pairs.
* `opaq` — a deliberate lossy projection. `concretise` (Phase B)
  collapses ADT / tuple / record values to `.opaq` for the events we
  actually prove sound; the structured cases above remain for
  paper-completeness and the optional Phase G LLBC port.

The recursive `Array Val` arguments make this a nested inductive;
Lean 4's standard recursor handles it directly.
-/
inductive Val where
  | sym (σ : SymValId)
  | lit (l : Lit)
  | mutLoan (ℓ : LoanId)
  | mutBorrow (ℓ : LoanId) (inner : Val)
  | sharedLoan (ℓ : LoanId)
  | sharedBorrow (ℓ : LoanId) (inner : Val)
  | bottom
  | adt (variantId : VariantId) (fields : Array Val)
  | tuple (fields : Array Val)
  | record (fields : Array (FieldId × Val))
  | opaq

/-- `Val.bottom` is a natural default for the value type — every
    uninitialised local starts there in `LLBCState`. -/
instance : Inhabited Val := ⟨Val.bottom⟩

/-! ## Role / RegionAbs — paper §4.1 `A_in(ρ)` content -/

/-- The four roles a single `LoanId` can play inside a region
    abstraction (cf. paper §4.1 + the checker's `AbsRoleEntry`):

* `mutBorrow` / `sharedBorrow` — the abstraction owns the borrow side.
* `mutLoan` / `sharedLoan` — the abstraction owns the loan side
  (when the abs ends, the loan is released).
-/
inductive Role where
  | mutBorrow
  | mutLoan
  | sharedBorrow
  | sharedLoan
  deriving DecidableEq, Inhabited, Repr

/-- A region abstraction `A_in(ρ) { … }` per paper §4.1.

* `roles` — multiset of `(Role, LoanId)` entries the abstraction
  holds. Multiset (not array / list) because the paper's `A_in(ρ)`
  has no role ordering; `Multiset` makes the join algebra's
  permutation-up-to-equality come out for free.
* `parents` — ancestor abs ids (nested-borrow contracts).
-/
structure RegionAbs where
  roles : Multiset (Role × LoanId)
  parents : Array AbsId := #[]

/-- The empty region abstraction (no roles, no parents). Used as the
    `default` and as a seed for the join algebra. -/
def RegionAbs.empty : RegionAbs := { roles := 0, parents := #[] }

instance : Inhabited RegionAbs := ⟨RegionAbs.empty⟩

/-- Convenience: a region abstraction with a single `(role, ℓ)` entry
    and no parents. Used by `concretise` (Phase B) when lifting a
    standalone replayer-side loan into a one-role abs (the
    "placeholder" abs of plan §2.3 risk #2). -/
def RegionAbs.singleton (role : Role) (ℓ : LoanId) : RegionAbs :=
  { roles := {(role, ℓ)}, parents := #[] }

/-- Membership predicate: does this abs hold the given `(role, ℓ)`
    entry? `Multiset.Mem` lets Phase-C lemmas reason about the abs's
    contents without committing to a list order. -/
def RegionAbs.holds (a : RegionAbs) (role : Role) (ℓ : LoanId) : Prop :=
  (role, ℓ) ∈ a.roles

end AeneasSoundness.LLBCSharpPaper
