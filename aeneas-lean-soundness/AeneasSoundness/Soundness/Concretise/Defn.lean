import AeneasCheck.LLBCSharp.State
import AeneasSoundness.LLBCSharpPaper.State
import AeneasSoundness.LLBCSharpPaper.WellFormed

/-!
# Concretisation `concretise : SymState → LLBCState` (M10.1a — partial)

Plan §2.1 / §1.3 commit B1. Lifts the replayer-side `SymState` into
the paper-side `LLBCState`. The lift is *lossy* — every replayer
abstraction the paper retains gets a faithful image, but ADT /
tuple / record values (which the M9.5d/f/p collapse already
approximates on the replayer side) project to `Val.opaq`.

## M10.1a scope (this commit)

This file lands the lift for the *env + numLocals* half of
`SymState`:

* `liftVal` — value-grammar lift `LLBCSharp.Val → LLBCSharpPaper.Val`.
* `liftEnv` — `Std.HashMap Nat LLBCSharp.Val → (LocalId → Option
  LLBCSharpPaper.Val)`. Missing locals lift to `none`; locals
  mapped to `.bottom` stay `.bottom`.
* `concretise` — the partial entry point. `ctx` is faithfully lifted
  via `liftEnv`; `abs` and `freshness` are placeholders (`abs :=
  fun _ => none`, `freshness := {}`) that M10.1b replaces.

After M10.1a, every per-event lemma that depends on the
`env`-image of `concretise` typechecks; lemmas that need the
`abs` or freshness counters still sorry (Phase C closes them after
M10.1b lands the other half).

## Why partial

Per plan §1.3 B1/B2 split: env + numLocals is the easy half. Loans
and absRegistry need the `RegionAbs.unknown` placeholder
infrastructure (plan §2.3 risk #2) to handle abs ids the cert
references before `EvCall` populates them. M10.1b adds that.

## Soundness sanity

`empty_concretise`: `concretise (SymState.empty 0) = LLBCState.empty`.
This is the smoke lemma that M10.1c will combine with
`LLBCState.empty_WellFormed` to flush the Phase-B vertical slice.
-/

namespace AeneasSoundness.Soundness.Concretise

open AeneasCheck.LLBCSharp
open AeneasSoundness.LLBCSharpPaper (LLBCState NonceCounters)

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

/-! ## Concretise (partial) -/

/-- M10.1a partial concretisation: lift `env` into `ctx`; leave
    `abs` and `freshness` as placeholders for M10.1b.

    Specifically:
    * `ctx := liftEnv st.env` — faithful per-local lift.
    * `abs := fun _ => none` — placeholder; M10.1b builds this
      from `st.absRegistry`.
    * `freshness := {}` — placeholder; M10.1b derives the next-id
      counters from `st.loans` / `st.absRegistry`. -/
def concretise (st : SymState) : LLBCState :=
  { ctx := liftEnv st.env
    abs := fun _ => none
    freshness := {} }

/-! ## Smoke lemma

The empty replayer state lifts to the empty paper state. Used by
M10.1c (`concretise_wellFormed_smoke`) and as a sanity probe that
the structure projections agree.
-/

theorem empty_concretise (n : Nat) :
    concretise (SymState.empty n) = LLBCState.empty := by
  unfold concretise SymState.empty LLBCState.empty
  congr 1
  funext l
  unfold liftEnv
  simp

end AeneasSoundness.Soundness.Concretise
