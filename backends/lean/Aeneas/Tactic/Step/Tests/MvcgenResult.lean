module
import Aeneas.Std.Scalar
import Aeneas.Tactic.Step

/-!
# Tests: `mvcgen` specs for the error monad

`mvcgen` must handle `ok`, `fail`, `loop` and `uncurry` through the library's `@[spec]` lemmas,
both for total (`⇓`) and partial (`⇓?`) correctness. The `PostCond` accessors must project the
success, failure and divergence parts of a postcondition.
-/

namespace Aeneas.Std.MvcgenResultTests

open Aeneas Aeneas.Std RustM Std.Do WP

set_option mvcgen.warning false

/- ## `ok` and `fail` -/

example : ⦃ ⌜ True ⌝ ⦄ (ok 3 : RustM Nat) ⦃ ⇓ r => ⌜ r = 3 ⌝ ⦄ := by
  mvcgen

example : ⦃ ⌜ True ⌝ ⦄ (fail .panic : RustM Nat) ⦃ ⇓? r => ⌜ r = 3 ⌝ ⦄ := by
  mvcgen

example : ¬ ⦃ ⌜ True ⌝ ⦄ (fail .panic : RustM Nat) ⦃ ⇓ r => ⌜ r = 3 ⌝ ⦄ := by
  simp [Triple, WP.wp, PredTrans.apply]

/- ## `PostCond` accessors -/

example (Q : PostCond Nat RustM.postShape) :
    PostCond.ok Q 3 ↔ (Q.1 3).down := Iff.rfl

example (Q : PostCond Nat RustM.postShape) (e : Error) :
    PostCond.fail Q e ↔ (Q.2.1 (ULift.up e)).down := Iff.rfl

/-- Partial correctness allows divergence, total correctness does not. -/
example : PostCond.div (⇓? (_ : Nat) => ⌜ False ⌝ : PostCond Nat RustM.postShape) := by
  simp [PostCond.div]

example : ¬ PostCond.div (⇓ (_ : Nat) => ⌜ True ⌝ : PostCond Nat RustM.postShape) := by
  simp [PostCond.div]

/- ## Tuples in a `do` block go through `uncurry` -/

def pair (x : Nat) : RustM (Nat × Nat) := ok (x, x + 1)

example (x : Nat) :
    ⦃ ⌜ True ⌝ ⦄ (do let (a, b) ← pair x; ok (a + b)) ⦃ ⇓ r => ⌜ r = 2 * x + 1 ⌝ ⦄ := by
  mvcgen [pair]
  omega

/- ## Loops -/

def countdown (n : Nat) : RustM Nat :=
  loop (fun i => if i = 0 then ok (.done 0) else ok (.cont (i - 1))) n

/-- Total correctness: the measure must decrease. -/
example (n : Nat) : ⦃ ⌜ True ⌝ ⦄ countdown n ⦃ ⇓ r => ⌜ r = 0 ⌝ ⦄ := by
  unfold countdown
  apply loop_spec (fun _ => True) (· < ·) id Nat.lt_wfRel.wf trivial
  intro i _
  split <;> mvcgen
  exact ⟨trivial, .inl (by simp only [id]; omega)⟩

/-- Partial correctness: no measure is needed. -/
example (n : Nat) : ⦃ ⌜ True ⌝ ⦄ countdown n ⦃ ⇓? r => ⌜ r = 0 ⌝ ⦄ := by
  unfold countdown
  apply loop_spec (fun _ => True) (fun (_ _ : Nat) => False) id
    ⟨fun _ => ⟨_, fun _ h => h.elim⟩⟩ trivial
  intro i _
  split <;> mvcgen
  simp [PostCond.div]

/- ## Triples and `ok` -/

example (x y : U8) (h : x.val + y.val ≤ U8.max) :
    ∃ z, x + y = ok z ∧ z.val = x.val + y.val := by
  apply triple_iff_exists_ok.1
  mvcgen
  scalar_tac

end Aeneas.Std.MvcgenResultTests
