import Aeneas.Std.Scalar
import Aeneas.Std.Array
import Aeneas.Tactic.Step

open Aeneas Aeneas.Std Result
open Std.Internal.Do Lean.Order

set_option mvcgen.warning false

/-!
# Tests: `vcgen` spec generation from `@[step]`

For every `@[step]` theorem, the attribute handler also generates a `vcgen` spec (in addition to
the `mvcgen` one, see `MvcgenSpec.lean`). The first three tests below are the `vcgen`
counterparts of the `mvcgen` tests.

Note that we spell the goals as `Std.Internal.Do.Triple` applications rather than with the
`⦃ _ ⦄ _ ⦃ _ ⦄` notation: that notation clashes with Aeneas' own postfix `⦃ _ ⦄` notation for
`spec`, which would swallow the postcondition.
-/

namespace Aeneas.Step.VcgenSpecTests

example {x y : U8} (hmax : x.val + y.val ≤ U8.max) :
    Triple (x + y) True (fun z => z.val = x.val + y.val) (⊥ : VCGen.EPred) := by
  vcgen <;> scalar_tac

example {x y : U8} :
    Triple
      ((do
        if x < 10#u8
        then x * 2#u8
        else pure y : Result U8))
      True (fun z => z.val ≠ y.val → z.val < 20) (⊥ : VCGen.EPred) := by
  vcgen <;> scalar_tac

example (arr : Array U8 25#usize) (i : Usize) (a : U8) (hi : i < arr.length) :
    Triple (Array.update arr i a) True (fun r => r.get? i = some a) (⊥ : VCGen.EPred) := by
  vcgen <;> grind

/-! ## Tuple-destructuring binds

`let (x, y) ← e` elaborates to a bind whose continuation is wrapped in `Std.uncurry`;
`Std.WP.uncurry_vcgen_spec` lets `vcgen` see through it. -/

example {α : Type} (v : Slice α) (i : Usize) (h : i.val < v.length) :
    Triple
      ((do
        let (x, back) ← v.index_mut_usize i
        pure (back x) : Result (Slice α)))
      True (fun r => r = v.set i v.val[i.val]) (⊥ : VCGen.EPred) := by
  vcgen <;> simp_all [WP.uncurry'_eq]

/-! ## Generated specs

`@[step]` generates a `vcgen` spec for `spec` and `dspec` theorems too (through the `to_vcgen`
conversion lemma registered with `#register_spec_info`), not only for `partialSpec` ones (those
are covered by `SpecPartial.lean`). A `dspec` does not rule out divergence, hence the
`x ≠ div` precondition. -/

opaque myId (x : U32) : Result U32

@[step] axiom myId_spec (x : U32) : myId x ⦃ y => y = x ⦄

/--
info: Aeneas.Step.VcgenSpecTests.myId_spec.vcgen_spec (x : U32) (epost : VCGen.EPred) :
  True ⊑ wp (myId x) (fun y => y = x) epost
-/
#guard_msgs in
#check myId_spec.vcgen_spec

example (x : U32) : Triple (myId x) True (fun y => y = x) (⊥ : VCGen.EPred) := by
  vcgen

opaque myMaybeLoop (x : U32) : Result U32

@[step] axiom myMaybeLoop_dspec (x : U32) : WP.dspec (myMaybeLoop x) (fun y => y = x)

/--
info: Aeneas.Step.VcgenSpecTests.myMaybeLoop_dspec.vcgen_spec (x : U32) (epost : VCGen.EPred) :
  (¬myMaybeLoop x = div) ⊑ wp (myMaybeLoop x) (fun y => y = x) epost
-/
#guard_msgs in
#check myMaybeLoop_dspec.vcgen_spec

example (x : U32) (h : myMaybeLoop x ≠ div) :
    Triple (myMaybeLoop x) True (fun y => y = x) (⊥ : VCGen.EPred) := by
  vcgen
  simp_all

/-! ## The `Result` constructors -/

example {α : Type} (a : α) : Triple (Result.ok a) True (fun r => r = a) (⊥ : VCGen.EPred) := by
  vcgen

example {α : Type} (a : α) (epost : VCGen.EPred) (h : VCGen.willFail .panic epost) :
    Triple (Result.fail .panic : Result α) True (fun r => r = a) epost := by
  vcgen; assumption

example {α : Type} (a : α) (epost : VCGen.EPred) (h : VCGen.willDiverge epost) :
    Triple (Result.div : Result α) True (fun r => r = a) epost := by
  vcgen; assumption

/-! ## Loops

`Std.loop_vcgen_spec` is the `vcgen` counterpart of `Std.loop_spec`. As for `mvcgen`, it is not
picked up automatically (the invariant, the well-founded relation and the termination measure
have to be supplied), so we apply it explicitly. -/

/-- `count n` counts from `0` up to `n`. -/
def count (n : Usize) : Result Usize :=
  loop (β := Usize) (fun i =>
    if i < n then do
      let i' ← i + 1#usize
      ok (ControlFlow.cont i')
    else ok (ControlFlow.done i)) 0#usize

example (n : Usize) : Triple (count n) True (fun r => r = n) (⊥ : VCGen.EPred) := by
  unfold count
  refine Triple.intro (Std.loop_vcgen_spec
    (inv := fun i : Usize => i.val ≤ n.val)
    (rel := fun (x y : Nat) => x < y)
    (termination := fun i : Usize => n.val - i.val)
    (hwf := Nat.lt_wfRel.wf) (h_inv_init := by scalar_tac) ?_)
  intro i hi
  vcgen <;> scalar_tac

end Aeneas.Step.VcgenSpecTests
