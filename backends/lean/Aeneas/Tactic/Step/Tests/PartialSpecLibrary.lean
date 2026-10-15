module
import Aeneas.Std.Scalar
import Aeneas.Std.Slice
import Aeneas.Tactic.Step

/-!
# Tests: library operations stated with `partialSpec`

Panicking library operations are specified with `partialSpec`, so that:
- `step` uses them with the no-panic condition as a hypothesis to discharge;
- `mvcgen` proves partial correctness (`⇓?`) without any precondition;
- the success postcondition also implies the no-panic condition.
-/

namespace Aeneas.Std.PartialSpecLibraryTests

open Aeneas Aeneas.Std RustM Std.Do WP

set_option mvcgen.warning false

example (x y : U32) (h : y.val ≠ 0) : x / y ⦃ z => z.val = x.val / y.val ⦄ := by
  step*

example (x y : U32) : ⦃ ⌜ True ⌝ ⦄ (x / y) ⦃ ⇓? z => ⌜ z.val = x.val / y.val ⌝ ⦄ := by
  mvcgen

example (x y : U32) : ⦃ ⌜ True ⌝ ⦄ (x + y) ⦃ ⇓? z => ⌜ z.val = x.val + y.val ⌝ ⦄ := by
  mvcgen

/-- The success postcondition of `Slice.update` yields the bounds check. -/
example (s : Slice U8) (i : Usize) (v : U8) :
    ⦃ ⌜ True ⌝ ⦄ s.update i v ⦃ ⇓? ns => ⌜ i.val < s.length ∧ ns.length = s.length ⌝ ⦄ := by
  mvcgen
  simp_all

example (b : Bool) : ⦃ ⌜ True ⌝ ⦄ massert b ⦃ ⇓? _ => ⌜ b ⌝ ⦄ := by
  mvcgen

end Aeneas.Std.PartialSpecLibraryTests
