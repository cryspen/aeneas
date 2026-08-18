module
import Aeneas.Std.Slice
import Aeneas.Std.Array
import Aeneas.Tactic.Step

/-!
# Tests: empty subslices

Rust allows empty ranges such as `s[i..i]` (including `s.len()..s.len()`): the subslice and
subslice-update operations must succeed whenever `start ≤ end ≤ len`.
-/

namespace Aeneas.Std.EmptySubsliceTests

open Aeneas Aeneas.Std RustM

example (s : Slice U8) (i : Usize) (h : i.val ≤ s.length) :
    Slice.subslice s ⟨i, i⟩ ⦃ ns => ns.length = 0 ⦄ := by
  step*

example (a : Array U8 4#usize) :
    Array.subslice a ⟨4#usize, 4#usize⟩ ⦃ s => s.length = 0 ⦄ := by
  step*

example (s ss : Slice U8) (i : Usize) (h : i.val ≤ s.length) (hss : ss.length = 0) :
    Slice.update_subslice s ⟨i, i⟩ ss ⦃ _ => True ⦄ := by
  step*

example (a : Array U8 4#usize) (ss : Slice U8) (hss : ss.length = 0) :
    Array.update_subslice a ⟨4#usize, 4#usize⟩ ss ⦃ _ => True ⦄ := by
  step*

end Aeneas.Std.EmptySubsliceTests
