import LeanDiff.Common
import incr_cert

/-!
Differential runner for `incr_cert` (M8 vertical-slice fixture).

We exercise both `incr` and `incr_local`: the cert pipeline collapses
the `&mut u32` borrow in `incr` to a take-and-return-by-value
function, and `incr_local` already takes by value. Both should
compute `x.wrapping_add(1)` on the Rust side.
-/

open Aeneas Aeneas.Std

namespace LeanDiff.IncrRunner

private def vectorsU32 : List UInt32 :=
  [0, 1, 2, 41, 0xFFFFFFFE, 0xFFFFFFFF, 0x7FFFFFFF, 0x80000000]

def runAll : IO Unit := do
  for x in vectorsU32 do
    IO.println (mkLine "incr_cert" "incr" [toString x.toNat] (incr_cert.incr x))
  for x in vectorsU32 do
    IO.println (mkLine "incr_cert" "incr_local" [toString x.toNat] (incr_cert.incr_local x))

end LeanDiff.IncrRunner
