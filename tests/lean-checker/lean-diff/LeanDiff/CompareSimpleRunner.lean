import LeanDiff.Common
import compare_simple

/-!
Differential runner for `compare_simple`.

Covers `id_u32`, `incr_val`, and `add_u32`. `add_u32` is interesting
because the cert lowers it as a call to `core.num.U32.wrapping_add`
(the shim defines that qualified path), so it exercises the
qualified-call wiring in `RuntimeShim/Aeneas/Std.lean`.
-/

open Aeneas Aeneas.Std

namespace LeanDiff.CompareSimpleRunner

private def u32Samples : List UInt32 :=
  [0, 1, 2, 42, 0xFFFFFFFE, 0xFFFFFFFF, 0x80000000, 0x7FFFFFFF]

private def u32Pairs : List (UInt32 × UInt32) :=
  [(0, 0), (1, 2), (0xFFFFFFFF, 1), (0xFFFFFFFE, 1), (0xFFFFFFFF, 0xFFFFFFFF),
   (0x80000000, 0x80000000)]

def runAll : IO Unit := do
  for x in u32Samples do
    IO.println (mkLine "compare_simple" "id_u32" [toString x.toNat]
      (compare_simple.id_u32 x))
  for x in u32Samples do
    IO.println (mkLine "compare_simple" "incr_val" [toString x.toNat]
      (compare_simple.incr_val x))
  for (a, b) in u32Pairs do
    IO.println (mkLine "compare_simple" "add_u32" [toString a.toNat, toString b.toNat]
      (compare_simple.add_u32 a b))

end LeanDiff.CompareSimpleRunner
