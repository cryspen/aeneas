import LeanDiff.Common
import bitwise

/-!
Differential runner for `bitwise` (M9.5h fixture).

We exercise the four bit-op functions on `U32` plus the two
shift functions (`U32 >>>/<<<` by a `Usize` amount, `I32 >>>/<<<`
by an `Isize` amount). The shift amount is fixed in the Rust
source (`let i = 16`) — both `shift_u32` and `shift_i32` only
take the operand as their parameter.

Phase 1A: this runner was unblocked by adding the `#isize`,
`#i32`, `#i64` macros to `RuntimeShim/Aeneas/Std.lean`, which
previously left `16#isize` in the emitted source uninterpretable.
-/

open Aeneas Aeneas.Std

namespace LeanDiff.BitwiseRunner

private def vectorsU32 : List UInt32 :=
  [0, 1, 0xDEADBEEF, 0xFFFFFFFF, 0x80000000, 0x7FFFFFFF]

private def vectorsI32 : List Int32 :=
  [0, 1, -1, 0x7FFFFFFF, Int32.ofInt (-0x80000000), Int32.ofInt 0xDEADBEEF]

private def pairsU32 : List (UInt32 × UInt32) :=
  [(0, 0), (0xFFFFFFFF, 0), (0xFFFFFFFF, 0xFFFFFFFF),
   (0xDEADBEEF, 0xCAFEBABE), (0x55555555, 0xAAAAAAAA),
   (0x12345678, 0x87654321)]

def runAll : IO Unit := do
  for x in vectorsU32 do
    IO.println (mkLine "bitwise" "shift_u32" [toString x.toNat] (bitwise.shift_u32 x))
  for x in vectorsI32 do
    IO.println (mkLine "bitwise" "shift_i32" [toString x.toInt] (bitwise.shift_i32 x))
  for (a, b) in pairsU32 do
    IO.println (mkLine "bitwise" "xor_u32"
      [toString a.toNat, toString b.toNat] (bitwise.xor_u32 a b))
  for (a, b) in pairsU32 do
    IO.println (mkLine "bitwise" "or_u32"
      [toString a.toNat, toString b.toNat] (bitwise.or_u32 a b))
  for (a, b) in pairsU32 do
    IO.println (mkLine "bitwise" "and_u32"
      [toString a.toNat, toString b.toNat] (bitwise.and_u32 a b))

end LeanDiff.BitwiseRunner
