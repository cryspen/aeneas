import LeanDiff.Common
import scalars

/-!
Session 4 — differential runner for `scalars`.

`tests/src/scalars.rs` exercises a handful of `u32` / `i32`-typed
arithmetic, bit-shift, bitwise, and rotate primitives. The runner
covers the differential-testable subset:

  - `wrapping_add` / `wrapping_sub` on `u32` and `i32` (4 fns)
  - `>>` / `<<` by an `i32`-typed amount on `u32` and `i32` (4 fns;
    Charon emits the rhs as `2#i32`, which lands on the new Session-4
    `HShift{L,R} U32 I32` / `I32 I32` shim instances)
  - `add_and` — `(b & a) + (b & a)` on `u32`, where the `&` is pure
    `UInt32`-valued and would otherwise type-mismatch a monadic `←`
    bind; the LeanEmit Session-4 fix renders the bind as `let t :=
    (b &&& a)` (non-monadic) so the do-block stays Result-typed (1 fn)
  - `rotate_left` / `rotate_right` on `u32` and `i32` (4 fns)

Skipped per the Session-4 prompt:

  - `u32_default` / `i32_default`: emit lowers `Default::default()` to
    `core.default.U32.default`; the shim returns `ok 0` so the file
    compiles, but the test surface for `Default` is wider than one
    point.
  - `match_usize` / `match_isize`: the cert walker's match-arm lowering
    is incomplete (match_usize body emits `ok false`; match_isize
    emits `(x1 + 1#isize)`). Wait for cert-walker fix.
  - `u32_as_u16` / `u16_as_u32` / `u32_as_i16` / `i16_as_u32`: cert
    drops the `as` cast op. The shim's `CoeHead` instances let the
    file typecheck but the values would not differential-match the
    source Rust except on the no-op operand.
  - `u32_use_bits` / `i32_use_bits`: cert emits the `u32::BITS`
    constant as the `0#u32` placeholder.

Total: 13 fns × ~5 vectors each ≈ 60+ new differential lines.
-/

open Aeneas Aeneas.Std

namespace LeanDiff.ScalarsRunner

private def vectorsU32 : List UInt32 :=
  [0, 1, 2, 41, 0xDEADBEEF, 0xFFFFFFFE, 0xFFFFFFFF, 0x7FFFFFFF, 0x80000000]

private def vectorsI32 : List Int32 :=
  [0, 1, -1, 42, -42, 0x7FFFFFFF, Int32.ofInt (-0x80000000), Int32.ofInt 0xDEADBEEF]

private def pairsU32 : List (UInt32 × UInt32) :=
  [(0, 0), (1, 2), (0xFFFFFFFF, 1), (0xFFFFFFFE, 1),
   (0xFFFFFFFF, 0xFFFFFFFF), (0x80000000, 0x80000000),
   (0xDEADBEEF, 0xCAFEBABE)]

private def pairsI32 : List (Int32 × Int32) :=
  [(0, 0), (1, 1), (1, -1), (-1, 1),
   (0x7FFFFFFF, 1), (Int32.ofInt (-0x80000000), -1),
   (100, 200), (-100, -200)]

def runAll : IO Unit := do
  -- wrapping_add / wrapping_sub on u32 / i32
  for (a, b) in pairsU32 do
    IO.println (mkLine "scalars" "u32_use_wrapping_add"
      [toString a.toNat, toString b.toNat] (scalars.u32_use_wrapping_add a b))
  for (a, b) in pairsI32 do
    IO.println (mkLine "scalars" "i32_use_wrapping_add"
      [toString a.toInt, toString b.toInt] (scalars.i32_use_wrapping_add a b))
  for (a, b) in pairsU32 do
    IO.println (mkLine "scalars" "u32_use_wrapping_sub"
      [toString a.toNat, toString b.toNat] (scalars.u32_use_wrapping_sub a b))
  for (a, b) in pairsI32 do
    IO.println (mkLine "scalars" "i32_use_wrapping_sub"
      [toString a.toInt, toString b.toInt] (scalars.i32_use_wrapping_sub a b))

  -- Shifts (rhs literal in source is 2)
  for x in vectorsU32 do
    IO.println (mkLine "scalars" "u32_use_shift_right"
      [toString x.toNat] (scalars.u32_use_shift_right x))
  for x in vectorsI32 do
    IO.println (mkLine "scalars" "i32_use_shift_right"
      [toString x.toInt] (scalars.i32_use_shift_right x))
  for x in vectorsU32 do
    IO.println (mkLine "scalars" "u32_use_shift_left"
      [toString x.toNat] (scalars.u32_use_shift_left x))
  for x in vectorsI32 do
    IO.println (mkLine "scalars" "i32_use_shift_left"
      [toString x.toInt] (scalars.i32_use_shift_left x))

  -- (b & a) + (b & a)
  for (a, b) in pairsU32 do
    IO.println (mkLine "scalars" "add_and"
      [toString a.toNat, toString b.toNat] (scalars.add_and a b))

  -- rotate_left / rotate_right on u32 / i32
  for x in vectorsU32 do
    IO.println (mkLine "scalars" "u32_use_rotate_right"
      [toString x.toNat] (scalars.u32_use_rotate_right x))
  for x in vectorsI32 do
    IO.println (mkLine "scalars" "i32_use_rotate_right"
      [toString x.toInt] (scalars.i32_use_rotate_right x))
  for x in vectorsU32 do
    IO.println (mkLine "scalars" "u32_use_rotate_left"
      [toString x.toNat] (scalars.u32_use_rotate_left x))
  for x in vectorsI32 do
    IO.println (mkLine "scalars" "i32_use_rotate_left"
      [toString x.toInt] (scalars.i32_use_rotate_left x))

end LeanDiff.ScalarsRunner
