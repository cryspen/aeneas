import LeanDiff.Common
import calls

/-!
Differential runner for `calls` (M10.2 fixture).

We exercise the easy primitive-only sub-functions:
- `incr_inner` -- &mut u32 -> () lowered to U32 -> Result U32
- `incr_via_helper` -- same after delegating
- `pick` -- bool + 2x U32 join via if-then-else; ends with
  `core.num.U32.wrapping_add t0 1`.

`choose` and `use_choose` are skipped: they return a closure
`(Std.U32 -> (Std.U32 × Std.U32))` for the cert's backward-function
encoding, which our Show1 framework does not format.
-/

open Aeneas Aeneas.Std

namespace LeanDiff.CallsRunner

private def u32Samples : List UInt32 :=
  [0, 1, 41, 42, 99, 0xFFFFFFFE, 0xFFFFFFFF]

def runAll : IO Unit := do
  for x in u32Samples do
    IO.println (mkLine "calls" "incr_inner" [toString x.toNat]
      (calls.incr_inner x))
  for x in u32Samples do
    IO.println (mkLine "calls" "incr_via_helper" [toString x.toNat]
      (calls.incr_via_helper x))
  -- pick: (b, x, y) -> if b then x+1 else y+1 (wrapping).
  let triples : List (Bool × UInt32 × UInt32) :=
    [(true, 0, 99), (false, 0, 99), (true, 42, 7), (false, 42, 7),
     (true, 0xFFFFFFFF, 0), (false, 0xFFFFFFFF, 0),
     (true, 0, 0xFFFFFFFF), (false, 0, 0xFFFFFFFF)]
  for (b, x, y) in triples do
    let bs := if b then "true" else "false"
    IO.println (mkLine "calls" "pick" [bs, toString x.toNat, toString y.toNat]
      (calls.pick b x y))

end LeanDiff.CallsRunner
