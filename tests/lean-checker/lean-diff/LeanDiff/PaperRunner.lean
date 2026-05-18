import LeanDiff.Common
import paper

/-!
Session 7 Item 3: differential runner for the `paper` fixture.

Only `paper::ref_incr` is exercised — the other decls in `paper.rs`
hit one of the still-open emit gaps (test_incr / test_choose use
`massert`-style side effects that our walker collapses to inert let
bindings; choose / list_nth_mut / call_choose use back-closures we
can't drive cleanly from this byte-stream harness; List + sum exercise
recursive enums whose match-arm scoping our walker still mangles).
Skip those at `aeneas-check --out` time so the file compiles; this
runner covers ref_incr alone (8 vectors × 1 fn = 8 vectors).
-/

open Aeneas Aeneas.Std

namespace LeanDiff.PaperRunner

private def vectorsI32 : List Int32 :=
  [0, 1, -1, 41, 0x7FFFFFFE, 0x7FFFFFFF, -0x80000000, -1]

def runAll : IO Unit := do
  for x in vectorsI32 do
    IO.println (mkLine "paper" "ref_incr" [toString x.toInt] (paper.ref_incr x))

end LeanDiff.PaperRunner
