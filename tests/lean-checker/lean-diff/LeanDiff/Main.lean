import LeanDiff.IncrRunner
import LeanDiff.CompareSimpleRunner
import LeanDiff.CallsRunner
import LeanDiff.BitwiseRunner
import LeanDiff.ConstantsRunner
import LeanDiff.ScalarsRunner
import LeanDiff.DemoRunner
import LeanDiff.PaperRunner

/-! Lean side of the differential harness. Emits a stable
    `<fixture>::<fn>(args) = <result>` line per test vector. -/

def main : IO Unit := do
  LeanDiff.IncrRunner.runAll
  LeanDiff.CompareSimpleRunner.runAll
  LeanDiff.CallsRunner.runAll
  LeanDiff.BitwiseRunner.runAll
  LeanDiff.ConstantsRunner.runAll
  LeanDiff.ScalarsRunner.runAll
  LeanDiff.DemoRunner.runAll
  LeanDiff.PaperRunner.runAll
