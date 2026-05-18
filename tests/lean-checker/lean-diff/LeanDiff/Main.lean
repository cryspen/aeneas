import LeanDiff.IncrRunner
import LeanDiff.CompareSimpleRunner
import LeanDiff.CallsRunner
import LeanDiff.BitwiseRunner

/-! Lean side of the differential harness. Emits a stable
    `<fixture>::<fn>(args) = <result>` line per test vector. -/

def main : IO Unit := do
  LeanDiff.IncrRunner.runAll
  LeanDiff.CompareSimpleRunner.runAll
  LeanDiff.CallsRunner.runAll
  LeanDiff.BitwiseRunner.runAll
