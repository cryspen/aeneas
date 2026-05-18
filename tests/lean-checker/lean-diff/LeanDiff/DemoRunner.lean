import LeanDiff.Common
import demo

/-!
Differential runner for `demo` (Session 5 Item 2 wire-in).

`tests/src/demo.rs` has 16 emitted defs, but 11 of them have known
emit-side gaps that block a clean lake build of the full file:

  - `CList` inductive uses `@[discriminant isize]` (unknown attr)
  - `Counter` trait + `Std.Usize.Insts.DemoCounter` impl have a
    signature mismatch: the trait method is `Self → Result Std.Usize`
    but the impl emits `Self → Result (Std.Usize × (Unit → Std.Usize))`
  - `choose` returns a closure (M12.2a closure-emit placeholder)
  - `list_nth` / `list_nth_mut` / `list_tail` / `list_nth1` /
    `list_nth1_loop` / `list_nth1_loop.body` / `i32_id` have broken
    bodies (`ok ()` where `T` expected, `if x1` on non-bool, undefined
    `s33` / `t3`, `partial_fixpoint` on non-recursive)
  - `use_counter` references the broken `Counter` impl

The cert-regen pass at `scripts/run-diff.sh` passes
`--skip-decl <name>` for each, leaving the well-emitted subset:

  - `mul2_add1(x: u32) -> u32 { x * 2 + 1 }`
  - `use_mul2_add1(x: u32, y: u32) -> u32 { mul2_add1(x) + y }`
  - `incr(x: u32) -> u32 { x + 1 }`
  - `use_incr() -> ()` (calls `incr` three times, discards results)
  - `mod_add(x: u32, y: u32) -> u32` (Aeneas modular-add via
    `wrapping_sub(x + y, 3329)` then mask via `>> 16i32`)

`use_incr` returns `Result Unit`; we print a fixed `ok ()` line.
-/

open Aeneas Aeneas.Std

namespace LeanDiff.DemoRunner

private def vectorsU32 : List UInt32 :=
  [0, 1, 2, 41, 0xDEADBEEF, 0xFFFFFFFE, 0xFFFFFFFF, 0x7FFFFFFF, 0x80000000]

private def pairsU32 : List (UInt32 × UInt32) :=
  [(0, 0), (1, 2), (42, 7), (0xFFFFFFFF, 1), (0x7FFFFFFF, 0x80000000),
   (1000, 2329), (3328, 1), (3329, 3329)]

/-- `use_incr` returns `Result Unit`; format with a fixed `ok ()`. -/
private def fmtUnit (r : Result Unit) : String :=
  match r with
  | .ok () => "ok ()"
  | .error e => "err " ++ LeanDiff.fmtErr e
  | .div     => "div"

def runAll : IO Unit := do
  for x in vectorsU32 do
    IO.println (mkLine "demo" "mul2_add1" [toString x.toNat] (demo.mul2_add1 x))
  for (a, b) in pairsU32 do
    IO.println (mkLine "demo" "use_mul2_add1"
      [toString a.toNat, toString b.toNat] (demo.use_mul2_add1 a b))
  for x in vectorsU32 do
    IO.println (mkLine "demo" "incr" [toString x.toNat] (demo.incr x))
  IO.println ("demo::use_incr() = " ++ fmtUnit demo.use_incr)
  for (a, b) in pairsU32 do
    IO.println (mkLine "demo" "mod_add"
      [toString a.toNat, toString b.toNat] (demo.mod_add a b))

end LeanDiff.DemoRunner
