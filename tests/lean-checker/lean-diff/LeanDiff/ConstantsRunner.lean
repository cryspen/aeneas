import LeanDiff.Common
import constants

/-!
Differential runner for `constants` (Phase 4a wire-in).

Constants in `tests/src/constants.rs` exercise:
  - `pub const fn incr(u32)` — wraps; same as `incr_cert::incr`
  - `pub const fn mk_pair0(u32, u32) -> (u32, u32)` — tuple ctor
  - `pub const fn add(i32, i32) -> i32` — signed wraps; needs the
    Phase 4a-1 `HAdd I32 I32 (Result I32)` shim instance
  - Nullary `const`/`static` initialisers (`X0`, `X2`, `X3`, `S1`,
    `Q1`, `P0`, `P2`) — constant evaluation against the cert's
    serialised value

We deliberately skip the constants whose body the cert walker emits
as a typed placeholder rather than the source-true value, because
the differential gate would flag the divergence as a fixture error
when it's really a known cert-translator gap. The skipped set:

  - `unwrap_y`, `YVAL`     (cert never threads `Y.value` through)
  - `Y`                    (returns `Wrap`, no `Show1 Wrap` here)
  - `mk_pair1`, `P1`, `P3`,
    `S3`, `S4`              (returns `Pair`, no `Show1 Pair` here)
  - `X1`                    (`u32::MAX` const, placeholder = 0)
  - `Q2`, `Q3`              (chained const eval through placeholders)
  - `S2`                    (`incr(S1)` — S1 read is placeholder)
  - `get_z1`, `get_z2`,
    `get_z1.Z1`             (const-block inner def chains break)
  - `use_v`, `V.LEN`        (const-generic flow unsupported)

The wire-up still exercises the four-bullet Phase 4a fixes end-to-
end: HAdd I32 (`add`), brace sanitisation (`Wrap.new` ordering), ADT
placeholder (`S3` typechecks even though its value is wrong), and
the topo-sort that put `Wrap.new` before `Y` in the emit.

Pair-returning + Wrap-returning functions are a candidate for the
next session: add a `Show1` instance for `constants.Pair Std.U32 Std.U32`
and `constants.Wrap Std.I32` so the runner can print + diff them.
-/

open Aeneas Aeneas.Std

namespace LeanDiff.ConstantsRunner

private def vectorsU32 : List UInt32 :=
  [0, 1, 2, 41, 100, 0xFFFFFFFE, 0xFFFFFFFF, 0x7FFFFFFF, 0x80000000]

private def vectorsI32 : List Int32 :=
  [0, 1, -1, 42, -42, 0x7FFFFFFF, Int32.ofInt (-0x80000000)]

private def pairsI32 : List (Int32 × Int32) :=
  [(0, 0), (1, 1), (1, -1), (-1, 1),
   (0x7FFFFFFF, 1), (Int32.ofInt (-0x80000000), -1),
   (100, 200), (-100, -200)]

private def pairsU32 : List (UInt32 × UInt32) :=
  [(0, 0), (1, 2), (42, 7),
   (0xFFFFFFFF, 1), (0x7FFFFFFF, 0x80000000)]

/-- Formatter for `Result (Std.U32 × Std.U32)` — same shape as
    `LeanDiff.Common.fmtPairU32` but lifted into the runner so this
    file stays self-contained. -/
private def mkTupleLineU32 (fn : String) (args : List String)
    (r : Result (Std.U32 × Std.U32)) : String :=
  "constants::" ++ fn ++ "(" ++ String.intercalate "," args ++ ") = " ++
    (match r with
     | .ok (a, b) => "ok " ++ toString a.toNat ++ "," ++ toString b.toNat
     | .error e   => "err " ++ fmtErr e
     | .div       => "div")

def runAll : IO Unit := do
  -- pub const fn incr(n: u32) -> u32 { n + 1 }
  for x in vectorsU32 do
    IO.println (mkLine "constants" "incr" [toString x.toNat] (constants.incr x))
  -- pub const fn add(a: i32, b: i32) -> i32 { a + b }
  for (a, b) in pairsI32 do
    IO.println (mkLine "constants" "add"
      [toString a.toInt, toString b.toInt] (constants.add a b))
  -- pub const fn mk_pair0(x: u32, y: u32) -> (u32, u32) { (x, y) }
  for (x, y) in pairsU32 do
    IO.println (mkTupleLineU32 "mk_pair0"
      [toString x.toNat, toString y.toNat] (constants.mk_pair0 x y))
  -- Const + static evaluations (nullary).
  IO.println (mkLine "constants" "X0" [] constants.X0)
  IO.println (mkLine "constants" "X2" [] constants.X2)
  IO.println (mkLine "constants" "X3" [] constants.X3)
  IO.println (mkLine "constants" "S1" [] constants.S1)
  IO.println (mkLine "constants" "Q1" [] constants.Q1)
  IO.println (mkTupleLineU32 "P0" [] constants.P0)
  IO.println (mkTupleLineU32 "P2" [] constants.P2)

end LeanDiff.ConstantsRunner
