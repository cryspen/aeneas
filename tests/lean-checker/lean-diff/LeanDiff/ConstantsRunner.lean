import LeanDiff.Common
import constants

/-!
Differential runner for `constants` (Phase 4a wire-in, extended in
Session 5 Item 1).

Constants in `tests/src/constants.rs` exercise:
  - `pub const fn incr(u32)` — wraps; same as `incr_cert::incr`
  - `pub const fn mk_pair0(u32, u32) -> (u32, u32)` — tuple ctor
  - `pub const fn add(i32, i32) -> i32` — signed wraps; needs the
    Phase 4a-1 `HAdd I32 I32 (Result I32)` shim instance
  - Nullary `const`/`static` initialisers whose body the cert walker
    now resolves to the source-true reference rather than a typed
    placeholder. Session 5 Item 1 unblocked `X1`, `Q2`, `Q3`, `S2`,
    `YVAL`, `unwrap_y`, `get_z1`, `get_z2` by preserving Charon's
    `PlaceGlobal` info through the cert serializer and seeding the
    forward translator's var-map from it.

We still skip the constants whose body the cert walker emits as a
typed placeholder rather than the source-true value, because the
differential gate would flag the divergence as a fixture error when
it's really a known cert-translator gap. The skipped set after
Session 5 Item 1:

  - `Y`                    (returns `Wrap`, no `Show1 Wrap` here)
  - `mk_pair1`, `P1`, `P3`,
    `S3`, `S4`              (returns `Pair`, no `Show1 Pair` here)
  - `use_v`, `V.LEN`        (const-generic flow — seed pass skips
                             globals carrying generic args like
                             `<T, N>` because the cert doesn't surface
                             the caller's generic instantiation)

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
  -- Session 5 (Item 1): constants whose body now reads another global.
  -- Each line exercises a different walk-path:
  --   X1     — `u32::MAX` (cross-crate builtin global, shim-provided)
  --   Q2     — `Q1` (intra-crate i32 global, tail position)
  --   Q3     — `add(Q2, 3)` (global as call arg, requires let-bind)
  --   S2     — `incr(S1)` (global as call arg through a re-borrow temp)
  --   get_z1 — `Z1` (local-const-block tail position)
  --   get_z2 — chained `add(Q1, add(get_z1(), Q3))` (three globals)
  --   unwrap_y — `Y.value` (field access through a Result-typed global)
  --   YVAL   — `unwrap_y()` (call returning a Result, tail position)
  IO.println (mkLine "constants" "X1" [] constants.X1)
  IO.println (mkLine "constants" "Q2" [] constants.Q2)
  IO.println (mkLine "constants" "Q3" [] constants.Q3)
  IO.println (mkLine "constants" "S2" [] constants.S2)
  IO.println (mkLine "constants" "get_z1" [] constants.get_z1)
  IO.println (mkLine "constants" "get_z2" [] constants.get_z2)
  IO.println (mkLine "constants" "unwrap_y" [] constants.unwrap_y)
  IO.println (mkLine "constants" "YVAL" [] constants.YVAL)

end LeanDiff.ConstantsRunner
