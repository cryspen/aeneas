import AeneasCheck

/-!
M9.5h bitwise + shift translation tests.

Covers the pure-vs-monadic binop taxonomy distinction (see
`Forward.lean::isPureBinop`):
* **Pure binops** (`BitXor` / `BitAnd` / `BitOr`): return the operand
  type directly, so the emitter must wrap them in `ok` at the do-tail.
  Without the M9.5h fix, the tail of `xor_u32` was the bare expression
  `(x1 ^^^ x2)` — a `Std.U32`, not a `Result Std.U32`, which the
  standard Aeneas backend would reject.
* **Monadic shifts** (`ShlPanic` / `ShrPanic`): the cert always emits
  the panic variants for surface-level `<<` / `>>`. The emitter binds
  these in `let tN ← <shift>` and collapses the last such binding into
  the do-tail when it matches `ok (var tN)`, producing the standard
  backend's `do let t ← a >>> 16#usize; t <<< 16#usize` shape for
  `shift_u32` / `shift_i32`.

The test exhaustively asserts the body of each of the five functions
in `tests/src/bitwise.rs` (both positive — `ok (x1 ^^^ x2)` is
present — and a couple of negative checks: the bare `do (x1 ^^^ x2)`
shape must NOT appear, and no `let t1 ← <pure-binop>; ok t1` shape
should leak into the output).
-/

open AeneasCheck Json LLBCSharp Typecheck Translate Backends

def expectAccept (path : System.FilePath) : IO Unit := do
  let cc ← readCrateCert path
  match checkCrateCert cc with
  | .ok _ => IO.println s!"  ✓ {path} typechecks"
  | .error errs =>
    for e in errs do IO.eprintln s!"    {e}"
    throw <| IO.userError s!"expected accept, got reject: {path}"
  match replayCrate cc with
  | .ok _ => IO.println s!"  ✓ {path} replays"
  | .error msg =>
    IO.eprintln s!"    {msg}"
    throw <| IO.userError s!"expected replay, got error: {path}"
  match translateCrate cc with
  | .ok tc => IO.println s!"  ✓ {path} translates ({tc.decls.size} decls)"
  | .error msg =>
    throw <| IO.userError s!"expected translate, got: {msg}"

def main : IO Unit := do
  IO.println "M9.5h bitwise tests:"
  expectAccept "tests/Direct/bitwise.cert.json"
  let cc ← readCrateCert "tests/Direct/bitwise.cert.json"
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"bitwise translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "bitwise" tc
    -- Positive substring checks: each function's signature + body
    -- must be exactly the standard-backend-matching shape.
    let mustContain : List String := [
      -- Pure binops: `xor_u32 / or_u32 / and_u32` must wrap their
      -- single binop in `ok`. Without the M9.5h fix this read as a
      -- bare `(x1 ^^^ x2)` — ill-typed in the standard backend's
      -- non-shimmed `Std`.
      "def xor_u32 (x1 : Std.U32) (x2 : Std.U32) : Result Std.U32 := do",
      "ok (x1 ^^^ x2)",
      "def or_u32 (x1 : Std.U32) (x2 : Std.U32) : Result Std.U32 := do",
      "ok (x1 ||| x2)",
      "def and_u32 (x1 : Std.U32) (x2 : Std.U32) : Result Std.U32 := do",
      "ok (x1 &&& x2)",
      -- Monadic shifts: panic-shifts emit `Shl` / `Shr` heads (which
      -- `isPureBinop` reports `false`), so the last-binding collapse
      -- inlines the second shift as the bare do-tail and the first
      -- shift remains a `let t0 ← …`. The standard backend's output
      -- is structurally identical (modulo cosmetic literal rendering
      -- — `16#usize` vs `16#usize`).
      "def shift_u32 (x1 : Std.U32) : Result Std.U32 := do",
      "let t0 ← (x1 >>> 16#usize)",
      "(t0 <<< 16#usize)",
      "def shift_i32 (x1 : Std.I32) : Result Std.I32 := do",
      "let t0 ← (x1 >>> 16#isize)",
      "(t0 <<< 16#isize)"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "bitwise body regressed (M9.5h)"
      else
        IO.println s!"  ✓ contains: {c}"
    -- Negative checks: the pre-fix malformed shapes must NOT appear.
    let mustNotContain : List String := [
      -- The bare-pure-binop tail. If this re-appears, the
      -- pure-binop ok-wrap regressed.
      "do\n  (x1 ^^^ x2)",
      "do\n  (x1 &&& x2)",
      "do\n  (x1 ||| x2)",
      -- A `let tN ← (pure-binop); ok tN` pair would mean the
      -- collapse-and-wrap rule misfired. We don't expect to see
      -- the assembled letIn shape for any of the pure ops.
      "let t0 ← (x1 ^^^ x2)",
      "let t0 ← (x1 &&& x2)",
      "let t0 ← (x1 ||| x2)",
      -- A redundant `ok tN` tail after the LAST shift binding would
      -- mean the last-binding collapse misfired on the shift case.
      "(t0 <<< 16#usize)\n  ok",
      "(t0 <<< 16#isize)\n  ok"
    ]
    for c in mustNotContain do
      if (src.splitOn c).length ≥ 2 then
        IO.eprintln s!"  ✗ found forbidden substring: {c}"
        IO.eprintln src
        throw <| IO.userError "bitwise body has malformed shape (M9.5h regression)"
      else
        IO.println s!"  ✓ absent: {c}"
  IO.println "all tests passed"
