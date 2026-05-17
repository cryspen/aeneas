import AeneasCheck

/-!
M12.2b: distinct-lifetime helper fixture.

`swap_pair<'a, 'b>(x: &'a mut u32, y: &'b mut u32) -> (&'a mut u32,
&'b mut u32)` is the smallest fixture exercising multi-region call
shapes. Each of the two `&mut` inputs lives in its own region, so
the standard Aeneas backend emits *two* backward closures (one per
region) rather than a single closure as it does for the `&'a`-only
`choose` helper.

This test asserts the checker now produces:

* **Callee `swap_pair`:** a 3-element flat tuple return type
  `Result ((U32 × U32) × (U32 → U32) × (U32 → U32))`, with each back
  closure being identity (pass-through).
* **Caller `use_swap_pair`:** a 3-name destructure
  `let (_v, _back0, _back1) ← swap_pair x1 x2`, with each
  deref-write through the destructured borrow applying its
  corresponding closure, and a tail tuple built from both.
-/

open AeneasCheck Json LLBCSharp Typecheck Translate Backends

def main : IO Unit := do
  IO.println "M12.2b multi-region tests:"
  let cc ← readCrateCert "tests/Direct/multi_region.cert.json"
  -- Typecheck + replay must accept the cert.
  match checkCrateCert cc with
  | .ok _ => IO.println "  ✓ multi_region.cert.json typechecks"
  | .error errs =>
    for e in errs do IO.eprintln s!"    {e}"
    throw <| IO.userError "expected accept"
  match replayCrate cc with
  | .ok _ => IO.println "  ✓ multi_region.cert.json replays"
  | .error msg =>
    throw <| IO.userError s!"replay failed: {msg}"
  -- The EvCall in use_swap_pair must carry TWO region_abs entries.
  let nMultiCalls := cc.functions.foldl (init := 0) fun acc f =>
    acc + (f.events.foldl (init := 0) fun a e => match e with
      | .call _ _ _ _ _ regs _ => if regs.size ≥ 2 then a + 1 else a
      | _ => a)
  if nMultiCalls ≥ 1 then
    IO.println s!"  ✓ saw {nMultiCalls} EvCall with ≥ 2 region_abs"
  else
    throw <| IO.userError "expected ≥ 1 multi-region EvCall"
  -- Translate must succeed and produce both the callee's
  -- N-back-closure shape and the caller's N-name destructure.
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "multi_region" tc
    let mustContain : List String := [
      -- Callee: 3-element return tuple + two identity closures.
      "Result ((Std.U32 × Std.U32) × (Std.U32 → Std.U32) × (Std.U32 → Std.U32))",
      "ok ((x1, x2), fun ret0 => ret0, fun ret1 => ret1)",
      -- Caller: 3-name destructure of the multi-region call.
      "def use_swap_pair (x1 : Std.U32) (x2 : Std.U32) : Result (Std.U32 × Std.U32)",
      "let (x1_post_v, x1_post_back0, x1_post_back1) ← (multi_region.swap_pair x1 x2)",
      -- Tail tuple built from both back-closure applications.
      "x1_post_back0 7#u32",
      "x1_post_back1 9#u32"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln "  --- emitted source ---"
        IO.eprintln src
        throw <| IO.userError "multi-region emit shape regressed"
      else
        IO.println s!"  ✓ contains: {c}"
  IO.println "all tests passed"
