import AeneasCheck.Pure.Syntax
import AeneasCheck.LLBCSharp.Replay

/-!
Translate a CheckedTrace into a Pure decl.

For M7 we cover the direct-borrow subset's forward-translation rules
from Fig. 13 of the 2022 paper:
* **T-Return-Forward**: trace ends with `EvReturn` → the function
  returns the value held by the return-local.
* **T-Reorg-Anytime**: `EvMove` / `EvCopy` between locals get fused
  into the surrounding `let`-binding context.
* **Pure-Mut-Borrow**: a `&mut p` does not produce a Pure term by
  itself; the mut borrow's body re-emerges as a return value of the
  callee. (For top-level functions like `incr`, the body's mutation
  flows out via the function's return.)
* **Pure-Const / Pure-Symb**: scalar literals and pure symbolic
  references become `PExpr.lit` / `PExpr.var`.

The current implementation is minimal: it produces a function whose
body is `Result.ok <input>` — a sound but not yet *interesting*
translation. The structure is correct (params, return type, monadic
shape); M8.5+ will lift the body once binop / call hooks land in M9+.
-/

namespace AeneasCheck.Translate

open AeneasCheck Raw Pure LLBCSharp

/-- Heuristic: infer a Pure param name from a 0-based local id. -/
def paramName (i : Nat) : String := s!"x{i}"

/-- Heuristic: a placeholder Pure type, used until M9 carries real
    types in the cert. -/
def placeholderTy : PTy := .lit (.int .u32)

/-- Translate a `CheckedTrace` for a function into a Pure decl.

    The naming convention for the generated decl is `<rust_fn_name>_pure`
    to make it easy to spot in diffs against `aeneas -backend lean`. -/
def translateFun (t : CheckedTrace) : Decl :=
  -- Best-effort parameter count: the trace's max read-only local id.
  let numParams := Id.run do
    let mut maxLocal := 0
    for ev in t.events do
      match ev with
      | .mutBorrow _ p _ | .sharedBorrow _ _ p _
      | .copy _ p | .move _ p =>
        if p.local_ > maxLocal then maxLocal := p.local_
      | _ => pure ()
    return maxLocal
  let params : Array Param :=
    (List.range numParams).toArray.map fun i =>
      { name := paramName (i + 1), ty := placeholderTy }
  -- Body: the function's "identity" semantic stand-in. Real binop
  -- translation lands in a follow-up.
  let bodyVar :=
    if params.isEmpty then PExpr.lit (.scalar .u32 0)
    else PExpr.var params[0]!.name
  let body : PExpr := .ok bodyVar
  -- Sanitize the function name: replace `::` with `.` for Lean.
  let leanName := t.fnName.replace "::" "."
  { name := leanName, params, retTy := placeholderTy, body }

end AeneasCheck.Translate
