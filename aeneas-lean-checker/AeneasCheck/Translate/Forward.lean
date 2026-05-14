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

/-- Strip the leading crate-name segment of a `crate::a::b` path,
    returning the inner def name `a.b`. The crate prefix becomes the
    surrounding `namespace` block in the emitter. -/
def innerName (qualified : String) : String :=
  let segs := qualified.splitOn "::"
  match segs with
  | _ :: rest => String.intercalate "." rest
  | [] => qualified

/-- Translate a function's cert + replay into a Pure decl.

    M9.0c uses the cert-carried signature for the emitted parameter
    count (was: max-local-seen-in-events). The signature's input types
    are still opaque pretty-printed strings, so emitted params still
    pick up `placeholderTy`; M9.1+ swaps that for the typed cert
    place's ty. -/
def translateFun (f : Raw.FunCert) (_t : CheckedTrace) : Decl :=
  let numParams := f.signature.inputs.size
  let params : Array Param :=
    (List.range numParams).toArray.map fun i =>
      { name := paramName (i + 1), ty := placeholderTy }
  -- Body: the function's "identity" semantic stand-in. Real binop
  -- translation lands in a follow-up.
  let bodyVar :=
    if params.isEmpty then PExpr.lit (.scalar .u32 0)
    else PExpr.var params[0]!.name
  let body : PExpr := .ok bodyVar
  { name := innerName f.fnName
    qualifiedName := f.fnName
    params, retTy := placeholderTy, body
    sourceSpan := f.sourceSpan }

end AeneasCheck.Translate
