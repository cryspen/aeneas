import AeneasCheck.LLBCSharp.Step
import AeneasCheck.Typecheck.Types

/-!
Drive the per-event step relation over a function's cert trace,
threading the symbolic state.

Output: a `CheckedTrace` — the cert events plus the final
`SymState`. M7's translator consumes this directly.
-/

namespace AeneasCheck.LLBCSharp

open AeneasCheck.Raw

structure CheckedTrace where
  fnId : Nat
  fnName : String
  events : Array Event
  finalState : SymState
  deriving Inhabited

/-- Apply one event to the running symbolic state. -/
def stepEvent (st : SymState) (ev : Event) : Result SymState := do
  match ev with
  | .mutBorrow loan place symval => stepMutBorrow st loan place symval
  | .sharedBorrow _ _ _ _ =>
    .error "shared borrows: not implemented in M6"
  | .assign dst rhs => stepAssign st dst rhs
  | .move src dst => stepMove st src dst
  | .copy src dst => stepCopy st src dst
  | .endBorrow loan restore => stepEndBorrow st loan restore
  | .assert cond expected =>
    let _ ← stepAssert st cond expected
    return st
  | .panic => return st
  | .retn => return st
  | .reborrow _ _ _ => .error "reborrow: not implemented until M9"
  | .call _ _ _ _ _ => .error "call: not implemented until M10"
  | .endAbs _ _ => .error "endAbs: not implemented until M10"
  | .proj _ _ _ => .error "proj: not implemented until M10"
  | .join _ _ _ => .error "join: not implemented until M11"
  | .loopInv _ _ => .error "loopInv: not implemented until M12"

/-- Replay a function's cert. -/
def replayFun (numLocals : Nat) (f : FunCert) : Except String CheckedTrace := do
  let mut st := SymState.empty numLocals
  -- Initialize input locals with fresh symbolic values. For the M6
  -- subset we don't yet know which locals are inputs; we approximate
  -- by leaving everything at bottom and letting the trace populate.
  let mut idx := 0
  for ev in f.events do
    match stepEvent st ev with
    | .ok st' => st := st'
    | .error e =>
      throw s!"[fn {f.fnId} '{f.fnName}', event {idx}]: {e}"
    idx := idx + 1
  -- Post-condition: no live loans at function exit.
  if st.loans.size ≠ 0 then
    let ids := st.loans.toList.map (·.fst)
    throw s!"[fn {f.fnId} '{f.fnName}']: {ids.length} loan(s) live at exit: {ids}"
  return { fnId := f.fnId, fnName := f.fnName, events := f.events, finalState := st }

/-- Replay a whole crate cert. Typechecks first to surface structural
    errors before running the replayer. -/
def replayCrate (cc : CrateCert) :
    Except String (Array CheckedTrace) := do
  -- Reuse the typechecker as a syntactic guard.
  match Typecheck.checkCrateCert cc with
  | .error errs =>
    let msgs := errs.map (·.toString)
    throw <| String.intercalate "\n" msgs
  | .ok _ => pure ()
  let mut out : Array CheckedTrace := #[]
  for f in cc.functions do
    -- numLocals approximation: infer from events (same as the
    -- typechecker). M6.5 / M9 will replace with the LLBC signature.
    let numLocals := Typecheck.inferNumLocals f.events
    out := out.push (← replayFun numLocals f)
  return out

end AeneasCheck.LLBCSharp
