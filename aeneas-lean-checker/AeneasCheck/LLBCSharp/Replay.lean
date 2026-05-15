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
  | .sharedBorrow loan sbId place symval =>
    stepSharedBorrow st loan sbId place symval
  | .assign dst rhs => stepAssign st dst rhs
  | .move src dst => stepMove st src dst
  | .copy src dst => stepCopy st src dst
  | .endBorrow loan restore => stepEndBorrow st loan restore
  | .assert cond expected =>
    let _ ← stepAssert st cond expected
    return st
  | .binop op lhs rhs dst => stepBinop st op lhs rhs dst
  | .panic => return st
  | .retn => return st
  | .reborrow child parent place => stepReborrow st child parent place
  | .call _ _ _ _ dst _ => stepCall st dst
  | .endAbs _ _ => return st
  | .proj _ _ _ => .error "proj: not implemented until M10"
  | .join l r res => stepJoin st l r res
  | .loopInv _ _ =>
    -- M12.0: structural no-op. The OCaml side emits one EvLoopInv per
    -- syntactic loop carrying the fixpoint state summary; the cert is
    -- already structurally checked by `checkEvent`. The LLBC# loop
    -- rule (T-Loop-Fixpoint) lands in M12.1, at which point this
    -- branch will dispatch to `stepLoopInv` and verify that the
    -- invariant subsumes the post-iteration state. For now we thread
    -- the state through unchanged so downstream events keep replaying.
    return st

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
  -- Post-condition: no live *direct* loans at function exit.
  -- Reborrow and shared loans may remain live (they tie to the
  -- caller's borrow lifetime via End-Abstraction, which a future
  -- milestone models explicitly); a direct in-body mut borrow that
  -- never ends is always a cert bug.
  let leakedDirect : List Nat := st.loans.toList.filterMap fun (b, li) =>
    if li.kind == .direct then some b else none
  if !leakedDirect.isEmpty then
    throw s!"[fn {f.fnId} '{f.fnName}']: {leakedDirect.length} direct loan(s) live at exit: {leakedDirect}"
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
