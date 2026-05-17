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
  | .mutBorrow loan place symval kindHint =>
    stepMutBorrow st loan place symval kindHint
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
  | .reborrow child parent place parentLive parentAbs =>
    stepReborrow st child parent place parentLive parentAbs
  | .call _ _ _ _ dst _ _ => stepCall st dst
  | .endAbs _ _ released tokenClearLocals =>
    stepEndAbs st released tokenClearLocals
  | .proj _ _ _ => .error "proj: not implemented until M10"
  | .symExpandMutBorrow svId bid innerSv parentAbs substLocals substLoans =>
    stepSymExpandMutBorrow st svId bid innerSv parentAbs substLocals substLoans
  | .join l r res _ => stepJoin st l r res
  | .loopInv _ invariant _ =>
    -- M12.0/M12.1: structural no-op. The OCaml side emits an
    -- EvLoopInv at the start of each loop's canonical synthesized
    -- body, paired with an EvLoopEnd at the end (see InterpLoops.ml).
    -- The cert is already structurally checked by `checkEvent`; the
    -- LLBC# loop rule (T-Loop-Fixpoint) is structurally handled by
    -- the Forward translator. The semantic ≤-relation check lands in
    -- M12.3.
    -- M9.5z: register loop-introduced borrow ids (those in
    -- `invariant.liveLoans` and those appearing as `SymMutBorrowTok n`
    -- in `invariant.env`) so a subsequent in-body `EvEndBorrow` finds
    -- them in `loans`. Mark them `.reborrow`: their lifetime belongs
    -- to the loop iteration's abstraction rather than to a discrete
    -- in-body `EvMutBorrow`, so the function-exit leak check tolerates
    -- residual liveness.
    -- M9.5aa: also open a loop scope so `stepMutBorrow` knows to
    -- classify in-body direct `&mut local` as `.lazyExpand`.
    let mut st := { st with loopDepth := st.loopDepth + 1 }
    for b in invariant.liveLoans do
      if !st.loans.contains b then
        st := st.addLoan b .bottom .reborrow
    for (_, e) in invariant.env do
      match e with
      | .symMutBorrowTok b =>
        if !st.loans.contains b then
          st := st.addLoan b .bottom .reborrow
      | _ => pure ()
    return st
  | .loopEnd _ =>
    -- M9.5aa: close the matching loop scope.
    return { st with loopDepth := st.loopDepth - 1 }
  | .matchArm _ _ _ _ =>
    -- M9.5d: structural no-op for the replayer. The `matchArm`
    -- marker partitions the trace into per-arm event ranges; the
    -- forward translator (not the replayer) walks those ranges and
    -- materialises the `PExpr.match`. No abstract state update.
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
