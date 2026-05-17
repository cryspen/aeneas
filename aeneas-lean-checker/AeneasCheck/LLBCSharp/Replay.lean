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

/-- Apply one event to the running symbolic state. The
    [strictJoin] flag (M9.6 / Option C, plan §4.1.2) enables the
    per-witness strict EvJoin check; it is propagated from
    [replayCrate]'s config and is off by default. -/
def stepEvent (st : SymState) (ev : Event) (strictJoin : Bool := false) :
    Result SymState := do
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
  | .call _ _ _ _ dst _ absSig => stepCall st dst absSig
  | .endAbs absId _ released tokenClearLocals =>
    stepEndAbs st absId released tokenClearLocals
  | .proj _ _ _ => .error "proj: not implemented until M10"
  | .symExpandMutBorrow svId bid innerSv parentAbs substLocals substLoans =>
    stepSymExpandMutBorrow st svId bid innerSv parentAbs substLocals substLoans
  | .join l r res witnesses =>
    stepJoin st l r res (witnesses := witnesses) (strict := strictJoin)
  | .loopInv _ invariant loanRegistry =>
    -- M12.0/M12.1: structural no-op. The OCaml side emits an
    -- EvLoopInv at the start of each loop's canonical synthesized
    -- body, paired with an EvLoopEnd at the end (see InterpLoops.ml).
    -- M9.6 (Option C, plan §4.1.3) — strict path: when
    -- [loanRegistry] is non-empty, register exactly the loans
    -- the OCaml side identified in the loop's input
    -- abstractions ((borrowId, parentAbsId) pairs from commit
    -- #9). When empty (v1 / hint-empty default), fall back to
    -- the M9.5z scan of [invariant.liveLoans] + [invariant.env]
    -- for [SymMutBorrowTok n] tokens. The parent_abs id is
    -- recorded by commit #19's AbsRegistry consumer.
    -- (M9.5aa loopDepth bump removed in commit #21 — the
    -- in-loop-borrow classification is now driven entirely by
    -- the OCaml emitter's MbkLoopOwned kindHint.)
    let mut st := st
    if loanRegistry.isEmpty then
      for b in invariant.liveLoans do
        if !st.loans.contains b then
          st := st.addLoan b .bottom .reborrow
      for (_, e) in invariant.env do
        match e with
        | .symMutBorrowTok b =>
          if !st.loans.contains b then
            st := st.addLoan b .bottom .reborrow
        | _ => pure ()
    else
      for (b, _parentAbs) in loanRegistry do
        if !st.loans.contains b then
          st := st.addLoan b .bottom .reborrow
    return st
  | .loopEnd _ =>
    -- M9.5aa loopDepth tracking retired in commit #21.
    return st
  | .matchArm _ _ _ _ =>
    -- M9.5d: structural no-op for the replayer. The `matchArm`
    -- marker partitions the trace into per-arm event ranges; the
    -- forward translator (not the replayer) walks those ranges and
    -- materialises the `PExpr.match`. No abstract state update.
    return st

/-- Replay a function's cert. The [strictJoin] flag (M9.6) is
    threaded through to [stepEvent.stepJoin]. -/
def replayFun (numLocals : Nat) (f : FunCert) (strictJoin : Bool := false) :
    Except String CheckedTrace := do
  let mut st := SymState.empty numLocals
  -- Initialize input locals with fresh symbolic values. For the M6
  -- subset we don't yet know which locals are inputs; we approximate
  -- by leaving everything at bottom and letting the trace populate.
  let mut idx := 0
  for ev in f.events do
    match stepEvent st ev strictJoin with
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
    errors before running the replayer. [strictJoin] (M9.6) toggles
    the per-witness EvJoin validation; off by default so callers
    that don't care (tests/Direct) keep working unchanged. The
    CLI reads the [AENEAS_STRICT_JOIN] env var and threads the
    flag in. -/
def replayCrate (cc : CrateCert) (strictJoin : Bool := false) :
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
    out := out.push (← replayFun numLocals f strictJoin)
  return out

end AeneasCheck.LLBCSharp
