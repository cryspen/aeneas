import AeneasCheck.Typecheck.Places

/-!
Per-event structural checks for the direct-borrow subset.

What M5 checks:
* mutBorrow / endBorrow are paired — every `endBorrow` matches a live
  borrow id, no double-end;
* places reference declared locals only;
* events from beyond the direct-borrow subset (Reborrow / Call /
  EndAbs / Proj / Join / LoopInv) are surfaced as
  "not-yet-supported" errors, mapping 1-1 to the M9/M10/M11 plan.

What M5 deliberately does *not* check: LLBC types. The LLBC# replayer
in M6 does that against the actual program.
-/

namespace AeneasCheck.Typecheck

open AeneasCheck.Raw

def addLoan (loan : Nat) : TC Unit := do
  let st ← get
  if st.liveLoans.contains loan then
    emitErr s!"borrow id {loan} already live"
  else if st.endedLoans.contains loan then
    emitErr s!"borrow id {loan} reused after being ended"
  else
    set { st with liveLoans := st.liveLoans.insert loan }

def removeLoan (loan : Nat) : TC Unit := do
  let st ← get
  if st.liveLoans.contains loan then
    -- M9.6: the OCaml cert emitter (commit #12) no longer emits
    -- the redundant post-join EvEndBorrow that the M9.5x
    -- joinDedupe fallback used to tolerate. Each loan is ended
    -- exactly once per function.
    set { st with
      liveLoans := st.liveLoans.erase loan
      endedLoans := st.endedLoans.insert loan }
  else if st.endedLoans.contains loan then
    emitErr s!"endBorrow on already-ended loan {loan}"
  else
    emitErr s!"endBorrow on unknown loan {loan}"

def checkEvent (ev : Event) : TC Unit := do
  match ev with
  | .mutBorrow loan place _ kindHint => do
    checkPlace place
    addLoan loan
    -- M9.6 (Option C, plan §7.1 #23) — strict-only path: the cert
    -- hint is the source of truth. .inAbsReborrow / .loopOwned
    -- mark the loan as reborrow-class; .direct is taken as
    -- truly direct (M9.5w's Deref-projection fallback retired,
    -- consistent with Step.stepMutBorrow).
    let leakClass : Bool :=
      match kindHint with
      | .inAbsReborrow _ | .loopOwned _ => true
      | .direct => false
    if leakClass then
      modify fun st => { st with reborrowLoans := st.reborrowLoans.insert loan }
  | .sharedBorrow loan _ place _ => do
    checkPlace place
    addLoan loan
    modify fun st => { st with reborrowLoans := st.reborrowLoans.insert loan }
  | .assign dst rhs => do
    checkPlace dst
    checkSymExpr rhs
  | .move src dst => do
    checkPlace src
    checkPlace dst
  | .copy src dst => do
    checkPlace src
    checkPlace dst
  | .endBorrow loan restore => do
    checkSymExpr restore.givenBack
    removeLoan loan
  | .assert cond _ => checkSymExpr cond
  | .binop _ lhs rhs dst => do
    checkSymExpr lhs
    checkSymExpr rhs
    checkPlace dst
  | .panic => pure ()
  | .retn => pure ()
  | .reborrow child _parent place _ _ => do
    checkPlace place
    addLoan child
    modify fun st => { st with reborrowLoans := st.reborrowLoans.insert child }
  -- Out-of-subset events: report a precise milestone.
  | .call _ _ _ args dst _ _ => do
    for a in args do checkSymExpr a
    checkPlace dst
  | .endAbs _ finals released _ => do
    -- M10.2: bounds-check any place references that flow through the
    -- abstraction's final-values list.
    for e in finals do checkSymExpr e
    -- M9.5s: implicit end-of-loan inside an abstraction. For each
    -- released loan: if it was tracked as live, move it to
    -- endedLoans (mirrors EvEndBorrow); if not tracked, silently
    -- accept — input-parameter loans created at the call's
    -- abstraction-build time never appear in our liveLoans set.
    let mut st ← get
    for loan in released do
      if st.liveLoans.contains loan then
        st := { st with
          liveLoans := st.liveLoans.erase loan
          endedLoans := st.endedLoans.insert loan }
    set st
  | .join left right result _ => do
    -- M11.1: structural check on the join witness. We bounds-check
    -- the SymExprs in each side's env (so a malformed cert is
    -- rejected up front), but defer the actual ≤-relation algebra
    -- to the LLBC# replayer (`stepJoin`). The typechecker's job is
    -- to ensure the witness is syntactically well-formed.
    for (_, e) in left.env do checkSymExpr e
    for (_, e) in right.env do checkSymExpr e
    for (_, e) in result.env do checkSymExpr e
    -- M9.6: M9.5x's joinDedupe / recentlyEnded promotion is gone
    -- (commit #12 fixed the OCaml side to not emit the redundant
    -- post-join EvEndBorrow that the dedupe used to swallow).
  | .loopInv _ invariant loanRegistry => do
    -- M9.5aa loopDepth bump removed in commit #21. The OCaml
    -- emitter now sets MbkLoopOwned for in-loop &mut local at
    -- emission time (commit #4), so the typechecker no longer
    -- needs to track loop nesting.
    -- M9.6 (Option C, plan §7.1 #23) — strict-only path:
    -- register exactly the (borrowId, parentAbsId) pairs the
    -- OCaml side identified. M9.5z env-scan fallback retired.
    modify fun st =>
      loanRegistry.foldl (init := st) fun st (b, _) =>
        if st.liveLoans.contains b || st.endedLoans.contains b then st
        else { st with
          liveLoans := st.liveLoans.insert b
          reborrowLoans := st.reborrowLoans.insert b }
    -- For M12.1 the replayer treats this event as a semantic no-op,
    -- and the Forward translator uses the position of EvLoopInv as
    -- the "begin loop body" marker (paired with EvLoopEnd).
    for (_, e) in invariant.env do checkSymExpr e
  | .loopEnd _ =>
    -- M12.1: structural no-op for the cert. EvLoopEnd is a
    -- sentinel marker for the Forward translator's
    -- T-Loop-Fixpoint walker; the replayer / typechecker
    -- ignore it. (M9.5x joinDedupe and M9.5aa loopDepth
    -- bookkeeping both retired in commits #20/#21.)
    pure ()
  | .matchArm scrutinee _ _ _ =>
    -- M9.5d: structural well-formedness on the match-arm marker. The
    -- arm body's events run separately and are checked one by one;
    -- here we only bounds-check the scrutinee place (when the cert
    -- emitted a SymCopy / SymMove form), which catches malformed
    -- certs early. The Forward translator interprets the marker
    -- semantically.
    checkSymExpr scrutinee
  | .symExpandMutBorrow _ bid _ _ _ _ =>
    -- M9.5r: register the freshly-minted concrete loan id so a
    -- subsequent EvEndBorrow on it doesn't trip
    -- "endBorrow on unknown loan". Mark it as a reborrow-class loan
    -- so checkFnPost tolerates it leaking past function exit (the
    -- loan's lifetime is owned by the abstraction created at the
    -- call site, not by an in-body EvMutBorrow). The LLBC# replayer's
    -- stepSymExpandMutBorrow does the corresponding state mutation.
    addLoan bid
    modify fun st => { st with reborrowLoans := st.reborrowLoans.insert bid }

/-- Walk a function's event list. -/
def checkEvents (events : Array Event) : TC Unit := do
  for ev in events do
    checkEvent ev
    advance

/-- After replaying all events, no *direct* mut borrow should still be
    live. Reborrow / shared loans tied to caller abstractions are
    allowed to leak through the exit (M11's End-Abstraction rule
    pops them implicitly). This is a sanity check on cert
    *completeness*; the LLBC# replayer is what actually verifies
    semantic correctness. -/
def checkFnPost : TC Unit := do
  let st ← get
  let leaked := st.liveLoans.toList.filter fun b => !st.reborrowLoans.contains b
  if !leaked.isEmpty then
    emitErr s!"function ended with live borrow(s): {leaked}"

end AeneasCheck.Typecheck
