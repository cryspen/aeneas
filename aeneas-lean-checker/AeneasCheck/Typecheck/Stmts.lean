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
    set { st with
      liveLoans := st.liveLoans.erase loan
      endedLoans := st.endedLoans.insert loan }
  else if st.endedLoans.contains loan then
    emitErr s!"endBorrow on already-ended loan {loan}"
  else
    emitErr s!"endBorrow on unknown loan {loan}"

def checkEvent (ev : Event) : TC Unit := do
  match ev with
  | .mutBorrow loan place _ => do
    checkPlace place
    addLoan loan
  | .sharedBorrow loan _ place _ => do
    checkPlace place
    -- Shared borrows are tracked separately from mut borrows in LLBC#
    -- but for the M5 structural check we treat them uniformly.
    addLoan loan
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
  | .panic => pure ()
  | .retn => pure ()
  -- Out-of-subset events: report a precise milestone.
  | .reborrow _ _ _ => emitErr "EvReborrow: not supported until M9"
  | .call _ _ _ _ _ => emitErr "EvCall: not supported until M10"
  | .endAbs _ _ => emitErr "EvEndAbs: not supported until M10"
  | .proj _ _ _ => emitErr "EvProj: not supported until M10"
  | .join _ _ _ => emitErr "EvJoin: not supported until M11"
  | .loopInv _ _ => emitErr "EvLoopInv: not supported until M12"

/-- Walk a function's event list. -/
def checkEvents (events : Array Event) : TC Unit := do
  for ev in events do
    checkEvent ev
    advance

/-- After replaying all events, no borrow should still be live. (This is
    a sanity check on cert *completeness*; the LLBC# replayer is what
    actually verifies semantic correctness.) -/
def checkFnPost : TC Unit := do
  let st ← get
  if st.liveLoans.size ≠ 0 then
    let ids := st.liveLoans.toList
    emitErr s!"function ended with live borrow(s): {ids}"

end AeneasCheck.Typecheck
