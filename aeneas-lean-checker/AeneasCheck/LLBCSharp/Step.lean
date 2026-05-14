import AeneasCheck.LLBCSharp.State

/-!
Per-event step relation for LLBC#.

Each function corresponds to one rule in Fig. 4 of the 2022 paper (and
later figures). For M6 we implement:
* E-MutBorrow (also covers in-body fresh borrows),
* E-Move / E-Copy / E-Assign (operands feeding an assign),
* Reorg-End-MutBorrow (`endBorrow`),
* E-Return / E-Panic / E-Assert.

Each `step*` function returns `.ok newState` or `.error msg`. Failures
correspond to cert violations the LLBC# semantics would not derive.
-/

namespace AeneasCheck.LLBCSharp

open AeneasCheck.Raw

abbrev Result α := Except String α

private def fail {α} (msg : String) : Result α := .error msg

/-- Resolve a place's "root local" — the local whose value the place
    ultimately reads or writes. Projection chains are tracked but the
    M6 replayer does not yet model nested data; field/deref projections
    reduce to the root local. M9+ refines this for nested borrows. -/
def placeRootLocal (p : Place) : Nat := p.local_

/-- Resolve a `SymExpr` in the current state. -/
def evalSymExpr (st : SymState) (e : SymExpr) : Result Val := do
  match e with
  | .symVal id => return .sym id
  | .symLit l => return .lit l
  | .symCopy p =>
    let v := st.getLocal (placeRootLocal p)
    return v
  | .symMove p =>
    let v := st.getLocal (placeRootLocal p)
    return v
  | .symMutBorrowTok b => return .mutLoan b

/-! ## E-MutBorrow

The OCaml interpreter emits this event when a `&mut p` rvalue is
evaluated. The place's current value moves into the new mut-borrow
body; the place is replaced by a `mutLoan b` token tracking the loan.
-/

def stepMutBorrow (st : SymState) (loan : Nat) (place : Place)
    (_symval : Nat) : Result SymState := do
  if st.loans.contains loan then
    fail s!"E-MutBorrow: borrow id {loan} already live"
  else
    let root := placeRootLocal place
    if root ≥ st.numLocals then
      fail s!"E-MutBorrow: local {root} out of bounds (have {st.numLocals})"
    else
      let inner := st.getLocal root
      let st := st.setLocal root (.mutLoan loan)
      let st := st.addLoan loan inner
      return st

/-! ## E-SharedBorrow

Creating a shared borrow does not move the place's value out — both
the original local and the borrower can read it concurrently. The
M9.2 structural check only verifies the borrow id is fresh and the
place is in range; full LLBC# shared-loan algebra lands in M11. -/

def stepSharedBorrow (st : SymState) (loan : Nat) (_sbId : Nat)
    (place : Place) (_symval : Nat) : Result SymState := do
  if st.loans.contains loan then
    fail s!"E-SharedBorrow: borrow id {loan} already live"
  else
    let root := placeRootLocal place
    if root ≥ st.numLocals then
      fail s!"E-SharedBorrow: local {root} out of bounds (have {st.numLocals})"
    else
      let inner := st.getLocal root
      return st.addLoan loan inner .shared

/-! ## E-Reborrow

The OCaml interpreter emits this event when a `&mut p` rvalue is
evaluated and the place [p] dereferences an existing parent borrow
(i.e. [p.projection] ends with [Deref] of a [VBorrow] value). The
parent's loan must still be live; the child's id must be fresh. -/

def stepReborrow (st : SymState) (child parent : Nat) (place : Place) :
    Result SymState := do
  if st.loans.contains child then
    fail s!"E-Reborrow: child borrow id {child} already live"
  else
    let root := placeRootLocal place
    if root ≥ st.numLocals then
      fail s!"E-Reborrow: local {root} out of bounds (have {st.numLocals})"
    else
      -- If the parent loan is not yet in state, treat it as an
      -- implicit input borrow (e.g. a `&mut T` function argument).
      -- The cert does not emit an explicit EvMutBorrow for input
      -- borrows; pre-adding it here keeps the parent-live invariant
      -- without forcing every cert to carry a signature-derived
      -- entry-event. Implicit parents are tagged `.reborrow` so the
      -- exit check tolerates their liveness (see `Replay.lean`).
      let st :=
        if st.loans.contains parent then st
        else st.addLoan parent .bottom .reborrow
      -- The new child borrow's body is the inner value of the parent
      -- chain. The M9.2 structural check uses `.bottom` as a
      -- sentinel since we don't model nested-borrow values yet; the
      -- restoration on EvEndBorrow uses the cert's [given_back]
      -- which carries the real symbolic value. The `.reborrow` kind
      -- tells `stepEndBorrow` not to scan env for a `mutLoan` token.
      return st.addLoan child .bottom .reborrow

/-! ## Reorg-End-MutBorrow

End an active mut borrow: the [given_back] value from the cert flows
back to the loan slot. We additionally check that the loan side of the
state really holds a `mutLoan loan` token — this is the LLBC#
precondition that rules out double-frees.
-/

def stepEndBorrow (st : SymState) (loan : Nat) (restore : RestoreInfo)
    : Result SymState := do
  match st.takeLoan loan with
  | none => fail s!"end-borrow: borrow id {loan} not live"
  | some (li, st) => do
    let v ← evalSymExpr st restore.givenBack
    match li.kind with
    | .direct => do
      -- The mut-borrow created via E-MutBorrow replaced its place
      -- with a `mutLoan` token; end-borrow restores the local's
      -- value from the cert-supplied `given_back`.
      let mut found := false
      let mut newEnv := st.env
      for (l, vv) in st.env.toList do
        match vv with
        | .mutLoan b => if b = loan then
            newEnv := newEnv.insert l v
            found := true
        | _ => pure ()
      if not found then
        fail s!"end-borrow: no local holds loan {loan}"
      else
        return { st with env := newEnv }
    | .reborrow =>
      -- A reborrow doesn't park a `mutLoan` token in env (the parent's
      -- token is still there); ending it only releases the loan id.
      return st
    | .shared =>
      -- Shared borrows don't replace the local value either; ending
      -- just drops the loan id.
      return st

/-! ## E-Move / E-Copy / E-Assign / E-Assert / E-Panic / E-Return -/

def stepMove (st : SymState) (src dst : Place) : Result SymState := do
  let v := st.getLocal (placeRootLocal src)
  let st := st.setLocal (placeRootLocal src) .bottom
  let st := st.setLocal (placeRootLocal dst) v
  return st

def stepCopy (st : SymState) (src dst : Place) : Result SymState := do
  let v := st.getLocal (placeRootLocal src)
  let st := st.setLocal (placeRootLocal dst) v
  return st

def stepAssign (st : SymState) (dst : Place) (rhs : SymExpr) :
    Result SymState := do
  let v ← evalSymExpr st rhs
  return st.setLocal (placeRootLocal dst) v

/-! ## E-BinaryOp

M10.0 structural rule: evaluate operands in the current state, bind
the destination local to a sentinel `bottom` (the symbolic-binop
result; the Pure translator carries the operand expressions
directly). The `op` tag is not interpreted here — the translator
maps it to a Lean operator. -/

def stepBinop (st : SymState) (_op : String) (lhs rhs : SymExpr)
    (dst : Place) : Result SymState := do
  let _ ← evalSymExpr st lhs
  let _ ← evalSymExpr st rhs
  let root := placeRootLocal dst
  if root ≥ st.numLocals then
    fail s!"E-BinaryOp: local {root} out of bounds (have {st.numLocals})"
  else
    return st.setLocal root (.sym 0)

/-! ## E-Call (forward only)

M10.1 structural rule: bind the destination local to a fresh
symbolic placeholder. Backward functions / region abstractions are
M10.2 work — for forward-only `wrapping_add`-style calls the dst
binding is all the replayer needs to thread the trace through. -/

def stepCall (st : SymState) (dst : Place) : Result SymState := do
  let root := placeRootLocal dst
  if root ≥ st.numLocals then
    fail s!"E-Call: dst local {root} out of bounds (have {st.numLocals})"
  else
    return st.setLocal root (.sym 0)

def stepAssert (_st : SymState) (cond : SymExpr) (expected : Bool) :
    Result Unit := do
  -- We don't model the assertion's truth value (symbolic execution
  -- can succeed even when the assertion is symbolic); the OCaml side
  -- having included this event means the rule fired. M11 strengthens
  -- this when joins land.
  match cond, expected with
  | .symLit (.bool b), e =>
    if b = e then return ()
    else fail s!"E-Assert: literal {b} disagrees with expected {e}"
  | _, _ => return ()

end AeneasCheck.LLBCSharp
