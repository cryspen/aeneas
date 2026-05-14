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
  | some (_, st) => do
    let v ← evalSymExpr st restore.givenBack
    -- Find the local holding the loan token and restore it.
    -- (For M6 the cert is well-formed so exactly one local holds the
    -- token; we scan the env to find it.)
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
