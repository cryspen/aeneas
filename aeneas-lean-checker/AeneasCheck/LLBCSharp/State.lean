import Std.Data.HashMap
import AeneasCheck.LLBCSharp.Values

/-!
LLBC# symbolic state — the executable mirror of OCaml's `eval_ctx`.

For the direct-borrow subset we track:
* per-local symbolic values (the `env`),
* the set of live mut-borrows + the symbolic value they restore upon
  ending (the `loans` map).

`SymState.empty` initializes everything to bottom; `Replay.lean`
populates locals from the function signature's input symbolic values.
-/

namespace AeneasCheck.LLBCSharp

open AeneasCheck.Raw

/-- How a loan was created. Affects how `endBorrow` restores state:
    a direct mut borrow replaces the borrowed local with a `mutLoan`
    token that the end must clear; a reborrow leaves the original
    parent's local untouched, so the end has no token to restore.
    M9.5r: `lazyExpand` loans come from EvSymExpandMutBorrow — they
    park a `mutLoan` token in the dst local (so end-borrow restores
    like `.direct`) but their lifetime is owned by the function's
    region abstraction (so they're allowed to leak past function
    exit, like `.reborrow`). -/
inductive LoanKind
  | direct
  | shared
  | reborrow
  | lazyExpand
  deriving Repr, BEq, Inhabited

/-- Info recorded for each live mut borrow: the inner symbolic value
    that flows back to the loan side upon `endBorrow`, and the loan
    kind so the end-borrow rule knows whether to scan for a `mutLoan`
    token in env. -/
structure LoanInfo where
  given : Val
  kind : LoanKind := .direct
  deriving Inhabited

structure SymState where
  /-- Per-local current value. -/
  env : Std.HashMap Nat Val
  /-- Active mut borrows. -/
  loans : Std.HashMap Nat LoanInfo
  /-- Number of locals declared in the current function. -/
  numLocals : Nat
  deriving Inhabited

namespace SymState

def empty (numLocals : Nat) : SymState := {
  env := {}, loans := {}, numLocals
}

/-- Lookup a local's current value; missing locals are `bottom`. -/
def getLocal (st : SymState) (l : Nat) : Val :=
  st.env.getD l .bottom

def setLocal (st : SymState) (l : Nat) (v : Val) : SymState :=
  { st with env := st.env.insert l v }

def hasLoan (st : SymState) (b : Nat) : Bool :=
  st.loans.contains b

def addLoan (st : SymState) (b : Nat) (inner : Val)
    (kind : LoanKind := .direct) : SymState :=
  { st with loans := st.loans.insert b { given := inner, kind } }

def takeLoan (st : SymState) (b : Nat) : Option (LoanInfo × SymState) :=
  match st.loans[b]? with
  | none => none
  | some li => some (li, { st with loans := st.loans.erase b })

end SymState

end AeneasCheck.LLBCSharp
