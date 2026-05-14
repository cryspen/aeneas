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

/-- Info recorded for each live mut borrow: the inner symbolic value
    that flows back to the loan side upon `endBorrow`. -/
structure LoanInfo where
  given : Val
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

def addLoan (st : SymState) (b : Nat) (inner : Val) : SymState :=
  { st with loans := st.loans.insert b { given := inner } }

def takeLoan (st : SymState) (b : Nat) : Option (LoanInfo × SymState) :=
  match st.loans[b]? with
  | none => none
  | some li => some (li, { st with loans := st.loans.erase b })

end SymState

end AeneasCheck.LLBCSharp
