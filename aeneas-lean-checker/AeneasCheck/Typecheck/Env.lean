import Std.Data.HashSet
import AeneasCheck.Raw.CertEvent

/-!
Typechecker environment. The direct-borrow subset only needs:
* the set of declared local ids in the current function,
* a counter of borrow ids the trace has produced so far so that
  `endBorrow` can be checked against `mutBorrow`.

We deliberately do not track LLBC types here. Type-level checks happen
in M6 when the LLBC# replayer matches each rule's preconditions; M5
just ensures the cert is *structurally* well-formed.
-/

namespace AeneasCheck.Typecheck

open AeneasCheck.Raw

/-- An error encountered while typechecking, attached to a 0-based
    event index when it originated inside an event. -/
structure CheckErr where
  fnId : Nat
  /-- `none` for "global" errors (signature, header). `some i` for the
      i-th event in the function's event list. -/
  eventIdx : Option Nat
  msg : String
  deriving Repr

def CheckErr.toString (e : CheckErr) : String :=
  match e.eventIdx with
  | some i => s!"[fn {e.fnId}, event {i}] {e.msg}"
  | none => s!"[fn {e.fnId}] {e.msg}"

instance : ToString CheckErr := ⟨CheckErr.toString⟩

/-- Per-function typechecker state. -/
structure FnEnv where
  fnId : Nat
  /-- The number of declared locals (we don't have their types at M5,
      so all checks reduce to bounds-checking against this count). -/
  numLocals : Nat
  /-- All currently-live mut borrow ids: set on `mutBorrow`, cleared on
      `endBorrow`. -/
  liveLoans : Std.HashSet Nat
  /-- Reborrow / shared loans created in the trace. The exit check
      only flags `liveLoans \ reborrowLoans` since reborrow/shared
      loans are caller-tied and end implicitly when the parent
      abstraction ends. -/
  reborrowLoans : Std.HashSet Nat
  /-- Borrow ids that were once live but have since been ended. We keep
      them so that a duplicate `endBorrow` produces a precise error. -/
  endedLoans : Std.HashSet Nat
  /-- 0-based event index — incremented as we walk the trace. -/
  cursor : Nat
  deriving Inhabited

def FnEnv.empty (fnId numLocals : Nat) : FnEnv := {
  fnId, numLocals,
  liveLoans := {}, reborrowLoans := {}, endedLoans := {},
  cursor := 0
}

abbrev TC α := StateT FnEnv (Except CheckErr) α

def emitErr {α} (msg : String) : TC α := do
  let st ← get
  StateT.lift (.error { fnId := st.fnId, eventIdx := some st.cursor, msg })

def advance : TC Unit := modify fun st => { st with cursor := st.cursor + 1 }

end AeneasCheck.Typecheck
