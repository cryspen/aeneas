import AeneasCheck.Raw.Places
import AeneasCheck.Raw.Literal

/-!
Raw certificate events — Lean mirror of `src/cert/CertEvent.ml`.

Direct-borrow subset (M2-M8): mutBorrow, sharedBorrow, assign, move,
copy, endBorrow, assert, panic, return. The rest are stubs that parse
but the replayer rejects in milestone-specific ways.
-/

namespace AeneasCheck.Raw

/-- A symbolic value reference or constant in a cert event RHS. -/
inductive SymExpr
  | symVal (id : Nat)
  | symLit (l : Lit)
  | symCopy (p : Place)
  | symMove (p : Place)
  | symMutBorrowTok (borrowId : Nat)
  deriving Repr

/-- Restoration info for an EvEndBorrow event. -/
structure RestoreInfo where
  givenBack : SymExpr
  deriving Repr

/-- A coarse summary of state at a point in evaluation. -/
structure StateSummary where
  env : Array (Nat × SymExpr)
  liveLoans : Array Nat
  deriving Repr, Inhabited

/-- LLBC# trace events. Constructor names match `CertEvent.event`
    (without the `Ev` prefix). -/
inductive Event
  -- direct-borrow subset
  | mutBorrow (loan : Nat) (place : Place) (symval : Nat)
  | sharedBorrow (loan : Nat) (sharedBorrowId : Nat) (place : Place) (symval : Nat)
  | assign (dst : Place) (rhs : SymExpr)
  | move (src dst : Place)
  | copy (src dst : Place)
  | endBorrow (loan : Nat) (restore : RestoreInfo)
  | assert (cond : SymExpr) (expected : Bool)
  | panic
  | retn
  /-- M10.0: a Charon `Rvalue.BinaryOp` reduction. `op` is the flat
      string tag emitted by OCaml's `cert_binop_string` (arithmetic
      ops bake the overflow mode in: `AddPanic` / `AddWrap` /
      `AddUB`, etc.). -/
  | binop (op : String) (lhs rhs : SymExpr) (dst : Place)
  -- later milestones
  | reborrow (child parent : Nat) (place : Place)
  | call (fn callId : Nat) (args : Array SymExpr) (dst : Place) (regionAbs : Array Nat)
  | endAbs (abs : Nat) (finalValues : Array SymExpr)
  | proj (abs : Nat) (place : Place) (symval : Nat)
  | join (left right result : StateSummary)
  | loopInv (loopId : Nat) (invariant : StateSummary)
  deriving Repr

/-- A source span attached to a cert function. Used by the Lean
    emitter to build the per-function `Source: ...` docstring. -/
structure SourceSpan where
  file : String
  begLine : Nat
  begCol : Nat
  endLine : Nat
  endCol : Nat
  deriving Repr, Inhabited

/-- Lean-side view of the Rust signature: input + output types as
    pretty-printed LLBC type strings (kept opaque until M9 carries
    proper Charon types in the cert). -/
structure FnSignature where
  inputs : Array RawTy
  output : RawTy
  deriving Repr, Inhabited

/-- Per-function cert trace. -/
structure FunCert where
  fnId : Nat
  fnName : String
  signature : FnSignature
  /-- `none` when the OCaml side could not attach a span (synthetic
      items, builtins). -/
  sourceSpan : Option SourceSpan
  events : Array Event
  finalState : StateSummary
  deriving Repr, Inhabited

/-- Top-level cert. -/
structure CrateCert where
  fmtVersion : Nat
  crateHash : String
  functions : Array FunCert
  deriving Repr, Inhabited

end AeneasCheck.Raw
