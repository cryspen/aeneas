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
  /-- M10.1: a function call. `fnName` is the qualified callee name
      (e.g. `core::num::{u32}::wrapping_add`); the translator
      consumes it directly so we don't need a builtin-id lookup
      table. `regionAbs` is the abstraction-id list that M10.2's
      End-Abstraction rule consumes. -/
  | call (fn callId : Nat) (fnName : String) (args : Array SymExpr)
      (dst : Place) (regionAbs : Array Nat)
  | endAbs (abs : Nat) (finalValues : Array SymExpr)
  | proj (abs : Nat) (place : Place) (symval : Nat)
  | join (left right result : StateSummary)
  | loopInv (loopId : Nat) (invariant : StateSummary)
  /-- M12.1: end-of-loop-body marker. Paired with the preceding
      `loopInv` carrying the same `loopId`; the events between the
      pair form the canonical loop body that the Lean translator
      lifts into a `<fn>_loop.body` decl. -/
  | loopEnd (loopId : Nat)
  deriving Repr, Inhabited

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

/-- M9.5b: a single field inside a [TypeDecl]. `name` is `none` for
    tuple-style positional fields; the emitter falls back to
    `field<idx>` in that case. `ty` is the cert's opaque-tagged LLBC
    type string. -/
structure CertField where
  idx : Nat
  name : Option String
  ty : RawTy
  deriving Repr, Inhabited

/-- M9.5b: kind of an ADT declaration. Only `struct` is supported in
    the M9.5 chunk; other shapes (enum, union, alias) come through as
    `opaque`. -/
inductive TypeDeclKind
  | struct (fields : Array CertField)
  | opaque
  deriving Repr, Inhabited

/-- M9.5b: a crate-level ADT declaration. `id` is the LLBC
    `TypeDeclId.id` that appears inside `TAdt {id = TAdtId N; ...}` in
    cert-event place types; the Lean checker uses `id`→`name` lookups
    to translate borrowed-struct signatures and field projections. -/
structure TypeDecl where
  id : Nat
  name : String
  kind : TypeDeclKind
  deriving Repr, Inhabited

/-- Top-level cert. -/
structure CrateCert where
  fmtVersion : Nat
  crateHash : String
  /-- M9.5b: ADT type decls. May be empty for crates with no struct/
      enum types. The OCaml cert generator populates this from
      `crate.type_decls`; old certs that pre-date M9.5b have an empty
      array (the JSON parser tolerates a missing `type_decls` key). -/
  typeDecls : Array TypeDecl
  functions : Array FunCert
  deriving Repr, Inhabited

end AeneasCheck.Raw
