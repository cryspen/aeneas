import AeneasCheck.Typecheck.Env

/-!
Place-level well-formedness:
* the local id must be within `[0, numLocals)`,
* the projection list must not contain placeholders the M5 subset
  cannot handle.
-/

namespace AeneasCheck.Typecheck

open AeneasCheck.Raw

def checkPlace (p : Place) : TC Unit := do
  let st ← get
  if p.local_ ≥ st.numLocals then
    emitErr s!"local id {p.local_} out of bounds (have {st.numLocals})"
  else
    -- Walk projections: M5 only accepts Deref / Field; ProjIndex /
    -- Subslice / PtrMetadata become valid in M9+ when arrays land.
    for pe in p.projection do
      match pe with
      | .deref | .field _ => pure ()
      | .ptrMetadata =>
        emitErr "PtrMetadata projection: not supported until M10 (fat pointers)"
      | .projIndex =>
        emitErr "Index projection: not supported until M9 (arrays)"
      | .subslice =>
        emitErr "Subslice projection: not supported until M9 (slices)"

def checkSymExpr (e : SymExpr) : TC Unit := do
  match e with
  | .symVal _ => pure ()
  | .symLit _ => pure ()
  | .symCopy p => checkPlace p
  | .symMove p => checkPlace p
  | .symMutBorrowTok _ => pure ()

end AeneasCheck.Typecheck
