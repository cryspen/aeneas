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
    -- Walk projections: Deref / Field / ProjIndex are accepted from
    -- M9 onward (reborrows + `&mut pair.fst` / `&mut xs[i]`). The
    -- cert currently records `ProjIndex` as an operand-less tag —
    -- the operand-carrying form lands when M10 wires real array
    -- indexing through the translator. Subslice / PtrMetadata stay
    -- gated to their respective milestones.
    for pe in p.projection do
      match pe with
      | .deref | .field _ | .projIndex => pure ()
      | .ptrMetadata =>
        emitErr "PtrMetadata projection: not supported until M10 (fat pointers)"
      | .subslice =>
        emitErr "Subslice projection: not supported until M9.1 (slices)"

def checkSymExpr (e : SymExpr) : TC Unit := do
  match e with
  | .symVal _ => pure ()
  | .symLit _ => pure ()
  | .symCopy p => checkPlace p
  | .symMove p => checkPlace p
  | .symMutBorrowTok _ => pure ()
  | .symVariant _ _ _ => pure ()

end AeneasCheck.Typecheck
