import AeneasCheck.Raw.Types

/-!
Raw places: a flat (local, projection*) shape matching the cert.json
schema in `src/cert/cert_schema.json`. Charon's nested `place` is
flattened to a list during cert emission so the Lean parser stays
simple.
-/

namespace AeneasCheck.Raw

inductive ProjElem
  | deref
  | field (id : Nat)
  | ptrMetadata
  | projIndex
  | subslice
  deriving Repr, BEq

structure Place where
  local_ : Nat
  projection : Array ProjElem
  ty : RawTy
  deriving Repr, Inhabited

end AeneasCheck.Raw
