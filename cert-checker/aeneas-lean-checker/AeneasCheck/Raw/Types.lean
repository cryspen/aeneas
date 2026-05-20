/-
Raw, unchecked types mirroring Charon's LLBC.

Pattern: plain inductives, no invariants enforced. `Typecheck.*` raises
invariants. JSON parsers in `Json.*` build these directly from
`Lean.Json`. The point of "Raw" is to keep parsing decoupled from
well-formedness checks.
-/

namespace AeneasCheck.Raw

/-- Primitive integer types. Mirrors Charon's `int_ty` + `u_int_ty`. -/
inductive IntKind
  | u8 | u16 | u32 | u64 | u128 | usize
  | i8 | i16 | i32 | i64 | i128 | isize
  deriving Repr, BEq, DecidableEq

/-- LLBC literal types. -/
inductive LitTy
  | int (k : IntKind)
  | bool
  | char
  | float (bits : Nat)
  deriving Repr, BEq

/-- Reference kinds: shared `&T`, mutable `&mut T`. -/
inductive RefKind | shared | mut
  deriving Repr, BEq, DecidableEq

/--
Raw type expressions.

Direct-borrow subset only needs literals, references, and ADTs as
opaque type-decl-id heads. Tuples and arrays come in M9+.
-/
inductive RawTy
  | lit (t : LitTy)
  | mutRef (region : Nat) (inner : RawTy)
  | shrRef (region : Nat) (inner : RawTy)
  | adt (id : Nat) (args : Array RawTy)
  | tuple (args : Array RawTy)
  /-- M9.5i: a type variable reference. `index` is the de-Bruijn-style
      free-variable index that Charon emits inside `TVar (Free K)`
      type strings. The Lean translator pairs this with the
      surrounding declaration's `typeParams` list to resolve the
      index to a parameter name (e.g. `0` → `"T"`). -/
  | tyVar (index : Nat)
  /-- Opaque payload — the cert.json carries a fully-formed type as a
      pretty-printed string. The typechecker treats `.opaque` as `Top`
      (matches any RawTy when the canonical form is unavailable). -/
  | opaque (repr : String)
  deriving Repr, Inhabited

end AeneasCheck.Raw
