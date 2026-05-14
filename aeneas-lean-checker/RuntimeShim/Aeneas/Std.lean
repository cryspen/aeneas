/-!
Minimal `Aeneas.Std` runtime shim for the aeneas-lean-checker tests.

This namespace mirrors enough of `backends/lean/Aeneas/Std/` for
*generated* Lean files to typecheck without pulling in mathlib. It
deliberately does NOT mirror the proof-side lemmas — generated code
references constructors and type names only.

For real verification work, downstream users should swap their
`import Aeneas.Std` against the proper backends/lean/Aeneas library;
this shim exists to validate the emitter pipeline end-to-end.
-/

namespace Aeneas
namespace Std

/-! ## Scalar types -/

/-- Unsigned 8-bit. -/
def U8   : Type := UInt8
/-- Unsigned 16-bit. -/
def U16  : Type := UInt16
/-- Unsigned 32-bit. -/
def U32  : Type := UInt32
/-- Unsigned 64-bit. -/
def U64  : Type := UInt64
/-- Pointer-sized unsigned. -/
def Usize : Type := USize

def I8   : Type := Int8
def I16  : Type := Int16
def I32  : Type := Int32
def I64  : Type := Int64
/-- Pointer-sized signed. (No Int8 alias for ISize in the shim — we
    use `ISize` from core.) -/
def Isize : Type := ISize

-- Re-derive OfNat through the underlying types so literals like
-- `(0 : Std.U32)` resolve to the UInt32 OfNat instance.
instance (n : Nat) [OfNat UInt8 n]  : OfNat U8 n   := inferInstanceAs (OfNat UInt8 n)
instance (n : Nat) [OfNat UInt16 n] : OfNat U16 n  := inferInstanceAs (OfNat UInt16 n)
instance (n : Nat) [OfNat UInt32 n] : OfNat U32 n  := inferInstanceAs (OfNat UInt32 n)
instance (n : Nat) [OfNat UInt64 n] : OfNat U64 n  := inferInstanceAs (OfNat UInt64 n)

-- Re-derive arithmetic instances so the M10.0 emitter's `x + 1` style
-- expressions typecheck against the shim's `Std.U*` aliases. The
-- result type is `Result α` to match the real Aeneas runtime, which
-- treats overflow as a checked failure inside the Result monad. The
-- shim is permissive — every binop succeeds with `.ok` modulo
-- wrapping semantics; the emitter's `do let t ← x + y` and bare-tail
-- `do x + y` shapes both resolve.

/-! ## ControlFlow

The standard Aeneas backend opens `ControlFlow` as part of its
header. The shim exposes it as an empty namespace — the placeholder
emitter never references any of its constructors, but the `open`
line still needs to resolve. -/

namespace ControlFlow end ControlFlow

/-! ## Result monad -/

/-- The kind of failure a fallible Aeneas computation can produce.

    The real runtime distinguishes overflow / out-of-bounds / panic;
    the shim treats them uniformly as a single `panic` constructor —
    enough to make `.ok x1` shaped expressions typecheck. -/
inductive Error
  | panic
  | overflow
  | outOfBounds
  | divisionByZero
  deriving Repr, BEq

/-- Aeneas's pervasive return monad. The emitter wraps every function
    body in `.ok` (forward direction) or `.error` (panic path). -/
inductive Result (α : Type) where
  | ok (value : α)
  | error (e : Error)
  deriving Repr

namespace Result

@[inline] def map (r : Result α) (f : α → β) : Result β :=
  match r with | .ok x => .ok (f x) | .error e => .error e

@[inline] def bind (r : Result α) (k : α → Result β) : Result β :=
  match r with | .ok x => k x | .error e => .error e

instance : Monad Result where
  pure := .ok
  bind := bind

end Result

-- Binop instances that lift the underlying-type operator into the
-- Result monad. Defined here (after `Result`) so the result type is
-- in scope.
@[inline] private def liftRes2 {α β : Type} (op : α → α → β) (a b : α)
    : Result β := .ok (op a b)

instance : HAdd U32 U32 (Result U32) :=
  ⟨liftRes2 (UInt32.add : UInt32 → UInt32 → UInt32)⟩
instance : HSub U32 U32 (Result U32) :=
  ⟨liftRes2 (UInt32.sub : UInt32 → UInt32 → UInt32)⟩
instance : HMul U32 U32 (Result U32) :=
  ⟨liftRes2 (UInt32.mul : UInt32 → UInt32 → UInt32)⟩
instance : HXor U32 U32 (Result U32) :=
  ⟨liftRes2 (UInt32.xor : UInt32 → UInt32 → UInt32)⟩
instance : HAnd U32 U32 (Result U32) :=
  ⟨liftRes2 (UInt32.land : UInt32 → UInt32 → UInt32)⟩
instance : HOr  U32 U32 (Result U32) :=
  ⟨liftRes2 (UInt32.lor : UInt32 → UInt32 → UInt32)⟩
instance : HShiftLeft U32 U32 (Result U32) :=
  ⟨liftRes2 (UInt32.shiftLeft : UInt32 → UInt32 → UInt32)⟩
instance : HShiftRight U32 U32 (Result U32) :=
  ⟨liftRes2 (UInt32.shiftRight : UInt32 → UInt32 → UInt32)⟩

instance : HAdd U64 U64 (Result U64) :=
  ⟨liftRes2 (UInt64.add : UInt64 → UInt64 → UInt64)⟩
instance : HSub U64 U64 (Result U64) :=
  ⟨liftRes2 (UInt64.sub : UInt64 → UInt64 → UInt64)⟩
instance : HMul U64 U64 (Result U64) :=
  ⟨liftRes2 (UInt64.mul : UInt64 → UInt64 → UInt64)⟩

end Std
end Aeneas
