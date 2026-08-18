module
public import Lean
public meta import Aeneas.Extract.Extract
public import Aeneas.Std.Primitives
public section

namespace Aeneas

namespace Std

open RustM

@[rust_trait "core::ops::index::Index"]
structure core.ops.index.Index (Self Idx Output : Type _) where
  index : Self → Idx → RustM Output

@[rust_trait "core::ops::index::IndexMut" (parentClauses := ["indexInst"])]
structure core.ops.index.IndexMut (Self Idx Output : Type _) where
  indexInst : Index Self Idx Output
  index_mut : Self → Idx → RustM (Output × (Output → Self))

@[rust_trait "core::ops::deref::Deref"]
structure core.ops.deref.Deref (Self Target : Type _) where
  deref : Self → RustM Target

@[rust_trait "core::ops::deref::DerefMut" (parentClauses := ["derefInst"])]
structure core.ops.deref.DerefMut (Self Target : Type _) where
  derefInst : Deref Self Target
  deref_mut : Self → RustM (Target × (Target → Self))

@[rust_trait "core::ops::bit::BitAnd"]
structure core.ops.bit.BitAnd (Self : Type _) (Rhs : Type _) (Self_Output : Type _) where
  bitand : Self → Rhs → RustM Self_Output

@[rust_trait "core::ops::drop::Drop"]
structure core.ops.drop.Drop (Self : Type _) where
  drop : Self → RustM Self

@[expose, rust_fun "core::ops::drop::Drop::drop"]
def core.ops.drop.Drop.drop.default {Self : Type _}
    (DropInst : core.ops.drop.Drop Self) : Self → RustM Self :=
  fun s => DropInst.drop s

@[rust_trait "core::ops::function::FnOnce"]
structure core.ops.function.FnOnce (Self : Type u) (Args : Type v) (Output : Type w) where
  call_once : Self → Args → RustM Output

@[rust_trait "core::ops::function::FnMut" (parentClauses := ["FnOnceInst"])]
structure core.ops.function.FnMut (Self : Type u) (Args : Type v) (Output : Type w) where
  FnOnceInst : core.ops.function.FnOnce Self Args Output
  call_mut : Self → Args → RustM (Output × Self)

@[rust_trait "core::ops::function::Fn" (parentClauses := ["FnMutInst"])]
structure core.ops.function.Fn (Self : Type u) (Args : Type v) (Output : Type w) where
  FnMutInst : core.ops.function.FnMut Self Args Output
  call : Self → Args → RustM Output

def BuiltinFnOnce (Inputs : Type u) (Outputs : Type v) : core.ops.function.FnOnce (Inputs → RustM Outputs) Inputs Outputs := {
  call_once f x := f x
}

def BuiltinFnMut (Inputs : Type u) (Outputs : Type v) : core.ops.function.FnMut (Inputs → RustM Outputs) Inputs Outputs := {
  FnOnceInst := BuiltinFnOnce Inputs Outputs
  call_mut f x := do
    bind (f x) λ v =>
    ok (v, f)
}

def BuiltinFn (Inputs : Type u) (Outputs : Type v) : core.ops.function.Fn (Inputs → RustM Outputs) Inputs Outputs := {
  FnMutInst := BuiltinFnMut Inputs Outputs
  call f x := f x
}

@[rust_trait "core::ops::try_trait::FromResidual"]
structure core.ops.try_trait.FromResidual (Self : Type u) (R : Type v) where
  from_residual : R → RustM Self

@[rust_type "core::ops::control_flow::ControlFlow"]
inductive core.ops.control_flow.ControlFlow (B : Type _) (C : Type _) where
| Continue : C → core.ops.control_flow.ControlFlow B C
| Break : B → core.ops.control_flow.ControlFlow B C

@[rust_trait "core::ops::try_trait::Try" (parentClauses := ["FromResidualInst"])]
structure core.ops.try_trait.Try (Self Output Residual : Type _) where
  FromResidualInst : core.ops.try_trait.FromResidual Self Residual
  from_output : Output → RustM Self
  branch : Self → RustM (core.ops.control_flow.ControlFlow Residual Output)

@[rust_trait "core::ops::try_trait::Residual" (parentClauses := ["TryInst"])]
structure core.ops.try_trait.Residual (Self O TryType: Type _) where
  TryInst : core.ops.try_trait.Try TryType O Self

namespace Std

namespace Aeneas
