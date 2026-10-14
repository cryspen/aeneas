-- Stubs for the `Lawful` structures of hax's core models (`CoreModels`), which
-- the generated specs refer to (e.g. the `Lawful` field of a `Clone` parent).
-- Kept here until the CoreModels library provides them. Imported into every
-- generated file through Aeneas' `-extra-includes` (see `tests/hax/hax.toml`),
-- so it must not import any `HaxTests` module.
import Aeneas
import CoreModels
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace CoreModels

-- The actual fields are to be decided with the library.
structure core.clone.Clone.Lawful (Self : Type)
  (CloneInst : core.clone.Clone Self) : Prop where

theorem core.U32.Insts.CoreCloneClone.Lawful :
  core.clone.Clone.Lawful Std.U32 core.U32.Insts.CoreCloneClone := ⟨⟩

structure core.default.Default.Lawful (Self : Type)
  (DefaultInst : core.default.Default Self) : Prop where

-- `Copy` has no method; its parent `Clone` would give a
-- `corecloneCloneInstLawful` field, omitted like the fields of `Clone.Lawful`.
structure core.marker.Copy.Lawful (Self : Type)
  (CopyInst : core.marker.Copy Self) : Prop where

-- The closure traits, implemented by the closures of hax decorations. The
-- parent fields (`FnOnceInstLawful`, `FnMutInstLawful`) are omitted like that
-- of `Copy.Lawful`.
structure core.ops.function.FnOnce.Lawful (Self : Type) (Args : Type)
  (Self_Output : Type)
  (FnOnceInst : core.ops.function.FnOnce Self Args Self_Output) : Prop where

structure core.ops.function.FnMut.Lawful (Self : Type) (Args : Type)
  (Self_Clause0_Output : Type)
  (FnMutInst : core.ops.function.FnMut Self Args Self_Clause0_Output) :
  Prop where

structure core.ops.function.Fn.Lawful (Self : Type) (Args : Type)
  (Self_Clause0_Output : Type)
  (FnInst : core.ops.function.Fn Self Args Self_Clause0_Output) : Prop where

end CoreModels
