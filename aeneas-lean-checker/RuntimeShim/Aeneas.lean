import Lean.Data.Options
import «Aeneas».Std

/-!
Top-level re-export so generated Lean's `import Aeneas` and
`open Aeneas (Std)` resolve.

Also registers the linter options that the standard Aeneas backend's
header sets via `set_option linter.dupNamespace false` (etc.). Without
mathlib these options are not declared, so the standalone shim build
needs its own dummy registrations to make the header parse.
-/

register_option linter.dupNamespace : Bool := {
  defValue := false
  descr := "Mathlib `dupNamespace` linter — stubbed in the aeneas-lean-checker shim."
}

register_option linter.hashCommand : Bool := {
  defValue := false
  descr := "Mathlib `hashCommand` linter — stubbed in the aeneas-lean-checker shim."
}
