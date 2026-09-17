import Aeneas
open Aeneas Aeneas.Std Result

/-- A hand-written model for `external_names::is_mult`.

    `tests/external-names/external-names.json` maps the Rust function to this
    definition, and the test passes `-extra-includes=ExternalNamesModel` so that
    the generated file imports it. Nothing here belongs to the Core/Std/Alloc
    models which ship with the compiler: that is the point of the test - a list
    of external names may point at definitions of the user's own library. -/
def ExternalNamesModel.isMult (n m : U32) : Result Bool :=
  ok (n.val % m.val == 0)
