import AeneasCheck.Translate.Forward

/-!
End-to-end pipeline:

    parse  cert.json  →  Raw.CrateCert
    typecheck         →  (errors)
    replay  trace     →  CheckedTrace
    translate         →  Pure.Decl
    emit              →  Lean source / Rust source (separate modules)
-/

namespace AeneasCheck.Translate

open AeneasCheck Raw Pure LLBCSharp

structure TranslatedCrate where
  decls : Array Decl
  deriving Inhabited

/-- Translate a whole crate cert. -/
def translateCrate (cc : CrateCert) : Except String TranslatedCrate := do
  let traces ← replayCrate cc
  return { decls := traces.map translateFun }

end AeneasCheck.Translate
