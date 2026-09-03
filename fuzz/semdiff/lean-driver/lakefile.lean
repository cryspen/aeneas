import Lake
open Lake DSL

-- Depends on the Aeneas Lean backend (which itself pulls in mathlib).
-- Path is relative to this lakefile: fuzz/semdiff/lean-driver -> repo root.
require aeneas from "../../../backends/lean"

package «semdiff-driver» {}

-- A single library holding whatever we drop into ./Driver.lean.
-- For the semantic-differential oracle we normally do NOT `lake build` this
-- library per crate; instead we run `lake env lean <file>` on a generated file.
-- This target exists only so `lake build` warms up the Aeneas + mathlib deps.
@[default_target] lean_lib Driver {
  globs := #[.one `Driver]
}
