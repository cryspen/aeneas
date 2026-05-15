import Lake
open Lake DSL

/-!
The Aeneas Lean checker.

M4-M6: this lib only depends on Lean core (for `Lean.Json`). It validates
the OCaml-side cert format and the LLBC# trace replay; it does not yet
emit Lean source.

M7+ will add a dependency on `../backends/lean/` so the emitted Lean
output can reference `Aeneas.Std.U32`, `Result`, etc. unchanged. The
dependency is held off until then to keep the M4/M5/M6 build cycle
mathlib-free (faster CI, faster local iteration).
-/

package «aeneas-lean-checker» where

@[default_target] lean_lib «AeneasCheck» where

lean_exe «aeneas-check» where
  root := `AeneasCheck.Cli
  supportInterpreter := true

/-- Minimal `Aeneas.Std` shim: just enough surface for the M7
    emitter's output to typecheck without pulling in the
    mathlib-backed real runtime in `backends/lean/`. See
    `RuntimeShim/Aeneas/Std.lean` for the design rationale. -/
lean_lib «RuntimeShim» where
  srcDir := "RuntimeShim"
  roots := #[`Aeneas, `Aeneas.Std]

/-- Compiles the M7-generated Lean source against `RuntimeShim`. The
    file at `tests/Generated/Incr.lean` is produced by running
    `aeneas-check --out tests/Generated/Incr.lean` (see
    `scripts/check-vertical-slice.sh`).

    M9.5c: `Generated.Reborrows` covers the cert-translated
    `set_fst` / `set_idx` / `reborrow_chain` from `tests/src/reborrows.rs`.
    The RuntimeShim grew `Aeneas.Std.Array` + `Array.update` + the
    `#usize` const-generic macro to make the shape compile.

    M9.5d: `Generated.EnumsBasic` (C-style enum + match arms).

    M9.5e: `Generated.EnumsPayload` (payload-bearing enum + match
    with binder extraction). Inductives are built-in so the
    RuntimeShim needs no additional surface.

    M9.5g: `Generated.SlicesBasic` (`&[T]` immutable read +
    `&mut [T]` write). RuntimeShim grew `Aeneas.Std.Slice` +
    `Slice.index_usize` + `Slice.update` for the emitted body to
    typecheck.

    M9.5h: `Generated.Bitwise` (pure bit ops + monadic shifts on
    `U32` / `I32`). RuntimeShim dropped the `Result`-typed `HXor` /
    `HAnd` / `HOr` overrides on `U32` (the standard backend treats
    bit ops as pure functions, so `ok (x1 ^^^ x2)` resolves the
    operand-type-typed built-in `HXor UInt32 UInt32 UInt32` via the
    `U32 := UInt32` reducible alias) and added `HShiftLeft` /
    `HShiftRight` instances over `U32 × Usize` and `I32 × Isize` to
    cover `a >>> 16#usize` and `a >>> 16#isize` shapes.

    M9.5i: `Generated.GenericsBasic` (generic enum + generic
    function on `MyOption<T>`). No RuntimeShim work needed —
    Lean's `Type` universe is a primitive and `inductive Foo
    (T : Type) where | …` doesn't require any Aeneas.Std support
    beyond what M9.5d/e already provide.

    M9.5j: `Generated.ListBasic` (non-generic recursive enum
    `List = Cons (U32, Box<List>) | Nil` + recursive walk
    `list_len`). The emitted def carries the standard backend's
    `partial_fixpoint` trailer; the inductive's recursive payload
    field appears as a bare `List` because Charon strips `Box<T>`
    at the LLBC layer (boxes are semantically transparent in pure
    functional code), so no Box-specific surface is needed in the
    RuntimeShim. -/
lean_lib «GeneratedTests» where
  srcDir := "tests"
  roots := #[`Generated.Incr, `Generated.CompareSimple, `Generated.Calls,
             `Generated.LoopsSimple, `Generated.Reborrows,
             `Generated.EnumsBasic, `Generated.EnumsPayload,
             `Generated.SlicesBasic, `Generated.Bitwise,
             `Generated.GenericsBasic, `Generated.ListBasic]
