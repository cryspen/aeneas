import Aeneas

/-!
Shared utilities for the Lean-side differential runners.

We do not rely on the auto-derived `Repr` for `Result α` because the
Rust-side oracle prints things in a fixed, language-neutral shape.
Every runner formats one line per test vector with `mkLine`; the
Rust runner's `format_line` produces the byte-identical string.

Line shape:  `<fixture>::<fn>(<arg>,<arg>,...) = <output>`
- `<output>` is `ok <decimal>` for `Result.ok v`, or `err <kind>`
  for `Result.error e` (kinds: overflow, panic, oob, divzero), or
  `div` for the nontermination bottom.
- Numeric args are printed as decimal of their *unsigned* bit
  pattern for `U*` types, and the standard signed decimal for `I*`.
-/

open Aeneas Aeneas.Std

namespace LeanDiff

/-- How to print one `Result` of a primitive scalar. We deliberately
    print the *byte-pattern* (unsigned/raw signed) for byte-stable
    cross-language comparison. -/
class Show1 (α : Type) where
  toLine : α → String

instance : Show1 UInt32 where toLine x := toString x.toNat
instance : Show1 UInt64 where toLine x := toString x.toNat
instance : Show1 USize  where toLine x := toString x.toNat
instance : Show1 Int32  where toLine x := toString x.toInt
instance : Show1 Int64  where toLine x := toString x.toInt

/-- The shim's `Std.U32` is reducibly equal to `UInt32`; instances
    above are picked up directly. The explicit aliases here just
    document that. -/
example : Show1 Std.U32 := inferInstance
example : Show1 Std.I32 := inferInstance

def fmtErr (e : Error) : String :=
  match e with
  | .panic          => "panic"
  | .overflow       => "overflow"
  | .outOfBounds    => "oob"
  | .divisionByZero => "divzero"

def fmtResult {α : Type} [Show1 α] (r : Result α) : String :=
  match r with
  | .ok v    => "ok " ++ Show1.toLine v
  | .error e => "err " ++ fmtErr e
  | .div     => "div"

def mkLine {α : Type} [Show1 α]
    (fixture : String) (fn : String) (args : List String) (r : Result α) : String :=
  fixture ++ "::" ++ fn ++ "(" ++ String.intercalate "," args ++ ") = " ++ fmtResult r

/-- Variant for tuple-returning Result. -/
def fmtPairU32 (r : Result (Std.U32 × Std.U32)) : String :=
  match r with
  | .ok (a, b) => "ok " ++ toString a.toNat ++ "," ++ toString b.toNat
  | .error e   => "err " ++ fmtErr e
  | .div       => "div"

end LeanDiff
