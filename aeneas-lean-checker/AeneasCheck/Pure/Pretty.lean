import AeneasCheck.Pure.Syntax

/-!
Pure IR shared helpers — the Lean-emit half of this file was retired
in Phase 2a. What remains are the helpers the Rust-model emit and the
Driver name-rewrite pass both need:
* `IntKind.toRust` — the lowercase Rust spelling (`u32`, `isize`, …).
* `sanitizeCallName` — canonical Charon-path → Lean-friendly name
  rewrite. Driver.lean uses this to detect inherent-impl method /
  field-projection collisions (`Struct.len` vs auto-generated field
  projection) and to key the per-decl pretty-name map; the same
  rewrite is applied at the Rust-emit call site so the model's call
  sites and the model's def names agree.
-/

namespace AeneasCheck.Pure

open AeneasCheck.Raw

def IntKind.toRust : IntKind → String
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
  | .u128 => "u128" | .usize => "usize"
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .i128 => "i128" | .isize => "isize"

/-- Sanitize a Charon-style qualified function name like
    `core::num::{u32}::wrapping_add` into a Lean-valid path
    `core.num.U32.wrapping_add`. Rules:
    * `::` becomes `.`
    * `{…}` brace groups collapse to a single Lean-valid identifier
      derived from their inner text — the last `::`-or-`.`-segment,
      with any `<…>` generic-arg suffix stripped, capitalised when
      it matches a bare integer type (`u32` → `U32`).
    * primitive integer-type segments outside braces are likewise
      capitalised to match the standard Aeneas backend's namespace
      casing.

    Phase 4a-2: brace groups in Charon paths frequently span more than
    one `::`-segment (`constants::{constants::Wrap<T>}::new`,
    `core::clone::impls::{core::clone::Clone for bool}::clone`). The
    previous per-segment `stripBraces` only handled the degenerate
    one-segment case (`{u32}`) and left mid-path braces decorated
    (`constants.{constants.Wrap<T>}.new`), producing names Lean rejects.
    Walk the input balancing `{` / `}` like `RustEmit.sanitizeRustPath`
    does, so the brace-inner text can be processed as a unit.

    Phase 2a: this lives on after the Lean-emit retirement because
    `Driver.lean` uses it to canonicalise decl names for the inherent-
    impl-vs-field-projection collision check; the Rust-emit side
    routes through `RustEmit.sanitizeRustPath` / `rustifyPath`, but
    the two helpers walk the same brace-balanced shape so the
    canonical names line up. -/
def sanitizeCallName (n : String) : String := Id.run do
  let bareInts :=
    ["u8","u16","u32","u64","u128","usize",
     "i8","i16","i32","i64","i128","isize"]
  -- Cluster-A follow-up: Charon's builtin-intercept calls carry a
  -- leading `@` (e.g. `@ArrayIndexShared`). Some are special-cased by
  -- the Forward translator (`@ArrayIndexMut`, `@SliceIndexShared`,
  -- `@SliceIndexMut`); the rest fall through to the generic call
  -- machinery and reach the emitter with `@` still in the name. Lean
  -- treats `@Foo` as the explicit-args form of `Foo`, which mis-binds
  -- the first arg to `Foo`'s leading implicit. Strip the `@` so the
  -- shim's top-level `abbrev`s (with their implicit type/const-generic
  -- binders) auto-elaborate from the explicit arg's type.
  --
  -- Step 7 (`use_v_arity`) intentionally prefixes IN-CRATE generic
  -- global calls with `@` so the implicit `{T : Type}` slot is filled
  -- explicitly from the call's type arg (`(@constants.V.LEN T N)`).
  -- Distinguish: builtin intercepts have a SINGLE name segment
  -- (`@ArrayIndexShared`); in-crate calls carry `::` or `.` (the
  -- crate-qualified path). Only strip in the single-segment case.
  let n :=
    if n.startsWith "@" ∧ ¬ (n.contains '.' ∨ n.contains ':') then
      (n.drop 1).toString
    else n
  -- Fast path: no brace decoration, keep the legacy per-segment shape
  -- so existing fixtures remain byte-identical.
  if !n.contains '{' then
    let parts := (n.splitOn "::").map fun p =>
      if bareInts.contains p then p.capitalize else p
    return String.intercalate "." parts
  -- Split into balanced top-level chunks of "outside" text vs `{…}`
  -- groups. Mirrors `RustEmit.sanitizeRustPath`'s walker.
  let cs := n.toList
  let mut chunks : Array (Bool × String) := #[]  -- (isBrace, text)
  let mut buf : String := ""
  let mut depth : Nat := 0
  for c in cs do
    if c == '{' then
      if depth == 0 then
        if !buf.isEmpty then chunks := chunks.push (false, buf)
        buf := ""
      else
        buf := buf.push c
      depth := depth + 1
    else if c == '}' then
      depth := depth - 1
      if depth == 0 then
        chunks := chunks.push (true, buf)
        buf := ""
      else
        buf := buf.push c
    else
      buf := buf.push c
  if !buf.isEmpty then chunks := chunks.push (false, buf)
  -- Reduce a brace-inner string to a single Lean identifier: prefer
  -- the segment after the last ` for ` (Charon's
  -- `{Trait for Self}::method` shape), then drop everything before
  -- the last `::` or `.`, then drop any `<…>` generic-arg suffix,
  -- then capitalise if it matches a bare integer type.
  let pickType (inner : String) : String :=
    let after := match inner.splitOn " for " with
      | [] => inner
      | xs => xs.getLast!
    -- Normalise the separator so an inner that uses `.` (`Wrap<T>`
    -- when the call-name was already lowered) and one that uses
    -- `::` (`constants::Wrap<T>` straight from Charon) both reduce
    -- the same way.
    let normalized := (after.trimAscii.toString).replace "::" "."
    -- Cluster-A follow-up: Rust slice / array brace-inners.
    -- `{[T]}` → `Slice`, `{[T; N]}` → `Array`. Mainline aeneas's
    -- backend reduces these forms to the runtime-shim's `Slice` /
    -- `Array` type. Stripping happens before the lastSeg/split-on-`<`
    -- pass so the `[T@0]` / `[T@0; C@0]` forms (Charon's region-
    -- tagged variables) reduce the same way.
    let stripped := normalized.trimAscii.toString
    if stripped.startsWith "[" ∧ stripped.endsWith "]" then
      if stripped.contains ';' then "Array" else "Slice"
    else
    let lastSeg := (normalized.splitOn ".").getLast?.getD normalized
    let cleanSeg := (lastSeg.splitOn "<").headD lastSeg
    let trimmed := cleanSeg.trimAscii.toString
    if bareInts.contains trimmed then trimmed.capitalize else trimmed
  let mut out : String := ""
  for (isBrace, txt) in chunks do
    if isBrace then
      out := out ++ pickType txt
    else
      let parts := (txt.splitOn "::").map fun p =>
        if bareInts.contains p then p.capitalize else p
      out := out ++ String.intercalate "." parts
  return out

end AeneasCheck.Pure
