import AeneasCheck.Pure.Pretty
import AeneasCheck.Translate.Driver

/-!
Rust source-code backend.

Each Pure decl `def f (x1 .. xn : T) : Result T := body` becomes a
Rust fn `pub fn f_model(x1 .. xn : T) -> T { … }` whose body is a
direct transliteration of the Pure expression.

Functions that originally took `&mut T` references in Rust are
emitted as functions that *take and return* `T` — this is the
differential-test convention: the model returns the updated value so
proptest can compare it to running the original function on a fresh
local.
-/

open AeneasCheck Raw Pure Translate

namespace AeneasCheck.Pure

partial def PTy.toRust : PTy → String
  | .unit => "()"
  | .lit (.int k) => IntKind.toRust k
  | .lit .bool => "bool"
  | .lit .char => "char"
  | .lit (.float _) => "f64"
  | .adt name args =>
    if args.isEmpty then name
    else s!"{name}<{String.intercalate ", " (args.toList.map PTy.toRust)}>"
  | .tuple args =>
    "(" ++ String.intercalate ", " (args.toList.map PTy.toRust) ++ ")"
  | .result inner => inner.toRust  -- M8: drop the Result wrapper
  -- M12.2a-2: render as `Box<dyn Fn(α) -> β>` so the differential
  -- test harness has *some* type to hang the closure off. Backward
  -- closures don't naturally exist in the original Rust source —
  -- the Rust model collapses them into a flat tuple-returning fn
  -- anyway — so this is a best-effort fallback.
  | .arrow dom cod => s!"Box<dyn Fn({dom.toRust}) -> {cod.toRust}>"
  -- M9.5c: a fixed-length array `[T; N]`. Rust's native array
  -- notation matches one-for-one; the differential harness can
  -- consume / produce these directly.
  | .array elem length => s!"[{elem.toRust}; {length}]"
  -- M9.5g: a runtime-sized slice. Rust has no naked-value slice
  -- type (it's always behind a reference), but for the
  -- differential-test convention we lower the borrow into an owned
  -- `Vec<T>` — the model returns the updated buffer in the same way
  -- it does for `&mut [T; N]` (see `.array` above). This keeps the
  -- harness's `T_in == T_out` invariant intact.
  | .slice elem => s!"Vec<{elem.toRust}>"
  -- M9.5i: a type-variable reference. Rust uses the same letter
  -- convention as the original source; the differential harness's
  -- generated `fn _model<T>` carries the binder so the inner `T`
  -- needs no further qualification.
  | .tyVar name => name

def litToRust : Lit → String
  | .scalar k v => s!"{v}{IntKind.toRust k}"
  | .bool b => toString b
  | .char c => s!"'\\u\{{c}}'"
  | .str s => s!"\"{s}\""
  | .byteStr _ => "b\"<bytestr>\""

/-- Rust-side operator for a binop `App` head. `Some _` means render
    the application as `lhs <op> rhs`; `none` falls through to a
    function-call form (used for wrapping/checked variants). -/
def binopRustOp : String → Option String
  | "Add" => some "+"
  | "Sub" => some "-"
  | "Mul" => some "*"
  | "Div" => some "/"
  | "Rem" => some "%"
  | "BitXor" => some "^"
  | "BitAnd" => some "&"
  | "BitOr"  => some "|"
  | "Shl" => some "<<"
  | "Shr" => some ">>"
  | "Eq" => some "=="
  | "Ne" => some "!="
  | "Lt" => some "<"
  | "Le" => some "<="
  | "Gt" => some ">"
  | "Ge" => some ">="
  | _ => none

/-- For wrapping / checked ops, render as `lhs.wrapping_add(rhs)`. -/
def binopRustMethod : String → Option String
  | "AddWrap" => some "wrapping_add"
  | "SubWrap" => some "wrapping_sub"
  | "MulWrap" => some "wrapping_mul"
  | "AddChecked" => some "checked_add"
  | "SubChecked" => some "checked_sub"
  | "MulChecked" => some "checked_mul"
  | _ => none

/-- Rewrite a Charon-style qualified name like
    `core::num::{u32}::wrapping_add` or
    `core::clone::impls::{core::clone::Clone for bool}::clone` into a
    parseable Rust path. Each `{…}` brace group is replaced by a
    "type" hint extracted from inside it (text after the last ` for `
    if present, else the inner stripped of any `::` prefix). The path
    prefix before the brace group is dropped, since Rust addresses
    primitives like `u32::wrapping_add` without a `core::num::` prefix.
    If no braces are present, the input is returned unchanged. -/
def sanitizeRustPath (n : String) : String := Id.run do
  if !n.contains '{' then return n
  let cs := n.toList
  -- Split into balanced top-level chunks of "outside" text vs "{…}" groups.
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
  -- Extract a "type" from a brace-group's inner text: prefer the
  -- segment after the last ` for `, else the last `::`-segment.
  let pickType (inner : String) : String :=
    let after :=
      match inner.splitOn " for " with
      | [] => inner
      | xs => xs.getLast!
    -- Trim and drop trailing `>` from generic args we don't model.
    let after := after.trimAscii.toString
    -- Take last `::`-segment.
    match (after.splitOn "::").getLast? with
    | some s => s
    | none => after
  -- Walk chunks; when we see a brace group, drop trailing `::` from
  -- the previously-emitted outside text (so `core::num::{u32}::foo`
  -- becomes `u32::foo`, not `core::num::u32::foo`).
  let mut out : String := ""
  for (isBrace, txt) in chunks do
    if isBrace then
      -- Strip a trailing `::` from `out`, plus the entire path prefix
      -- before the brace group. We choose the simpler "drop prefix"
      -- rule by resetting `out` to empty whenever we see a brace.
      out := pickType txt
    else
      out := out ++ txt
  return out

partial def PExpr.toRust : PExpr → String
  | .var name => name
  | .lit l => litToRust l
  | .app head args =>
    match binopRustOp head, binopRustMethod head, args.toList with
    | some op, _, [l, r] =>
      "(" ++ l.toRust ++ " " ++ op ++ " " ++ r.toRust ++ ")"
    | _, some m, [l, r] =>
      l.toRust ++ "." ++ m ++ "(" ++ r.toRust ++ ")"
    | _, _, _ =>
      -- Strip Charon-style `{…}` brace-decorated segments (impl-for
      -- and type-instantiation markers) which aren't valid Rust.
      let head := sanitizeRustPath head
      if args.isEmpty then head
      else s!"{head}(" ++ String.intercalate ", " (args.toList.map PExpr.toRust) ++ ")"
  | .letIn name _ e1 e2 =>
    s!"let {name} = {e1.toRust};\n    {e2.toRust}"
  -- M8 drops the .ok wrapper: the Rust model returns the value directly.
  | .ok inner => inner.toRust
  | .ifThenElse c t e =>
    "if " ++ c.toRust ++ " { " ++ t.toRust ++ " } else { " ++ e.toRust ++ " }"
  -- M12.2a-2: best-effort transliteration for tuple / lambda / let
  -- shapes that arrive via the backward-function machinery. The Rust
  -- differential model is a coarse approximation here; the real
  -- model swap is tracked in M13.
  | .tuple args =>
    match args.toList with
    | [e] => e.toRust
    | _ => "(" ++ String.intercalate ", " (args.toList.map PExpr.toRust) ++ ")"
  | .lam params body =>
    let names := String.intercalate ", " (params.toList.map (·.1))
    s!"Box::new(move |{names}| {body.toRust})"
  | .letPure name _ e1 e2 =>
    s!"let {name} = {e1.toRust};\n    {e2.toRust}"
  | .letPat pat _ e1 e2 =>
    let pats := String.intercalate ", " pat.toList
    s!"let ({pats}) = {e1.toRust};\n    {e2.toRust}"
  | .structUpdate base field value adtName =>
    -- Phase 1C: when the PExpr carries the struct's bare Lean name,
    -- emit Rust's native struct-update syntax `Foo { field: value, ..base }`.
    -- Otherwise fall back to the historic `with_<field>(base, value)`
    -- placeholder — kept so test fixtures or proof paths that
    -- synthesise a PExpr without the ADT name still produce *some*
    -- output (the differential test will then fail to parse, but the
    -- rest of the pipeline keeps working).
    match adtName with
    | some name =>
      s!"{name} \{ {field}: {value.toRust}, ..{base.toRust} }"
    | none =>
      s!"with_{field}({base.toRust}, {value.toRust})"
  | .fieldAccess base field =>
    -- M9.5n: Rust uses the same dot-notation as Lean for struct
    -- field reads. We pass it through verbatim.
    s!"{base.toRust}.{field}"
  | .recordLit fields adtName =>
    -- Phase 1C: when the PExpr carries the struct's bare Lean name,
    -- emit Rust's struct-literal syntax `Foo { x: e1, y: e2 }`. The
    -- field names already match the original Rust struct's surface
    -- names (the OCaml cert generator resolves `field_name` or
    -- falls back to `fieldK` for tuple-style structs). When the name
    -- is absent (legacy / synthesised PExpr), fall back to the
    -- historic `record_lit { … }` placeholder so the rest of the
    -- pipeline keeps emitting something rather than panicking.
    let body := String.intercalate ", "
      (fields.toList.map fun (n, v) => s!"{n}: {v.toRust}")
    match adtName with
    | some name => s!"{name} \{ {body} }"
    | none => s!"record_lit \{ {body} }"
  | .matchE scrutinee arms =>
    -- M9.5d / M9.5e: Rust's `match` syntax differs only in arm
    -- separator (comma) and ctor path. The Pure IR's ctor strings
    -- already carry the qualified form (e.g. `Sign.Pos`); we
    -- rewrite the dot to Rust's `::` so the differential model
    -- compiles. M9.5e: payload binders are surfaced as a Rust
    -- tuple-pattern after the ctor (`NumOrZero::Num(n) => …`).
    let armS := arms.toList.map fun (ctor, binders, body) =>
      let ctor := ctor.replace "." "::"
      let pat :=
        if binders.isEmpty then ctor
        else ctor ++ "(" ++ String.intercalate ", " binders.toList ++ ")"
      s!"{pat} => {body.toRust},"
    s!"match {scrutinee.toRust} \{ {String.intercalate " " armS} }"

end AeneasCheck.Pure

namespace AeneasCheck.Backends

open AeneasCheck Pure

def sanitizeRustName (n : String) : String :=
  -- Lean's `::` and `.` are not valid in Rust function names. Take the
  -- last segment and append `_model` so we don't collide with the
  -- original Rust function.
  let segs := (n.replace "::" ".").splitOn "."
  let basename := segs.getLast?.getD n
  basename ++ "_model"

def emitDeclRust (d : Decl) : String :=
  let params := String.intercalate ", "
    (d.params.toList.map fun p => s!"{p.name}: {p.ty.toRust}")
  let retTy := d.retTy.toRust
  let body := d.body.toRust
  let fnName := sanitizeRustName d.name
  "pub fn " ++ fnName ++ "(" ++ params ++ ") -> " ++ retTy ++ " {\n    " ++
    body ++ "\n}\n"

def emitTranslatedCrateRust (crateName : String) (tc : TranslatedCrate) : String :=
  -- Decls are emitted without an inner `#![allow(...)]` so the file
  -- can be `include!`'d from a lib root that already sets the
  -- relevant lints crate-wide.
  let header :=
    s!"// THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS-LEAN-CHECKER\n" ++
    s!"// Crate: {crateName}\n\n"
  header ++ String.intercalate "\n" (tc.decls.toList.map emitDeclRust)

end AeneasCheck.Backends
