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
  | .structUpdate base field value =>
    -- M9.5b: Rust's struct-update syntax is `Name { field: value, ..base }`.
    -- We don't know the struct's name from PExpr alone; the differential
    -- Rust model passes structs through as a coarse approximation. Render
    -- as a function-call-style `with_<field>(base, value)` placeholder so
    -- the M13 model can supply a matching helper. Real ADT support in the
    -- differential model is tracked separately.
    s!"with_{field}({base.toRust}, {value.toRust})"
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
