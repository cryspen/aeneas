import AeneasCheck.Pure.Syntax

/-!
Pure IR pretty-printer (Lean-style syntax, used by both LeanEmit and
diagnostic output).
-/

namespace AeneasCheck.Pure

open AeneasCheck.Raw

def IntKind.toLean : IntKind → String
  | .u8 => "U8" | .u16 => "U16" | .u32 => "U32" | .u64 => "U64"
  | .u128 => "U128" | .usize => "Usize"
  | .i8 => "I8" | .i16 => "I16" | .i32 => "I32" | .i64 => "I64"
  | .i128 => "I128" | .isize => "Isize"

def IntKind.toRust : IntKind → String
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"
  | .u128 => "u128" | .usize => "usize"
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .i128 => "i128" | .isize => "isize"

partial def PTy.toLean : PTy → String
  | .unit => "Unit"
  | .lit (.int k) => s!"Std.{IntKind.toLean k}"
  | .lit .bool => "Bool"
  | .lit .char => "Char"
  | .lit (.float _) => "Float"
  | .adt name args =>
    if args.isEmpty then name
    else s!"({name} {String.intercalate " " (args.toList.map PTy.toLean)})"
  | .tuple args =>
    "(" ++ String.intercalate " × " (args.toList.map PTy.toLean) ++ ")"
  -- The standard Aeneas Lean backend's `open Aeneas Aeneas.Std`
  -- header makes `Result` unqualified, so we drop the `Std.` prefix
  -- here for byte-identity with `aeneas -backend lean`.
  | .result inner => s!"Result {inner.toLean}"

def litToLean : Lit → String
  | .scalar k v =>
    s!"({v} : Std.{IntKind.toLean k})"
  | .bool b => toString b
  | .char c => s!"⟨{c}⟩"
  | .str s => s!"\"{s}\""
  | .byteStr _ => "<bytestr>"

/-- Expression form used inside a `do`-block: tail `.ok` becomes a
    bare `ok …` (Result is opened), let-bindings become monadic
    `let … ← …`. -/
partial def PExpr.toLeanDo : PExpr → String
  | .var name => name
  | .lit l => litToLean l
  | .app head args =>
    if args.isEmpty then head
    else "(" ++ head ++ " " ++ String.intercalate " " (args.toList.map PExpr.toLeanDo) ++ ")"
  | .letIn name _ e1 e2 =>
    -- Inner expressions in a monadic let bind a Result-valued
    -- computation; emit a `let … ←` form. Tail position is e2.
    s!"let {name} ← {e1.toLeanDo}\n  {e2.toLeanDo}"
  | .ok inner =>
    let s := match inner with
      | .var _ | .lit _ => PExpr.toLeanDo inner
      | _ => "(" ++ PExpr.toLeanDo inner ++ ")"
    s!"ok {s}"

/-- Non-monadic rendering. Retained for diagnostics; the Lean backend
    uses `toLeanDo` exclusively. -/
partial def PExpr.toLean : PExpr → String
  | .var name => name
  | .lit l => litToLean l
  | .app head args =>
    if args.isEmpty then head
    else "(" ++ head ++ " " ++ String.intercalate " " (args.toList.map PExpr.toLean) ++ ")"
  | .letIn name _ e1 e2 =>
    s!"let {name} := {e1.toLean}\n  {e2.toLean}"
  | .ok inner => s!".ok {inner.toLean}"

/-- Build the `/-- [crate::fn]: ... -/` docstring lines that precede a
    `def`. Empty when no `sourceSpan` is attached. -/
def Decl.docComment (d : Decl) : String :=
  match d.sourceSpan with
  | none => ""
  | some sp =>
    let loc :=
      s!"{sp.begLine}:{sp.begCol}-{sp.endLine}:{sp.endCol}"
    s!"/-- [{d.qualifiedName}]:\n    Source: '{sp.file}', lines {loc} -/\n"

/-- Render the Lean `def …` for `d`, with monadic body. The signature
    matches the standard Aeneas backend's output (Result, do-block). -/
def Decl.toLean (d : Decl) : String :=
  let params := String.intercalate " "
    (d.params.toList.map fun p => s!"({p.name} : {p.ty.toLean})")
  d.docComment ++
  s!"def {d.name} {params} : Result {d.retTy.toLean} := do\n  {d.body.toLeanDo}"

end AeneasCheck.Pure
