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
  | .result inner => s!"Std.Result {inner.toLean}"

def litToLean : Lit → String
  | .scalar k v =>
    s!"({v} : Std.{IntKind.toLean k})"
  | .bool b => toString b
  | .char c => s!"⟨{c}⟩"
  | .str s => s!"\"{s}\""
  | .byteStr _ => "<bytestr>"

partial def PExpr.toLean : PExpr → String
  | .var name => name
  | .lit l => litToLean l
  | .app head args =>
    if args.isEmpty then head
    else "(" ++ head ++ " " ++ String.intercalate " " (args.toList.map PExpr.toLean) ++ ")"
  | .letIn name _ e1 e2 =>
    s!"let {name} := {e1.toLean}\n  {e2.toLean}"
  | .ok inner => s!".ok {inner.toLean}"

def Decl.toLean (d : Decl) : String :=
  let params := String.intercalate " "
    (d.params.toList.map fun p => s!"({p.name} : {p.ty.toLean})")
  s!"def {d.name} {params} : Std.Result {d.retTy.toLean} :=\n  {d.body.toLean}"

end AeneasCheck.Pure
