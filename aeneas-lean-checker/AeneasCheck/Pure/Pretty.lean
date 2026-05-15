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

/-- Map a binop `App` head to its Lean infix operator (or `none` if
    the head should render as a function application). The notations
    match the standard Aeneas backend's output. -/
def binopInfix : String → Option String
  | "Add"       => some "+"
  | "Sub"       => some "-"
  | "Mul"       => some "*"
  | "Div"       => some "/"
  | "Rem"       => some "%"
  | "BitXor"    => some "^^^"
  | "BitAnd"    => some "&&&"
  | "BitOr"     => some "|||"
  | "Shl"       => some "<<<"
  | "Shr"       => some ">>>"
  | "Eq"        => some "="
  | "Ne"        => some "≠"
  | "Lt"        => some "<"
  | "Le"        => some "≤"
  | "Gt"        => some ">"
  | "Ge"        => some "≥"
  | _           => none

/-- Map a wrapping/checked binop head to its qualified-name surface
    form. Returns `none` if `head` is not such an op. -/
def binopWrappingName : String → Option String
  | "AddWrap" => some "wrapping_add"
  | "SubWrap" => some "wrapping_sub"
  | "MulWrap" => some "wrapping_mul"
  | "AddChecked" => some "checked_add"
  | "SubChecked" => some "checked_sub"
  | "MulChecked" => some "checked_mul"
  | _ => none

/-- Sanitize a Charon-style qualified function name like
    `core::num::{u32}::wrapping_add` into a Lean-valid path
    `core.num.U32.wrapping_add`. Rules:
    * `::` becomes `.`
    * `{…}` braces strip to their content
    * primitive integer-type segments `u8` / `u16` / … / `i32` / … are
      capitalised (`u32` → `U32`) to match the standard Aeneas
      backend's namespace casing. -/
def sanitizeCallName (n : String) : String :=
  let bareInts :=
    ["u8","u16","u32","u64","u128","usize",
     "i8","i16","i32","i64","i128","isize"]
  let stripBraces (p : String) : String :=
    if p.startsWith "{" && p.endsWith "}" then
      ((p.drop 1).dropEnd 1).toString
    else p
  let parts := (n.splitOn "::").map fun p =>
    let p := stripBraces p
    if bareInts.contains p then p.capitalize else p
  String.intercalate "." parts

/-- Expression form used inside a `do`-block: tail `.ok` becomes a
    bare `ok …` (Result is opened), let-bindings become monadic
    `let … ← …`, binary operators render with the matching infix or
    a qualified function call. -/
partial def PExpr.toLeanDo : PExpr → String
  | .var name => name
  | .lit l => litToLean l
  | .app head args =>
    match binopInfix head, args.toList with
    | some op, [lhs, rhs] =>
      "(" ++ lhs.toLeanDo ++ " " ++ op ++ " " ++ rhs.toLeanDo ++ ")"
    | _, _ =>
      -- Function-call head: try the wrapping-shortcut map first
      -- (`AddWrap → wrapping_add`), then fall back to sanitising a
      -- Charon-style qualified path (`a::b::{u32}::c → a.b.U32.c`).
      let head :=
        match binopWrappingName head with
        | some w => w
        | none => sanitizeCallName head
      if args.isEmpty then head
      else "(" ++ head ++ " " ++
        String.intercalate " " (args.toList.map PExpr.toLeanDo) ++ ")"
  | .letIn name _ e1 e2 =>
    -- Inner expressions in a monadic let bind a Result-valued
    -- computation; emit a `let … ←` form. Tail position is e2.
    s!"let {name} ← {e1.toLeanDo}\n  {e2.toLeanDo}"
  | .ok inner =>
    let s := match inner with
      | .var _ | .lit _ => PExpr.toLeanDo inner
      | _ => "(" ++ PExpr.toLeanDo inner ++ ")"
    s!"ok {s}"
  | .ifThenElse cond thenE elseE =>
    -- M11.2: standard Aeneas backend's two-line shape for short
    -- branches is `if c then <e1> else <e2>`. We keep that when both
    -- branches are single-line; otherwise unfold into a multi-line
    -- `if c\n  then …\n  else …` form.
    let thenS := thenE.toLeanDo
    let elseS := elseE.toLeanDo
    let isSimple (s : String) : Bool := !s.contains '\n'
    if isSimple thenS && isSimple elseS then
      s!"if {cond.toLeanDo} then {thenS} else {elseS}"
    else
      s!"if {cond.toLeanDo}\n  then {thenS}\n  else {elseS}"

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
  | .ifThenElse c t e =>
    s!"if {c.toLean} then {t.toLean} else {e.toLean}"

/-- Build the `/-- [crate::fn]: ... -/` docstring lines that precede a
    `def`. Empty when no `sourceSpan` is attached. -/
def Decl.docComment (d : Decl) : String :=
  match d.sourceSpan with
  | none => ""
  | some sp =>
    let loc :=
      s!"{sp.begLine}:{sp.begCol}-{sp.endLine}:{sp.endCol}"
    s!"/-- [{d.qualifiedName}]:\n    Source: '{sp.file}', lines {loc} -/\n"

/-- Build the `/- TRANSLATOR NOTE: … -/` block emitted *before*
    `docComment` when the translator attached a `note`. M12.0 uses
    this to flag loop-bearing functions whose body is a sentinel. -/
def Decl.noteBlock (d : Decl) : String :=
  match d.note with
  | none => ""
  | some n => s!"/- TRANSLATOR NOTE: {n} -/\n"

/-- Render the Lean `def …` for `d`, with monadic body. The signature
    matches the standard Aeneas backend's output (Result, do-block). -/
def Decl.toLean (d : Decl) : String :=
  let params := String.intercalate " "
    (d.params.toList.map fun p => s!"({p.name} : {p.ty.toLean})")
  d.noteBlock ++ d.docComment ++
  s!"def {d.name} {params} : Result {d.retTy.toLean} := do\n  {d.body.toLeanDo}"

end AeneasCheck.Pure
