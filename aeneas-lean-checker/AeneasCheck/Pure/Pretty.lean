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
    -- M9.5i: a generic ADT (e.g. `MyOption T`) renders as multiple
    -- tokens without outer parens. Use sites wrap with parens when
    -- the multi-token shape would re-parse incorrectly (the
    -- `Result (...)` guard in [.result], and the `Decl.toLean`
    -- return-type bracketing, both detect a space in the inner
    -- form). Monomorphic ADTs (empty `args`) stay single-token.
    --
    -- M9.5n: each argument that renders to a multi-token form (e.g.
    -- nested `AVLNode T` inside `Option (AVLNode T)`) MUST be
    -- parenthesised, otherwise `Option AVLNode T` re-parses as
    -- `Option` applied to two args. We detect multi-token by the
    -- presence of an internal space and by the form not already
    -- self-parenthesising. Single tokens (`T`, `Std.U32`) stay bare.
    if args.isEmpty then name
    else
      let parenArg (a : PTy) : String :=
        let s := a.toLean
        let selfParen := s.startsWith "("
        if s.contains ' ' ∧ !selfParen then "(" ++ s ++ ")" else s
      s!"{name} {String.intercalate " " (args.toList.map parenArg)}"
  | .tuple args =>
    "(" ++ String.intercalate " × " (args.toList.map PTy.toLean) ++ ")"
  -- The standard Aeneas Lean backend's `open Aeneas Aeneas.Std`
  -- header makes `Result` unqualified, so we drop the `Std.` prefix
  -- here for byte-identity with `aeneas -backend lean`.
  --
  -- M9.5c: a multi-token inner type (an `.array`) needs parens
  -- because Lean's parser would otherwise read
  -- `Result Array Std.U32 4#usize` as `Result` applied to 4
  -- separate args. We add parens when the inner contains a space
  -- *and* doesn't already self-parenthesise (the `.tuple` and
  -- `.arrow` cases above always wrap themselves in `(…)`).
  | .result inner =>
    let s := inner.toLean
    let selfParen := s.startsWith "("
    if s.contains ' ' && !selfParen then s!"Result ({s})" else s!"Result {s}"
  -- M12.2a-2: `α → β`. We always wrap in parens so it can sit safely
  -- inside another application head without re-parsing as multiple
  -- args (`(α → β)` not `α → β`).
  | .arrow dom cod => s!"({dom.toLean} → {cod.toLean})"
  -- M9.5c: a fixed-length array. The standard Aeneas backend emits
  -- `Array <elem> <N>#usize`. Both the element type and the
  -- length-literal are simple-enough tokens that we don't need to
  -- parenthesise the whole thing — at use site it's always preceded
  -- by `:` (param type) or `Result` (return type).
  | .array elem length => s!"Array {elem.toLean} {length}#usize"
  -- M9.5g: a runtime-sized slice. The standard Aeneas backend emits
  -- `Slice <elem>` — no length component. As with `Array`, use-site
  -- parenthesisation is handled by the `Result (...)` guard above
  -- (since `Slice <elem>` is also a multi-token type).
  | .slice elem => s!"Slice {elem.toLean}"
  -- M9.5i: a type-variable reference. Renders as just the parameter
  -- name. Use-site disambiguation: when this is the result type
  -- (`Result T`) or a single-arg ADT (`MyOption T`), the surrounding
  -- printer wraps it (or leaves it bare — `T` is a single token so
  -- no parens needed). When used as a multi-arg ADT's argument,
  -- single-letter type-var names stay as single tokens (Greek alpha
  -- would too); the catch-all branches above are the ones that
  -- require parens.
  | .tyVar name => name

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

/-- M12.1: a sub-expression used as a function-application argument
    needs to render with surrounding parens when its Lean form would
    otherwise be parsed as a multi-token construct (lambda, if/else,
    let, …). We pre-parenthesise such forms so `app head [arg1, …]`
    can space-join its args safely. -/
private partial def parenIfNeeded (s : String) (e : PExpr) : String :=
  match e with
  | .lam _ _ | .ifThenElse _ _ _ | .letIn _ _ _ _
  | .letPure _ _ _ _ | .letPat _ _ _ _
  -- M9.5b: a `{ base with f := v }` record-update token spans
  -- multiple operators; wrap it when used as an `app` arg so it
  -- can't be reparsed as `{ base` ` with f := v }`.
  | .structUpdate _ _ _
  -- M9.5d: a `match … with …` token chain similarly spans multiple
  -- arms; wrap it when used as an `app` arg.
  | .matchE _ _ => "(" ++ s ++ ")"
  | _ => s

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
        String.intercalate " " (args.toList.map fun a =>
          parenIfNeeded (PExpr.toLeanDo a) a) ++ ")"
  | .letIn name _ e1 e2 =>
    -- Inner expressions in a monadic let bind a Result-valued
    -- computation; emit a `let … ←` form. Tail position is e2.
    s!"let {name} ← {e1.toLeanDo}\n  {e2.toLeanDo}"
  | .ok inner =>
    let s := match inner with
      | .var _ | .lit _ => PExpr.toLeanDo inner
      -- Tuple already self-parenthesises; don't add another pair.
      | .tuple _ => PExpr.toLeanDo inner
      -- `.app` also self-parenthesises (`(head a b)`), so skip
      -- adding another pair — `ok (head a b)` not `ok ((head a b))`.
      | .app _ _ => PExpr.toLeanDo inner
      -- M9.5b: `{ base with f := v }` self-delimits via braces, so
      -- skip parens — `ok { p with fst := v }` not `ok ({ … })`.
      | .structUpdate _ _ _ => PExpr.toLeanDo inner
      | _ => "(" ++ PExpr.toLeanDo inner ++ ")"
    s!"ok {s}"
  | .ifThenElse cond thenE elseE =>
    -- M11.2: standard Aeneas backend's two-line shape for short
    -- branches is `if c then <e1> else <e2>`. We keep that when both
    -- branches are single-line; otherwise unfold into a multi-line
    -- `if c\n  then …\n  else …` form.
    --
    -- M12.1: when a branch is itself a multi-line do-block (e.g. a
    -- `let t ← e` followed by `ok …`), every continuation line
    -- needs to be re-indented to sit under the `then`/`else` body
    -- start. We splice in the appropriate indent (the `t` of `then `
    -- is column 7 from the start of the `if`). The standard backend
    -- aligns the continuation under the body start, e.g.
    --     then let i1 ← i + 1#u32
    --          ok (cont i1)
    -- where "ok" sits in column 12. We approximate by using the
    -- standard backend's exact column count.
    let thenS := thenE.toLeanDo
    let elseS := elseE.toLeanDo
    let isSimple (s : String) : Bool := !s.contains '\n'
    -- Continuation-line indent for a `then ` prefix: 7 spaces puts
    -- subsequent lines under the body start. For `else ` we use 7
    -- spaces too (alignment with `else`'s body start).
    let reindent (prefixLen : Nat) (s : String) : String :=
      let pad := "".pushn ' ' prefixLen
      let lines := s.splitOn "\n"
      (lines.zipIdx).foldl (init := "") fun acc (line, i) =>
        if i = 0 then line
        -- Drop the leading "  " (the do-block sub-line indent) and
        -- replace with our pad. If the line doesn't start with "  ",
        -- leave it alone.
        else
          let stripped := if line.startsWith "  " then line.drop 2 else line
          acc ++ "\n" ++ pad ++ stripped
    if isSimple thenS && isSimple elseS then
      s!"if {cond.toLeanDo} then {thenS} else {elseS}"
    else
      let thenLines := reindent 7 thenS
      let elseLines := reindent 7 elseS
      s!"if {cond.toLeanDo}\n  then {thenLines}\n  else {elseLines}"
  | .tuple args =>
    -- M12.2a-2: render `(e₁, e₂, ...)`. Single-element tuples are
    -- syntactically forbidden in Lean; we render them as the bare
    -- inner expression.
    match args.toList with
    | [e] => e.toLeanDo
    | _ => "(" ++ String.intercalate ", " (args.toList.map PExpr.toLeanDo) ++ ")"
  | .lam params body =>
    -- M12.2a-2: `fun x₁ x₂ ... => body`. We do not emit explicit
    -- parameter types — the type is inferred from the surrounding
    -- function signature in the standard Aeneas backend, and we
    -- match that shape.
    let names := String.intercalate " " (params.toList.map (·.1))
    s!"fun {names} => {body.toLeanDo}"
  | .letPure name _ e1 e2 =>
    -- M12.2a-2: non-monadic `let name := e1; e2`. Used inside a
    -- do-block for the backward closure binding.
    s!"let {name} := {e1.toLeanDo}\n  {e2.toLeanDo}"
  | .letPat pat _ e1 e2 =>
    -- M12.2a-2: monadic `let (p₁, ..., pₙ) ← e1; e2`. Standard
    -- Aeneas backend uses `_` for the discard slot; we follow.
    let pats := String.intercalate ", " pat.toList
    s!"let ({pats}) ← {e1.toLeanDo}\n  {e2.toLeanDo}"
  | .structUpdate base field value =>
    -- M9.5b: `{ base with field := value }`. The standard Aeneas
    -- backend renders this exact shape for a write through `&mut Pair`
    -- (e.g. `set_fst`'s `ok { p with fst := v }`). We do not bracket
    -- the inner pieces; the outer `{ … }` self-delimits. `\{` and
    -- `}` escape the curly braces inside an `s!"..."` interpolation.
    s!"\{ {base.toLeanDo} with {field} := {value.toLeanDo} }"
  | .matchE scrutinee arms =>
    -- M9.5d / M9.5e: `match <scrutinee> with | Ctor1 b₁ … bₙ => body1
    -- | …`. The standard Aeneas backend renders each arm on its own
    -- line, two-space indented under the `def`'s opening line. The
    -- first line `match … with` continues the surrounding do-block;
    -- the subsequent `| Ctor … => body` lines need the same `  `
    -- prefix so they align with the `match` token. Arm bodies are
    -- monadic-position expressions (typically `ok <ctor>` or
    -- `ok <binder>`). M9.5e: binders are space-prefixed after the
    -- ctor when present (`| NumOrZero.Num n => …`).
    --
    -- M9.5j: multi-line arm bodies (e.g. a recursive call binding
    -- followed by a tail expression) need every continuation line
    -- indented under the body start, not under the `|`. We render
    -- the body inline when single-line and on a new 4-space-indented
    -- line block when multi-line, re-indenting each continuation
    -- line to the same column. The standard Aeneas backend uses
    -- this exact `=>` newline-and-4-spaces shape for
    -- `let i ← … / ok …` arm bodies.
    let armS := arms.toList.map fun (ctor, binders, body) =>
      let pat :=
        if binders.isEmpty then ctor
        else ctor ++ " " ++ String.intercalate " " binders.toList
      let bodyS := body.toLeanDo
      if bodyS.contains '\n' then
        -- Strip the default "  " (do-block sub-line indent) at the
        -- start of each continuation line and replace with a
        -- 4-space indent. Lean's parser is whitespace-sensitive on
        -- monadic-do continuations and aligns them with the first
        -- non-keyword token after `=>`; 4 spaces is the column the
        -- standard backend uses.
        let lines := bodyS.splitOn "\n"
        let bodyIndented := (lines.zipIdx).foldl (init := "")
          fun acc (line, i) =>
            if i = 0 then line
            else
              let stripped :=
                if line.startsWith "  " then line.drop 2 else line
              acc ++ "\n    " ++ stripped
        s!"  | {pat} =>\n    {bodyIndented}"
      else
        s!"  | {pat} => {bodyS}"
    s!"match {scrutinee.toLeanDo} with\n" ++ String.intercalate "\n" armS

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
  | .tuple args =>
    match args.toList with
    | [e] => e.toLean
    | _ => "(" ++ String.intercalate ", " (args.toList.map PExpr.toLean) ++ ")"
  | .lam params body =>
    let names := String.intercalate " " (params.toList.map (·.1))
    s!"fun {names} => {body.toLean}"
  | .letPure name _ e1 e2 =>
    s!"let {name} := {e1.toLean}\n  {e2.toLean}"
  | .letPat pat _ e1 e2 =>
    let pats := String.intercalate ", " pat.toList
    s!"let ({pats}) := {e1.toLean}\n  {e2.toLean}"
  | .structUpdate base field value =>
    s!"\{ {base.toLean} with {field} := {value.toLean} }"
  | .matchE scrutinee arms =>
    let armS := arms.toList.map fun (ctor, binders, body) =>
      let pat :=
        if binders.isEmpty then ctor
        else ctor ++ " " ++ String.intercalate " " binders.toList
      s!"| {pat} => {body.toLean}"
    s!"match {scrutinee.toLean} with\n" ++ String.intercalate "\n" armS

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

/-- Render the optional Lean attribute prefix, e.g. `@[rust_loop]\n`
    or `@[rust_loop_body, reducible]\n`. Empty when no attributes. -/
def Decl.attrPrefix (d : Decl) : String :=
  if d.attributes.isEmpty then ""
  else s!"@[{String.intercalate ", " d.attributes.toList}]\n"

/-- Render the Lean `def …` for `d`, with monadic body. The signature
    matches the standard Aeneas backend's output (Result, do-block).

    M12.1: the order is docComment → noteBlock → attrPrefix → def.
    The docstring `/-- … -/` must lead so Lean's parser attaches it
    to the `def`; attributes (`@[rust_loop]`, …) come immediately
    before `def`. -/
def Decl.toLean (d : Decl) : String :=
  let params := String.intercalate " "
    (d.params.toList.map fun p => s!"({p.name} : {p.ty.toLean})")
  -- M9.5c: parenthesise multi-token return types (e.g. an `.array`
  -- like `Array Std.U32 4#usize`) so `Result T` doesn't reparse as
  -- `Result` applied to four separate args. Single-token forms and
  -- self-parenthesising forms (`.tuple`, `.arrow`) stay bare.
  let retStr := d.retTy.toLean
  let retParens :=
    if retStr.contains ' ' && !retStr.startsWith "(" then
      s!"({retStr})"
    else retStr
  -- M9.5i: implicit type-param binders, rendered before the value
  -- params. Standard Aeneas backend emits `{T : Type}` (one per
  -- declared param, space-separated). Empty for monomorphic
  -- functions, so the surface stays byte-identical with the M9.5h
  -- shape.
  let typeBinders :=
    if d.typeParams.isEmpty then ""
    else
      (String.intercalate " "
        (d.typeParams.toList.map fun n => s!"\{{n} : Type}")) ++ " "
  -- M9.5f: a zero-param function (e.g. `zero : Result NumOrZero`)
  -- has empty `params`. The standard backend emits `def zero :
  -- Result …` with a single space before `:`; concatenating `params`
  -- naively would yield `def zero  :` (double space). Build the
  -- signature head explicitly so both shapes are byte-clean.
  let sigHead :=
    if d.params.isEmpty then s!"def {d.name} {typeBinders}: Result {retParens}"
    else s!"def {d.name} {typeBinders}{params} : Result {retParens}"
  -- M9.5j: optional trailer keyword line (`partial_fixpoint`, etc.)
  -- attaches at column 0 after the do-block. The standard Aeneas
  -- backend emits this for recursive functions where Lean's
  -- structural-recursion check would otherwise reject the body. We
  -- emit it on its own line, no leading indent, so the surrounding
  -- `end <namespace>` separator still injects the blank line.
  let trailerS : String :=
    match d.trailer with
    | some kw => s!"\n{kw}"
    | none => ""
  d.docComment ++ d.noteBlock ++ d.attrPrefix ++
  s!"{sigHead} := do\n  {d.body.toLeanDo}{trailerS}"

/-- M9.5b: docstring for a `structure` decl. Mirrors `Decl.docComment`
    but uses the `[crate::Foo]` form without a trailing colon (the
    standard Aeneas backend uses the same shape). -/
def StructDecl.docComment (sd : StructDecl) : String :=
  match sd.sourceSpan with
  | none => ""
  | some sp =>
    let loc :=
      s!"{sp.begLine}:{sp.begCol}-{sp.endLine}:{sp.endCol}"
    s!"/-- [{sd.qualifiedName}]\n    Source: '{sp.file}', lines {loc} -/\n"

/-- M9.5l: docstring for a unit-struct alias. The standard Aeneas
    backend adds a `Visibility: public` line that we elide (we
    universally elide it across all decls — known cosmetic drift). -/
private def StructDecl.unitAliasDocComment (sd : StructDecl) : String :=
  match sd.sourceSpan with
  | none => ""
  | some sp =>
    let loc :=
      s!"{sp.begLine}:{sp.begCol}-{sp.endLine}:{sp.endCol}"
    s!"/-- [{sd.qualifiedName}]\n    Source: '{sp.file}', lines {loc} -/\n"

/-- M9.5b: render a `structure Foo where …` block. Each field becomes
    one `  name : ty` line. Empty-field structs still emit the
    `structure` header (so the type is constructable as `{}` in Lean).

    M9.5l: a tuple struct with zero fields renders as
    `@[reducible] def <Name> := Unit` instead — matching the standard
    Aeneas backend's encoding of `pub struct Tag;`. The `@[reducible]`
    attribute is needed so Lean's elaborator unfolds the alias when
    typechecking a `Numeric Tag` instance ascription. -/
def StructDecl.toLean (sd : StructDecl) : String :=
  if sd.isTupleStruct ∧ sd.fields.isEmpty then
    -- M9.5l: unit struct → `@[reducible] def <Name> := Unit`.
    -- Type parameters on a unit struct are a degenerate case
    -- (e.g. `struct Phantom<T>;`); we render them anyway as
    -- `(T : Type)` binders before the `:=` for forward-compat.
    let typeBinders :=
      if sd.typeParams.isEmpty then ""
      else " " ++ String.intercalate " "
        (sd.typeParams.toList.map fun n => s!"({n} : Type)")
    sd.unitAliasDocComment ++ "@[reducible]\n" ++
      s!"def {sd.name}{typeBinders} := Unit"
  else
    -- M9.5i: explicit type-param binders go between the name and the
    -- `where`, rendered as `(T : Type) (U : Type) …`. Empty for
    -- monomorphic structs (the M9.5b shape).
    let typeBinders :=
      if sd.typeParams.isEmpty then ""
      else " " ++ String.intercalate " "
        (sd.typeParams.toList.map fun n => s!"({n} : Type)")
    let header := s!"structure {sd.name}{typeBinders} where"
    let body := sd.fields.toList.map fun f => s!"  {f.name} : {f.ty.toLean}"
    sd.docComment ++ header ++ "\n" ++ String.intercalate "\n" body

/-- M9.5d: docstring for an `inductive` decl, same shape as
    [StructDecl.docComment]. -/
def EnumDecl.docComment (ed : EnumDecl) : String :=
  match ed.sourceSpan with
  | none => ""
  | some sp =>
    let loc :=
      s!"{sp.begLine}:{sp.begCol}-{sp.endLine}:{sp.endCol}"
    s!"/-- [{ed.qualifiedName}]\n    Source: '{sp.file}', lines {loc} -/\n"

/-- M9.5d / M9.5e: render an `inductive Foo where …` block. Each
    variant becomes one line: `| Variant : Foo` for a nullary variant,
    or `| Variant : Ty₁ → … → Tyₙ → Foo` for a payload-bearing variant
    (M9.5e). Field names from the cert are discarded at this layer;
    the standard Aeneas backend renders tuple-style variants positionally,
    and we match that shape. -/
def EnumDecl.toLean (ed : EnumDecl) : String :=
  -- M9.5i: explicit type-param binders go between the name and the
  -- `where`, rendered as `(T : Type) (U : Type) …` (matching the
  -- standard Aeneas backend's shape). Empty for monomorphic enums
  -- (the M9.5d/e shape).
  let typeBinders :=
    if ed.typeParams.isEmpty then ""
    else " " ++ String.intercalate " "
      (ed.typeParams.toList.map fun n => s!"({n} : Type)")
  -- M9.5i: in each variant's `: ... → <Enum>` signature, the trailing
  -- `<Enum>` becomes `<Enum> T₁ T₂ ...` for a generic enum so the
  -- variant's return type is fully applied. Monomorphic enums keep
  -- the bare `<Enum>` shape from M9.5d/e.
  let appliedName : String :=
    if ed.typeParams.isEmpty then ed.name
    else ed.name ++ " " ++ String.intercalate " " ed.typeParams.toList
  let header := s!"inductive {ed.name}{typeBinders} where"
  let body := ed.variants.toList.map fun v =>
    if v.fields.isEmpty then
      s!"| {v.name} : {appliedName}"
    else
      let tys := v.fields.toList.map fun f => f.ty.toLean
      let signature := String.intercalate " → " (tys ++ [appliedName])
      s!"| {v.name} : {signature}"
  ed.docComment ++ header ++ "\n" ++ String.intercalate "\n" body

/-- M9.5l: docstring for a `trait` decl. The standard Aeneas backend
    prefixes the comment with `Trait declaration: ` and lists the
    qualified name in `[...]` brackets — mirror that exactly. -/
def TraitDecl.docComment (td : TraitDecl) : String :=
  match td.sourceSpan with
  | none => ""
  | some sp =>
    let loc :=
      s!"{sp.begLine}:{sp.begCol}-{sp.endLine}:{sp.endCol}"
    s!"/-- Trait declaration: [{td.qualifiedName}]\n    Source: '{sp.file}', lines {loc} -/\n"

/-- M9.5l: render a method type at the trait-method-row top level —
    i.e. strip the outer `( … )` that `PTy.toLean` would add around an
    `.arrow` so the standard backend's `value : Self → Result Std.U32`
    shape comes out unwrapped (the `app`-arg form keeps its parens). -/
private def PTy.toLeanMethodSlot : PTy → String
  | .arrow dom cod => s!"{dom.toLean} → {cod.toLean}"
  | other => other.toLean

/-- M9.5l: render a `structure <Name> (Self : Type) where …` block.
    Each method becomes one `  <name> : <ty>` line under the header.
    Matches the standard Aeneas backend's encoding of a Rust trait —
    Aeneas uses a Lean `structure`, not a typeclass, so impl resolution
    happens via named instances rather than implicit search. -/
def TraitDecl.toLean (td : TraitDecl) : String :=
  let header := s!"structure {td.name} (Self : Type) where"
  let body := td.methods.toList.map fun m =>
    s!"  {m.name} : {PTy.toLeanMethodSlot m.ty}"
  td.docComment ++ header ++ "\n" ++ String.intercalate "\n" body

/-- M9.5l: docstring for a trait impl. Mirrors the standard backend's
    `Trait implementation: [<qualified>]` prefix shape. -/
def TraitImpl.docComment (ti : TraitImpl) : String :=
  match ti.sourceSpan with
  | none => ""
  | some sp =>
    let loc :=
      s!"{sp.begLine}:{sp.begCol}-{sp.endLine}:{sp.endCol}"
    s!"/-- Trait implementation: [{ti.qualifiedName}]\n    Source: '{sp.file}', lines {loc} -/\n"

/-- M9.5l: render an `@[reducible] def <Name> : <TraitName> <SelfTy>
    := { … }` block. The instance literal binds each method to its
    pre-computed body name (already qualified, e.g.
    `Tag.Insts.Traits_basicNumeric.value`). -/
def TraitImpl.toLean (ti : TraitImpl) : String :=
  let methodLines := ti.methods.toList.map fun m =>
    s!"  {m.name} := {m.body}"
  let header := s!"@[reducible]\ndef {ti.name} : {ti.traitName} {ti.selfTy.toLean} := \{"
  ti.docComment ++ header ++ "\n" ++
    String.intercalate "\n" methodLines ++ "\n}"

/-- M9.5b: render a `TopDecl` (struct / enum / function) into Lean
    source. M9.5d added the enum case. M9.5l added trait decls + impls. -/
def TopDecl.toLean : TopDecl → String
  | .struct sd => sd.toLean
  | .enum ed => ed.toLean
  | .function d => d.toLean
  | .traitDecl td => td.toLean
  | .traitImpl ti => ti.toLean

end AeneasCheck.Pure
