import AeneasCheck.Translate.Forward
import AeneasCheck.Translate.Loops

/-!
End-to-end pipeline:

    parse  cert.json  →  Raw.CrateCert
    typecheck         →  (errors)
    replay  trace     →  CheckedTrace
    translate         →  Pure.Decl
    emit              →  Lean source / Rust source (separate modules)
-/

namespace AeneasCheck.Translate

open AeneasCheck Raw Pure LLBCSharp

structure TranslatedCrate where
  decls : Array Decl
  /-- M9.5b: ADT struct decls, in cert order. Emitted before function
      decls in the same crate namespace. Empty for crates with no
      structs. -/
  structs : Array StructDecl := #[]
  /-- M9.5d: ADT enum decls, in cert order. Emitted alongside struct
      decls (before function decls). Empty for crates with no enums. -/
  enums : Array EnumDecl := #[]
  /-- M9.5l: trait decls, in cert order. Emitted before any impl that
      references them (impls come after); both go in the crate
      namespace alongside structs / enums. -/
  traitDecls : Array Pure.TraitDecl := #[]
  /-- M9.5l: trait impls, in cert order. Each impl's `methods`
      reference body functions by their pre-computed `prettyName`,
      which the call-site emitter also uses (via the
      `fnIdPrettyName` table threaded through `translateFunWith`). -/
  traitImpls : Array Pure.TraitImpl := #[]
  deriving Inhabited

/-- M9.5n: the set of stdlib ADT qualified names whose cert decl
    must NOT be re-emitted by the Lean translator. Each one already
    has a Lean equivalent that the emitted file's
    `open Aeneas Aeneas.Std` brings into scope (e.g. `Option`,
    `Result`, `Ordering`, `ControlFlow`). Re-declaring them inside
    the crate namespace shadows the built-ins and breaks
    elaboration of any reference to those types.

    The list mirrors a subset of the standard Aeneas Lean backend's
    `lean_builtin_types` table from
    `src/extract/ExtractBuiltinLean.ml` — only the entries whose
    cert decls show up in the M9.5n / pre-M9.5n fixtures. Future
    fixtures may grow this list as they exercise more stdlib ADTs.

    The `TypeDeclMap` still records suppressed decls so cert events
    that mention `TAdtId N` for, e.g., the stdlib `Option` continue
    to resolve to `.adt "Option" #[…]` in field types and signatures;
    only the per-decl `structure`/`inductive` emission is skipped. -/
def isStdlibTypeDecl (qualifiedName : String) : Bool :=
  match qualifiedName with
  | "alloc::alloc::Global"
  | "core::option::Option"
  | "core::result::Result"
  | "core::cmp::Ordering"
  | "core::ops::control_flow::ControlFlow" => true
  | _ => false

/-- M9.5b: build the [TypeDeclMap] used by the per-function translator
    to resolve `TAdtId N` references to struct names + field names.
    Only struct decls populate entries; opaque/unknown kinds are
    skipped (so `Field K` projections through them fall back to the
    M11 non-struct paths). -/
def buildTypeDeclMap (cc : CrateCert) : TypeDeclMap := Id.run do
  let mut m : TypeDeclMap := {}
  for td in cc.typeDecls do
    match td.kind with
    | .struct fields =>
      let names : Array String := fields.map fun f =>
        match f.name with
        | some n => n
        | none => s!"field{f.idx}"
      m := m.insert td.id { name := td.name, fieldNames := names }
    | .enum variants =>
      -- M9.5d: register the enum so [parseTAdtId]-driven type
      -- resolution can produce a `.adt <name>` PTy for parameters
      -- / return types of `Sign`-shaped enums. The Forward
      -- translator needs the bare adt name to qualify the variant
      -- constructors. M9.5e: also record each variant's payload
      -- arity so the match-arm sub-walk can pre-seed payload
      -- binders (one per field) for the arm body.
      let counts : Array Nat := variants.map fun v => v.fields.size
      m := m.insert td.id
        { name := td.name, fieldNames := #[], variantFieldCounts := counts }
    | .opaque => ()
  return m

/-- M9.5b: lift a cert `TypeDecl` into a Pure `StructDecl`, when the
    decl is a struct. Returns `none` for opaque/unknown kinds (we
    silently skip those — M9.5c+ will surface them). Field types
    come through as opaque cert strings; we feed them through
    `rawTyToPTyWith` (defined in Forward.lean) to get a concrete
    Pure type.

    M9.5l: `isTupleStruct` flows through so the pretty-printer can
    render unit structs as `@[reducible] def Tag := Unit`. -/
def structDeclOfTypeDecl (tdm : TypeDeclMap) (crateName : String) (td : TypeDecl) :
    Option StructDecl :=
  -- M9.5n: skip stdlib ADTs (`alloc::alloc::Global`, …). They have
  -- Lean equivalents already in scope via `open Aeneas Aeneas.Std`;
  -- re-emitting them here would either bloat the file (`Global`) or
  -- actively shadow the built-in (`Option`, `Result`).
  if isStdlibTypeDecl td.qualifiedName then none
  else match td.kind with
  | .struct fields =>
    -- M9.5i: pass the struct's `typeParams` into the field-type
    -- translator so a generic field type `T` resolves to
    -- `.tyVar "T"` rather than the placeholder.
    let pureFields : Array StructField := fields.map fun f =>
      { name :=
          match f.name with
          | some n => n
          | none => s!"field{f.idx}"
        ty := rawTyToPTyWithVars tdm td.typeParams f.ty }
    some
      { name := td.name
        qualifiedName := s!"{crateName}::{td.name}"
        fields := pureFields
        typeParams := td.typeParams
        isTupleStruct := td.isTupleStruct
        sourceSpan := td.sourceSpan }
  | .enum _ => none
  | .opaque => none

/-- M9.5d / M9.5e: lift a cert `TypeDecl` into a Pure `EnumDecl`,
    when the decl is an enum. M9.5e populates each variant's field
    list (was empty under M9.5d) so payload-bearing variants render
    with their parameter types (e.g. `| Num : Std.U32 → NumOrZero`).
    Returns `none` for non-enum kinds; struct decls go through
    [structDeclOfTypeDecl] instead. -/
def enumDeclOfTypeDecl (tdm : TypeDeclMap) (crateName : String) (td : TypeDecl) :
    Option EnumDecl :=
  -- M9.5n: skip stdlib ADTs (`core::option::Option`,
  -- `core::result::Result`, `core::cmp::Ordering`, …). Re-emitting
  -- e.g. `inductive Option (T : Type) where …` shadows Lean's
  -- built-in `Option` and breaks any reference to the stdlib type
  -- in the rest of the emitted file.
  if isStdlibTypeDecl td.qualifiedName then none
  else match td.kind with
  | .enum variants =>
    -- M9.5i: pass the enum's `typeParams` into the field-type
    -- translator so a generic variant payload type like
    -- `MySome(T)` → `T` (i.e. `TVar (Free 0)` in the cert)
    -- resolves to `.tyVar "T"` rather than the placeholder.
    let pureVariants : Array EnumVariant := variants.map fun v =>
      let pureFields : Array StructField := v.fields.map fun f =>
        { name :=
            match f.name with
            | some n => n
            | none => s!"field{f.idx}"
          ty := rawTyToPTyWithVars tdm td.typeParams f.ty }
      { name := v.name, fields := pureFields }
    some
      { name := td.name
        qualifiedName := s!"{crateName}::{td.name}"
        variants := pureVariants
        typeParams := td.typeParams
        sourceSpan := td.sourceSpan }
  | .struct _ => none
  | .opaque => none

/-- M9.5l: heuristic strip of an outer `TRef (…, RShared)` /
    `TRef (…, RMut)` wrapper around a cert type string, returning the
    inner type substring. The standard backend's pure layer drops
    the borrow shape from method input types; we mirror that for the
    trait-declaration's `self` parameter.

    The cert string for `&T` arrives as
    `(Generated_Types.TRef (<region>, <inner>, Generated_Types.RShared))`
    where `<inner>` is itself a parenthesised cert type. We find the
    second top-level comma inside the outer `TRef (…)` and return
    the slice between the two commas, trimmed. Returns the original
    string when the shape doesn't match (so the regular
    `rawTyToPTyWithVars` path handles non-ref types). -/
private def stripOuterRef (s : String) : String := Id.run do
  -- Locate the start of the outer `TRef`.
  let parts := s.splitOn "TRef"
  if parts.length < 2 then return s
  -- After the first `TRef`, scan for the opening `(` of the args list,
  -- then walk the chars tracking paren depth. Two top-level commas
  -- (depth = 1) delimit the three args: region, inner, ref-kind.
  let after := parts.tail!.head!
  let chars := after.toList
  let mut depth : Nat := 0
  let mut innerStart : Option Nat := none
  let mut innerEnd : Option Nat := none
  let mut commaCount : Nat := 0
  let mut idx : Nat := 0
  for c in chars do
    if c = '(' then depth := depth + 1
    else if c = ')' then
      if depth = 0 then break
      else depth := depth - 1
    else if c = ',' ∧ depth = 1 then
      commaCount := commaCount + 1
      if commaCount = 1 then innerStart := some (idx + 1)
      else if commaCount = 2 then innerEnd := some idx
    idx := idx + 1
  match innerStart, innerEnd with
  | some a, some b =>
    if a ≥ b then return s
    let n := b - a
    let chrs := (after.toList.drop a).take n
    let trimmed := (chrs.dropWhile Char.isWhitespace).reverse.dropWhile
      Char.isWhitespace
    return String.ofList trimmed.reverse
  | _, _ => return s

/-- M9.5l: lift a cert `TraitDecl` into a Pure `TraitDecl`. The trait
    method's signature in the cert always has `Self` as its first
    parameter; we render the method as a `Self → Result <output>`
    function-type. Borrow heads on input types are stripped (the
    standard backend's pure layer does the same). -/
def traitDeclOfCert (tdm : TypeDeclMap) (_crateName : String)
    (td : Raw.TraitDecl) : Pure.TraitDecl :=
  -- For the M9.5l minimal-case trait, the binder always introduces
  -- exactly one type parameter named "Self". The cert's
  -- `TVar (Free 0)` references resolve to this name.
  let selfParams : Array String := #[ "Self" ]
  let methods : Array Pure.TraitMethod := td.methods.map fun m =>
    let inputs : Array PTy := m.signature.inputs.map fun rt =>
      match rt with
      | .opaque s =>
        let stripped := stripOuterRef s
        rawTyToPTyWithVars tdm selfParams (.opaque stripped)
      | other => rawTyToPTyWithVars tdm selfParams other
    let retInner : PTy :=
      rawTyToPTyWithVars tdm selfParams m.signature.output
    -- Build the method's full type: `inp1 → inp2 → … → Result retInner`.
    -- For the minimal-case M9.5l fixture, `inputs` has exactly one
    -- entry (`self : Self`), but we generalise to N inputs for
    -- forward compatibility.
    let buildArrow (acc : PTy) (xs : List PTy) : PTy :=
      xs.foldr (fun a b => .arrow a b) acc
    let ty := buildArrow (.result retInner) inputs.toList
    { name := m.name, ty }
  { name := td.name
    qualifiedName := td.qualifiedName
    methods
    sourceSpan := td.sourceSpan }

/-- M9.5l: lift a cert `TraitImpl` into a Pure `TraitImpl`. The impl
    method's `body` is the trait-impl-method body function's
    standard-backend Lean name (`<prettyName>.<methodName>`). The
    Self type is resolved via `selfTypeDeclId` against the
    `TypeDeclMap`. -/
def traitImplOfCert (tdm : TypeDeclMap)
    (traitNameById : Std.HashMap Nat String)
    (_crateName : String) (ti : Raw.TraitImpl) : Pure.TraitImpl :=
  let selfTy : PTy :=
    match ti.selfTypeDeclId with
    | some id =>
      match tdm[id]? with
      | some info => .adt info.name #[]
      | none => .unit
    | none => .unit
  let traitName : String :=
    traitNameById.getD ti.traitDeclId "__UnknownTrait"
  let methods : Array Pure.TraitImplMethod := ti.methods.map fun m =>
    { name := m.name, body := s!"{ti.prettyName}.{m.name}" }
  { name := ti.prettyName
    qualifiedName := ti.qualifiedName
    traitName
    selfTy
    methods
    sourceSpan := ti.sourceSpan }

/-- M9.5l: traverse a `PExpr` and replace every `.app head args`
    whose `head` matches a key in `pretty` with the corresponding
    pretty name. Used to rewrite trait-impl-method call sites from
    the Charon `traits_basic::{...}::value` form to the standard-
    backend's `Tag.Insts.Traits_basicNumeric.value` form. -/
partial def rewriteCalleeNames (pretty : Std.HashMap String String) :
    PExpr → PExpr
  | .var n => .var n
  | .lit l => .lit l
  | .app head args =>
    let head' := pretty.getD head head
    .app head' (args.map (rewriteCalleeNames pretty))
  | .letIn n ty e1 e2 =>
    .letIn n ty (rewriteCalleeNames pretty e1) (rewriteCalleeNames pretty e2)
  | .ok e => .ok (rewriteCalleeNames pretty e)
  | .ifThenElse c t e =>
    .ifThenElse (rewriteCalleeNames pretty c)
                (rewriteCalleeNames pretty t)
                (rewriteCalleeNames pretty e)
  | .tuple args => .tuple (args.map (rewriteCalleeNames pretty))
  | .lam ps body => .lam ps (rewriteCalleeNames pretty body)
  | .letPure n ty e1 e2 =>
    .letPure n ty (rewriteCalleeNames pretty e1) (rewriteCalleeNames pretty e2)
  | .letPat ps ty e1 e2 =>
    .letPat ps ty (rewriteCalleeNames pretty e1) (rewriteCalleeNames pretty e2)
  | .structUpdate base f v =>
    .structUpdate (rewriteCalleeNames pretty base) f (rewriteCalleeNames pretty v)
  | .matchE scr arms =>
    .matchE (rewriteCalleeNames pretty scr)
            (arms.map fun (ctor, binders, body) =>
              (ctor, binders, rewriteCalleeNames pretty body))

/-- Translate a whole crate cert. Per-function metadata (signature,
    source span) is taken from the cert's `FunCert`, while the
    behavioural trace comes from the replayer's `CheckedTrace`.

    M9.5b: cert `type_decls` lift into `StructDecl`s; `LeanEmit`
    emits them before functions in the same namespace.

    M12.1: functions whose cert contains an `EvLoopInv` / `EvLoopEnd`
    pair are translated via `translateLoopFun`, which emits three
    decls (body / wrapper / top-level). Non-loop functions go through
    the M10 `translateFun` (one decl). -/
def translateCrate (cc : CrateCert) : Except String TranslatedCrate := do
  let traces ← replayCrate cc
  if traces.size ≠ cc.functions.size then
    throw s!"translate: replay produced {traces.size} traces, cert has {cc.functions.size} functions"
  -- M9.5b: derive the crate name from the first function's qualified
  -- name (everything before the first `::`). Fall back to "crate" if
  -- there are no functions; structs from such a crate end up in a
  -- `crate` namespace, which the emitter handles uniformly.
  let crateName : String :=
    match cc.functions.toList with
    | f :: _ => (f.fnName.splitOn "::").headD "crate"
    | [] => "crate"
  let tdm := buildTypeDeclMap cc
  let structs : Array StructDecl :=
    cc.typeDecls.filterMap (structDeclOfTypeDecl tdm crateName)
  let enums : Array EnumDecl :=
    cc.typeDecls.filterMap (enumDeclOfTypeDecl tdm crateName)
  -- M9.5l: lift cert trait decls + impls into Pure IR. We also build
  -- a `traitNameById` lookup so impls can resolve their target trait
  -- by id.
  let traitDecls : Array Pure.TraitDecl :=
    cc.traitDecls.map (traitDeclOfCert tdm crateName)
  let traitNameById : Std.HashMap Nat String :=
    cc.traitDecls.foldl (init := {}) fun acc td =>
      acc.insert td.id td.name
  let traitImpls : Array Pure.TraitImpl :=
    cc.traitImpls.map (traitImplOfCert tdm traitNameById crateName)
  -- M9.5l: build a per-fn-id → pretty-name table so the Forward
  -- translator can rewrite EvCall `fn_name` to its standard-backend
  -- shape (e.g. `traits_basic::{...}::value` →
  -- `Tag.Insts.Traits_basicNumeric.value`).
  let fnPrettyByName : Std.HashMap String String :=
    cc.functions.foldl (init := {}) fun acc f =>
      match f.prettyName with
      | some n => acc.insert f.fnName n
      | none => acc
  let mut decls : Array Decl := #[]
  for i in [0:cc.functions.size] do
    let f := cc.functions[i]!
    match translateLoopFun f with
    | some loopDecls => decls := decls ++ loopDecls
    | none => decls := decls.push (translateFunWith tdm f traces[i]!)
  -- M9.5l: rewrite each Decl's body to use pretty names for any
  -- callee whose `fn_name` is in `fnPrettyByName`. Also rewrite the
  -- Decl's own `name` when its qualifiedName carries a pretty-name
  -- override (so the impl method body's `def` header uses
  -- `Tag.Insts.Traits_basicNumeric.value` not `{...}.value`).
  decls := decls.map fun d =>
    let body := rewriteCalleeNames fnPrettyByName d.body
    -- If this decl's *own* function name maps to a pretty name,
    -- override its `name` (which the LeanEmit uses as the `def`
    -- header). The impl-method body decl is the only case where
    -- this triggers in M9.5l.
    let nameOverride : Option String := fnPrettyByName[d.qualifiedName]?
    match nameOverride with
    | some n =>
      -- Strip the leading crate segment to get the bare def name
      -- within the crate namespace block. The pretty name format is
      -- `Tag.Insts.<crateCap><Trait>.<method>` — we keep the full
      -- name, since the namespace block in LeanEmit doesn't strip
      -- it (the pretty name's segments aren't `::`-separated so the
      -- existing splitOn logic ignores them).
      { d with name := n, body }
    | none =>
      { d with body }
  return { decls, structs, enums, traitDecls, traitImpls }

end AeneasCheck.Translate
