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

/-- M9.7k: structured-source twin of [buildTypeDeclMap]. Builds the
    same `TypeDeclId → TypeDeclInfo` map but reads from
    `cc.llbcProgram.typeDecls` instead of the flat `cc.typeDecls`.

    The map's `name` slot is the *bare* last segment of the LLBC
    item-meta name (e.g. `test_crate::Pair` → `Pair`). Union / alias /
    opaque LLBC decls don't populate the map (they don't appear as
    callable struct / enum heads in the translator's downstream
    consumers). -/
def buildTypeDeclMapFromLlbc (cc : CrateCert) : TypeDeclMap := Id.run do
  let mut m : TypeDeclMap := {}
  for td in cc.llbcProgram.typeDecls do
    let bareName := bareNameOfQualified td.itemMeta.name
    match td.kind with
    | .struct fields =>
      let names : Array String := fields.map fun f =>
        match f.name with
        | some n => n
        | none => s!"field{f.idx}"
      m := m.insert td.id { name := bareName, fieldNames := names }
    | .enum variants =>
      let counts : Array Nat := variants.map fun v => v.fields.size
      m := m.insert td.id
        { name := bareName, fieldNames := #[], variantFieldCounts := counts }
    | .union _ | .tAlias _ | .opaque => ()
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

/-- M9.7k: structured-source twin of [structDeclOfTypeDecl]. Lifts an
    `LlbcTypeDecl` (when its kind is `struct`) into a `StructDecl`,
    sourcing field types from `LlbcTy` via [llbcTyToPTyWithVars]
    rather than parsing opaque cert-strings. -/
def structDeclOfLlbcTypeDecl (tdm : TypeDeclMap) (crateName : String)
    (td : LlbcTypeDecl) : Option StructDecl :=
  let bareName := bareNameOfQualified td.itemMeta.name
  let typeParams := td.generics.types
  if isStdlibTypeDecl td.itemMeta.name then none
  else match td.kind with
  | .struct fields =>
    let pureFields : Array StructField := fields.map fun f =>
      { name :=
          match f.name with
          | some n => n
          | none => s!"field{f.idx}"
        ty := llbcTyToPTyWithVars tdm typeParams f.ty }
    some
      { name := bareName
        qualifiedName := s!"{crateName}::{bareName}"
        fields := pureFields
        typeParams := typeParams
        isTupleStruct := td.isTupleStruct
        sourceSpan := td.itemMeta.span }
  | .enum _ | .union _ | .tAlias _ | .opaque => none

/-- M9.7k: structured-source twin of [enumDeclOfTypeDecl]. -/
def enumDeclOfLlbcTypeDecl (tdm : TypeDeclMap) (crateName : String)
    (td : LlbcTypeDecl) : Option EnumDecl :=
  let bareName := bareNameOfQualified td.itemMeta.name
  let typeParams := td.generics.types
  if isStdlibTypeDecl td.itemMeta.name then none
  else match td.kind with
  | .enum variants =>
    let pureVariants : Array EnumVariant := variants.map fun v =>
      let pureFields : Array StructField := v.fields.map fun f =>
        { name :=
            match f.name with
            | some n => n
            | none => s!"field{f.idx}"
          ty := llbcTyToPTyWithVars tdm typeParams f.ty }
      { name := v.name, fields := pureFields }
    some
      { name := bareName
        qualifiedName := s!"{crateName}::{bareName}"
        variants := pureVariants
        typeParams := typeParams
        sourceSpan := td.itemMeta.span }
  | .struct _ | .union _ | .tAlias _ | .opaque => none

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

/-- M9.5o: given a per-clause obligation `(traitQualifiedName,
    typeParamIdx)` and the surrounding decl's `typeParams` list,
    build a Pure `TraitBoundParam`. The trait's bare name is looked
    up via `traitNameByQualified`; if the qualified name isn't in
    the table the bare name falls back to the last `::`-segment of
    the qualified form. The binder name is canonically
    `<TraitName>Inst`. -/
def traitBoundParamOf
    (traitNameByQualified : Std.HashMap String String)
    (typeParams : Array String)
    (c : Raw.TraitClause) : Pure.TraitBoundParam :=
  let bareTrait : String :=
    match traitNameByQualified[c.traitQualifiedName]? with
    | some n => n
    | none =>
      match (c.traitQualifiedName.splitOn "::").getLast? with
      | some n => n
      | none => c.traitQualifiedName
  let selfTypeName : String :=
    match typeParams[c.typeParamIdx]? with
    | some n => n
    | none => "_"
  { binderName := s!"{bareTrait}Inst"
    traitName := bareTrait
    selfTypeName }

/-- M9.5l: lift a cert `TraitImpl` into a Pure `TraitImpl`. The impl
    method's `body` is the trait-impl-method body function's
    standard-backend Lean name (`<prettyName>.<methodName>`). The
    Self type is resolved via `selfTypeDeclId` against the
    `TypeDeclMap`.

    M9.5o: a blanket impl (Self is a type variable) is rendered with
    `{T : Type} (Trait1Inst : Trait1 T) : Trait2 T` binders. The
    cert's `selfTypeVar` carries the type variable's name; the
    record literal's method bodies are applied to the trait-bound
    binders so the impl forwards each clause to the body fn. -/
def traitImplOfCert (tdm : TypeDeclMap)
    (traitNameById : Std.HashMap Nat String)
    (traitNameByQualified : Std.HashMap String String)
    (_crateName : String) (ti : Raw.TraitImpl) : Pure.TraitImpl :=
  let selfTy : PTy :=
    match ti.selfTypeVar with
    | some n => .tyVar n
    | none =>
      match ti.selfTypeDeclId with
      | some id =>
        match tdm[id]? with
        | some info => .adt info.name #[]
        | none => .unit
      | none =>
        -- M9.5u: primitive Self (e.g. [impl Tr for bool]) — neither
        -- a declared ADT nor a type variable. The OCaml cert
        -- generator already encoded the Self type's Lean name as
        -- the prefix of [prettyName] (e.g. `Bool.Insts.…`,
        -- `Std.U32.Insts.…`). Split on `.Insts.` to recover it and
        -- bind as an opaque ADT name. Falls back to [.unit] when
        -- the prettyName doesn't carry the `.Insts.` separator
        -- (defensive — should never happen for a non-blanket impl).
        let segs := ti.prettyName.splitOn ".Insts."
        match segs with
        | hd :: _ :: _ => .adt hd #[]
        | _ => .unit
  let traitName : String :=
    traitNameById.getD ti.traitDeclId "__UnknownTrait"
  let traitBoundParams : Array Pure.TraitBoundParam :=
    ti.traitClauses.map (traitBoundParamOf traitNameByQualified ti.typeParams)
  let methods : Array Pure.TraitImplMethod := ti.methods.map fun m =>
    { name := m.name, body := s!"{ti.prettyName}.{m.name}" }
  { name := ti.prettyName
    qualifiedName := ti.qualifiedName
    traitName
    selfTy
    methods
    sourceSpan := ti.sourceSpan
    typeParams := ti.typeParams
    traitBoundParams }

/-- M9.7l: structured-source twin of [traitDeclOfCert]. Lifts an
    `LlbcTraitDecl` into a `Pure.TraitDecl`. Method signatures are
    translated via [llbcTyToPTyWithVars] with `selfParams := #["Self"]`
    so any `LlbcTy.tVar 0` inside a method input/output resolves to
    `.tyVar "Self"`. Borrow heads on inputs are stripped (the value
    layer drops `&` / `&mut` shape). -/
def traitDeclOfLlbcTraitDecl (tdm : TypeDeclMap) (_crateName : String)
    (td : LlbcTraitDecl) : Pure.TraitDecl :=
  let selfParams : Array String := #[ "Self" ]
  let bareName := bareNameOfQualified td.itemMeta.name
  let methods : Array Pure.TraitMethod := td.methods.map fun m =>
    let inputs : Array PTy := m.signature.inputs.map fun rt =>
      -- Strip an outer `&'r T` / `&'r mut T` (mirror of [stripOuterRef]
      -- on the flat path) — the value layer renders `self : Self`,
      -- not `&self`. The `tRef` case unwraps to the inner type.
      match rt with
      | .tRef _ inner _ => llbcTyToPTyWithVars tdm selfParams inner
      | other => llbcTyToPTyWithVars tdm selfParams other
    let retInner : PTy :=
      llbcTyToPTyWithVars tdm selfParams m.signature.output
    let buildArrow (acc : PTy) (xs : List PTy) : PTy :=
      xs.foldr (fun a b => .arrow a b) acc
    let ty := buildArrow (.result retInner) inputs.toList
    { name := m.name, ty }
  { name := bareName
    qualifiedName := td.itemMeta.name
    methods
    sourceSpan := td.itemMeta.span }

/-- M9.7l: capitalise the first character of a string (ASCII).
    Helper for the standard-backend impl-pretty-name shape. -/
def capitalizeFirstLetter (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: rest => String.ofList (c.toUpper :: rest)

/-- M9.7l: extract the first `::`-segment of a qualified path. Helper
    for the standard-backend impl-pretty-name shape. -/
def crateSegmentOf (qualified : String) : String :=
  match (qualified.splitOn "::").head? with
  | some s => s
  | none => qualified

/-- M9.7l: Lean name of a primitive literal type, mirroring the
    OCaml-side `lean_name_of_lit_ty`. Used to root the impl-pretty-
    name for primitive-Self impls (e.g. `impl Tr for bool` →
    `Bool.Insts.…`). -/
def leanNameOfLitTy : LitTy → String
  | .bool => "Bool"
  | .int .u8 => "Std.U8"
  | .int .u16 => "Std.U16"
  | .int .u32 => "Std.U32"
  | .int .u64 => "Std.U64"
  | .int .u128 => "Std.U128"
  | .int .usize => "Std.Usize"
  | .int .i8 => "Std.I8"
  | .int .i16 => "Std.I16"
  | .int .i32 => "Std.I32"
  | .int .i64 => "Std.I64"
  | .int .i128 => "Std.I128"
  | .int .isize => "Std.Isize"
  | .char => "Char"
  | .float _ => "Float"

/-- M9.7l: structured-source twin of [traitImplOfCert]. Lifts an
    `LlbcTraitImpl` into a `Pure.TraitImpl`. The standard-backend
    impl-pretty-name shape is recomputed from the structured info:

      * blanket impl (`selfType` is a type variable):
        `<TraitBare>.Blanket`
      * ADT Self:   `<SelfBare>.Insts.<CrateCap><TraitBare>`
      * primitive Self: same but `<SelfBare>` is the literal's Lean
        name (e.g. `Bool`, `Std.U32`).

    Mirrors `CertGen.ml`'s computation around line 437. -/
def traitImplOfLlbcTraitImpl (tdm : TypeDeclMap)
    (traitNameById : Std.HashMap Nat String)
    (traitQualifiedNameById : Std.HashMap Nat String)
    (_crateName : String) (ti : LlbcTraitImpl) : Pure.TraitImpl :=
  -- Resolve the Self type's bare name from the structured selfType.
  let (selfTypeVar, selfBareName, selfTy) : Option String × String × PTy :=
    match ti.selfType with
    | .tVar k =>
      let n := (ti.generics.types[k]?).getD "_"
      (some n, "Blanket", .tyVar n)
    | .tAdt id _ =>
      match tdm[id]? with
      | some info => (none, info.name, .adt info.name #[])
      | none => (none, "__UnknownSelf", .unit)
    | .litTy k =>
      let n := leanNameOfLitTy k
      (none, n, .adt n #[])
    | _ => (none, "__UnknownSelf", .unit)
  let traitBare : String :=
    traitNameById.getD ti.traitDeclId "__UnknownTrait"
  let traitQualified : String :=
    traitQualifiedNameById.getD ti.traitDeclId ""
  let traitCrateSeg : String := crateSegmentOf traitQualified
  let prettyName : String :=
    match selfTypeVar with
    | some _ => s!"{traitBare}.Blanket"
    | none => s!"{selfBareName}.Insts.{capitalizeFirstLetter traitCrateSeg}{traitBare}"
  let traitNameByQualified : Std.HashMap String String :=
    -- Build a local qualified→bare lookup from the same two maps so
    -- [traitBoundParamOf] can resolve the impl's trait-clause names.
    traitQualifiedNameById.fold (init := {}) fun acc id qn =>
      match traitNameById[id]? with
      | some bn => acc.insert qn bn
      | none => acc
  let traitBoundParams : Array Pure.TraitBoundParam :=
    ti.generics.traitClauses.map
      (traitBoundParamOf traitNameByQualified ti.generics.types)
  let methods : Array Pure.TraitImplMethod := ti.methods.map fun m =>
    { name := m.name, body := s!"{prettyName}.{m.name}" }
  { name := prettyName
    qualifiedName := ti.itemMeta.name
    traitName := traitBare
    selfTy
    methods
    sourceSpan := ti.itemMeta.span
    typeParams := ti.generics.types
    traitBoundParams }

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
  | .fieldAccess base f =>
    .fieldAccess (rewriteCalleeNames pretty base) f
  -- M9.5p: aggregate record literals — recurse into each field value.
  | .recordLit fields =>
    .recordLit (fields.map fun (n, v) => (n, rewriteCalleeNames pretty v))
  | .matchE scr arms =>
    .matchE (rewriteCalleeNames pretty scr)
            (arms.map fun (ctor, binders, body) =>
              (ctor, binders, rewriteCalleeNames pretty body))

/-- M9.5o: rewrite `TraitClause@N::method` heads inside a `PExpr`
    body. For each `.app head args`, if `head` matches the pattern
    `TraitClause@N::method` (sanitized form `TraitClause@N.method`
    or the raw `TraitClause@N::method` from the cert), rewrite to
    `<TraitName>Inst.method` using the N-th entry of
    `traitBoundParams`. If N is out of range, leave the call
    unchanged. -/
partial def rewriteTraitClauseRefs (bounds : Array Pure.TraitBoundParam) :
    PExpr → PExpr
  | .var n => .var n
  | .lit l => .lit l
  | .app head args =>
    let parts := head.splitOn "::"
    let head' : String :=
      match parts with
      | first :: rest =>
        if first.startsWith "TraitClause@" then
          let nstr := first.drop "TraitClause@".length
          match nstr.toNat? with
          | some n =>
            match bounds[n]? with
            | some b =>
              let suffix := String.intercalate "." rest
              s!"{b.binderName}.{suffix}"
            | none => head
          | none => head
        else head
      | [] => head
    .app head' (args.map (rewriteTraitClauseRefs bounds))
  | .letIn n ty e1 e2 =>
    .letIn n ty (rewriteTraitClauseRefs bounds e1) (rewriteTraitClauseRefs bounds e2)
  | .ok e => .ok (rewriteTraitClauseRefs bounds e)
  | .ifThenElse c t e =>
    .ifThenElse (rewriteTraitClauseRefs bounds c)
                (rewriteTraitClauseRefs bounds t)
                (rewriteTraitClauseRefs bounds e)
  | .tuple args => .tuple (args.map (rewriteTraitClauseRefs bounds))
  | .lam ps body => .lam ps (rewriteTraitClauseRefs bounds body)
  | .letPure n ty e1 e2 =>
    .letPure n ty (rewriteTraitClauseRefs bounds e1) (rewriteTraitClauseRefs bounds e2)
  | .letPat ps ty e1 e2 =>
    .letPat ps ty (rewriteTraitClauseRefs bounds e1) (rewriteTraitClauseRefs bounds e2)
  | .structUpdate base f v =>
    .structUpdate (rewriteTraitClauseRefs bounds base) f (rewriteTraitClauseRefs bounds v)
  | .fieldAccess base f =>
    .fieldAccess (rewriteTraitClauseRefs bounds base) f
  -- M9.5p: aggregate record literals — recurse into each field value.
  | .recordLit fields =>
    .recordLit (fields.map fun (n, v) => (n, rewriteTraitClauseRefs bounds v))
  | .matchE scr arms =>
    .matchE (rewriteTraitClauseRefs bounds scr)
            (arms.map fun (ctor, binders, body) =>
              (ctor, binders, rewriteTraitClauseRefs bounds body))

/-- Translate a whole crate cert. Per-function metadata (signature,
    source span) is taken from the cert's `FunCert`, while the
    behavioural trace comes from the replayer's `CheckedTrace`.

    M9.5b: cert `type_decls` lift into `StructDecl`s; `LeanEmit`
    emits them before functions in the same namespace.

    M12.1: functions whose cert contains an `EvLoopInv` / `EvLoopEnd`
    pair are translated via `translateLoopFun`, which emits three
    decls (body / wrapper / top-level). Non-loop functions go through
    the M10 `translateFun` (one decl). -/
def translateCrate (cc : CrateCert) (strictJoin : Bool := false)
    (useLlbcProgram : Bool := true) :
    Except String TranslatedCrate := do
  let traces ← replayCrate cc strictJoin
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
  -- M9.7k: `useLlbcProgram` switches the TypeDeclMap + StructDecl /
  -- EnumDecl source between the flat cert path (`cc.typeDecls`) and
  -- the structured `cc.llbcProgram` path. When the flag is set but
  -- the LLBC program is empty (v2 cert), fall back to the flat path
  -- so the parity test can flip the flag uniformly on the sweep.
  let useStructured := useLlbcProgram ∧ !cc.llbcProgram.typeDecls.isEmpty
  let tdm :=
    if useStructured then buildTypeDeclMapFromLlbc cc
    else buildTypeDeclMap cc
  let structs : Array StructDecl :=
    if useStructured then
      cc.llbcProgram.typeDecls.filterMap (structDeclOfLlbcTypeDecl tdm crateName)
    else
      cc.typeDecls.filterMap (structDeclOfTypeDecl tdm crateName)
  let enums : Array EnumDecl :=
    if useStructured then
      cc.llbcProgram.typeDecls.filterMap (enumDeclOfLlbcTypeDecl tdm crateName)
    else
      cc.typeDecls.filterMap (enumDeclOfTypeDecl tdm crateName)
  -- M9.5l / M9.7l: lift trait decls + impls into Pure IR. We also
  -- build a `traitNameById` lookup so impls can resolve their target
  -- trait by id. The structured path (M9.7l) sources the entries
  -- from `cc.llbcProgram.traitDecls` / `.traitImpls`, deriving the
  -- bare trait name from `itemMeta.name`'s last `::`-segment and
  -- recomputing the standard-backend impl-pretty-name shape from
  -- structured info.
  let useStructuredTraits :=
    useLlbcProgram ∧ (!cc.llbcProgram.traitDecls.isEmpty ∨ !cc.llbcProgram.traitImpls.isEmpty)
  let traitDecls : Array Pure.TraitDecl :=
    if useStructuredTraits then
      cc.llbcProgram.traitDecls.map (traitDeclOfLlbcTraitDecl tdm crateName)
    else
      cc.traitDecls.map (traitDeclOfCert tdm crateName)
  let traitNameById : Std.HashMap Nat String :=
    if useStructuredTraits then
      cc.llbcProgram.traitDecls.foldl (init := {}) fun acc td =>
        acc.insert td.id (bareNameOfQualified td.itemMeta.name)
    else
      cc.traitDecls.foldl (init := {}) fun acc td =>
        acc.insert td.id td.name
  -- M9.5o: parallel `qualified_name → bare name` table for resolving
  -- trait clauses (which carry qualified names) to the bare names
  -- used in the emitted Lean source.
  let traitNameByQualified : Std.HashMap String String :=
    if useStructuredTraits then
      cc.llbcProgram.traitDecls.foldl (init := {}) fun acc td =>
        acc.insert td.itemMeta.name (bareNameOfQualified td.itemMeta.name)
    else
      cc.traitDecls.foldl (init := {}) fun acc td =>
        acc.insert td.qualifiedName td.name
  let traitQualifiedNameById : Std.HashMap Nat String :=
    -- Only used by the structured trait-impl pretty-name computation
    -- (which needs the trait's qualified name for `crateSegmentOf`).
    if useStructuredTraits then
      cc.llbcProgram.traitDecls.foldl (init := {}) fun acc td =>
        acc.insert td.id td.itemMeta.name
    else {}
  let traitImpls : Array Pure.TraitImpl :=
    if useStructuredTraits then
      cc.llbcProgram.traitImpls.map
        (traitImplOfLlbcTraitImpl tdm traitNameById traitQualifiedNameById crateName)
    else
      cc.traitImpls.map (traitImplOfCert tdm traitNameById traitNameByQualified crateName)
  -- M9.5l: build a per-fn-id → pretty-name table so the Forward
  -- translator can rewrite EvCall `fn_name` to its standard-backend
  -- shape (e.g. `traits_basic::{...}::value` →
  -- `Tag.Insts.Traits_basicNumeric.value`).
  let fnPrettyByName : Std.HashMap String String :=
    cc.functions.foldl (init := {}) fun acc f =>
      match f.prettyName with
      | some n => acc.insert f.fnName n
      | none => acc
  -- M9.5o: build a `fn_name → "<TraitName>.<methodName>.default"` table
  -- for default-method body functions. The standard backend renders
  -- these with a `.default` suffix and (depending on the default's
  -- generics) an explicit `(Self : Type)` binder. The cert
  -- identifies default methods via `TraitMethodDecl.hasDefault`.
  -- The fn_name pattern for a default body is
  -- `<crate>::<Trait>::<method>` (standalone fun_decl emitted by
  -- Charon for the default body).
  let defaultRenameByName : Std.HashMap String String :=
    if useStructuredTraits then
      cc.llbcProgram.traitDecls.foldl (init := {}) fun acc td =>
        td.methods.foldl (init := acc) fun acc m =>
          if m.hasDefault then
            let bare := bareNameOfQualified td.itemMeta.name
            let fnQual := s!"{td.itemMeta.name}::{m.name}"
            let pretty := s!"{bare}.{m.name}.default"
            acc.insert fnQual pretty
          else acc
    else
      cc.traitDecls.foldl (init := {}) fun acc td =>
        td.methods.foldl (init := acc) fun acc m =>
          if m.hasDefault then
            -- The default body's standalone fun_name is
            -- `<traitQualifiedName>::<methodName>`. Map it to
            -- `<bareTraitName>.<methodName>.default`.
            let fnQual := s!"{td.qualifiedName}::{m.name}"
            let pretty := s!"{td.name}.{m.name}.default"
            acc.insert fnQual pretty
          else acc
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
  --
  -- M9.5o: also rewrite default-body callsites. EvCall traces that
  -- reference a trait's default body's fun_name (the standalone
  -- `Trait::method` form) need to point to `<Trait>.<method>.default`.
  -- We merge the default rename map into the same callee-rewrite pass.
  let allCalleeRenames : Std.HashMap String String :=
    defaultRenameByName.fold (init := fnPrettyByName) fun acc k v => acc.insert k v
  -- M9.5o: attach `traitBoundParams` to each decl by translating
  -- the cert's `csig_trait_clauses` against the decl's typeParams.
  -- For trait-impl method bodies, the impl-level type params are
  -- inherited from the trait_impl entry (a body fn's own cert
  -- signature carries the same type-params + clauses, since Charon
  -- copies them to the standalone fun_decl).
  decls := decls.map fun d =>
    let body := rewriteCalleeNames allCalleeRenames d.body
    -- M9.7l: structured-source path reads the function's trait
    -- clauses from `cc.llbcProgram.funDecls[matching].signature.generics.traitClauses`
    -- instead of the flat `f.signature.traitClauses`. Both carry the
    -- same `Array TraitClause` shape — TraitClause is shared between
    -- the two schemas.
    let traitBoundParams : Array Pure.TraitBoundParam :=
      if useStructuredTraits then
        match cc.llbcProgram.funDecls.find? (·.itemMeta.name == d.qualifiedName) with
        | some fd =>
          fd.signature.generics.traitClauses.map
            (traitBoundParamOf traitNameByQualified d.typeParams)
        | none => #[]
      else
        match cc.functions.find? (·.fnName == d.qualifiedName) with
        | some f =>
          f.signature.traitClauses.map
            (traitBoundParamOf traitNameByQualified d.typeParams)
        | none => #[]
    -- M9.5o: a body that references `TraitClause@N::method` resolves
    -- against the function's clauses — for now we rewrite to
    -- `<TraitName>Inst.method` using the first matching binder
    -- (single-clause cases). Multi-clause disambiguation is M9.5p+.
    let body2 :=
      if traitBoundParams.isEmpty then body
      else rewriteTraitClauseRefs traitBoundParams body
    -- If this decl's *own* function name maps to a pretty name,
    -- override its `name` (which the LeanEmit uses as the `def`
    -- header). The impl-method body decl is the only case where
    -- this triggers in M9.5l.
    -- M9.5o: extend to also rename default-method bodies.
    let nameOverride : Option String :=
      match fnPrettyByName[d.qualifiedName]? with
      | some n => some n
      | none => defaultRenameByName[d.qualifiedName]?
    let isDefault : Bool := defaultRenameByName.contains d.qualifiedName
    let d := match nameOverride with
      | some n => { d with name := n, body := body2 }
      | none => { d with body := body2 }
    -- M9.5o: when this decl is a default-method body and it carries
    -- no trait-clause obligations of its own (i.e. the default body
    -- doesn't reference `TraitClause@N::method`), the standard
    -- backend emits the `Self` binder as an *explicit* `(Self :
    -- Type)` rather than the implicit `{Self : Type}`. We model that
    -- by clearing `typeParams` and inserting a value-level `Param`
    -- at the head of `params`. (When trait-clause obligations ARE
    -- present, the implicit-Self + TraitBoundParam shape is
    -- correct.) Detect via the cert's hasDefault flag (via the
    -- defaultRenameByName key) AND the absence of trait clauses.
    if isDefault && traitBoundParams.isEmpty then
      let explicitSelfParams : Array Param :=
        d.typeParams.map fun n => { name := n, ty := .adt "Type" #[] }
      { d with
        typeParams := #[]
        params := explicitSelfParams ++ d.params
        traitBoundParams := #[] }
    else
      { d with traitBoundParams }
  return { decls, structs, enums, traitDecls, traitImpls }

end AeneasCheck.Translate
