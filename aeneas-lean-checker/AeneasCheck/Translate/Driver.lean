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

/-- M9.7k / M9.7o-E5a: build the [TypeDeclMap] used by the
    per-function translator from `cc.llbcProgram.typeDecls`.

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

/-- M9.7k / M9.7o-E5a: structured-source twin (now sole path) of the
    old `structDeclOfTypeDecl`. Lifts an `LlbcTypeDecl` (when its kind
    is `struct`) into a `StructDecl`,
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

/-- M9.7l / M9.7o-E5a: lift an `LlbcTraitDecl` into a `Pure.TraitDecl`.
    Method signatures are
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

/-- M9.7l / M9.7o-E5a: lift an `LlbcTraitImpl` into a `Pure.TraitImpl`.
    The standard-backend impl-pretty-name shape is recomputed from the
    structured info:

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
  | .structUpdate base f v adtName =>
    .structUpdate (rewriteCalleeNames pretty base) f (rewriteCalleeNames pretty v) adtName
  | .fieldAccess base f =>
    .fieldAccess (rewriteCalleeNames pretty base) f
  -- M9.5p: aggregate record literals — recurse into each field value.
  | .recordLit fields adtName =>
    .recordLit (fields.map fun (n, v) => (n, rewriteCalleeNames pretty v)) adtName
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
  | .structUpdate base f v adtName =>
    .structUpdate (rewriteTraitClauseRefs bounds base) f (rewriteTraitClauseRefs bounds v) adtName
  | .fieldAccess base f =>
    .fieldAccess (rewriteTraitClauseRefs bounds base) f
  -- M9.5p: aggregate record literals — recurse into each field value.
  | .recordLit fields adtName =>
    .recordLit (fields.map fun (n, v) => (n, rewriteTraitClauseRefs bounds v)) adtName
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
def translateCrate (cc : CrateCert) (strictJoin : Bool := false) :
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
  -- M9.7o-E5a: structured (LlbcProgram-sourced) path is now the only
  -- path. Cert v2's flat `typeDecls` / `traitDecls` / `traitImpls`
  -- arrays were dropped from `CrateCert` in this commit; the JSON
  -- parser now rejects v1 / v2 certs at parse time, so by the time
  -- `translateCrate` runs the embedded LLBC program is fully
  -- populated.
  let tdm := buildTypeDeclMapFromLlbc cc
  let structs : Array StructDecl :=
    cc.llbcProgram.typeDecls.filterMap (structDeclOfLlbcTypeDecl tdm crateName)
  let enums : Array EnumDecl :=
    cc.llbcProgram.typeDecls.filterMap (enumDeclOfLlbcTypeDecl tdm crateName)
  -- M9.7l: build the `traitNameById` / `traitNameByQualified` lookups
  -- from `cc.llbcProgram.traitDecls`. Lifting + impl pretty-name
  -- computation come from the LlbcTraitDecl / LlbcTraitImpl shapes.
  let traitDecls : Array Pure.TraitDecl :=
    cc.llbcProgram.traitDecls.map (traitDeclOfLlbcTraitDecl tdm crateName)
  let traitNameById : Std.HashMap Nat String :=
    cc.llbcProgram.traitDecls.foldl (init := {}) fun acc td =>
      acc.insert td.id (bareNameOfQualified td.itemMeta.name)
  let traitNameByQualified : Std.HashMap String String :=
    cc.llbcProgram.traitDecls.foldl (init := {}) fun acc td =>
      acc.insert td.itemMeta.name (bareNameOfQualified td.itemMeta.name)
  let traitQualifiedNameById : Std.HashMap Nat String :=
    cc.llbcProgram.traitDecls.foldl (init := {}) fun acc td =>
      acc.insert td.id td.itemMeta.name
  let traitImpls : Array Pure.TraitImpl :=
    cc.llbcProgram.traitImpls.map
      (traitImplOfLlbcTraitImpl tdm traitNameById traitQualifiedNameById crateName)
  -- M9.5l: build a per-fn-id → pretty-name table so the Forward
  -- translator can rewrite EvCall `fn_name` to its standard-backend
  -- shape (e.g. `traits_basic::{...}::value` →
  -- `Tag.Insts.Traits_basicNumeric.value`).
  let fnPrettyByName : Std.HashMap String String :=
    cc.functions.foldl (init := {}) fun acc f =>
      match f.prettyName with
      | some n => acc.insert f.fnName n
      | none => acc
  -- M9.5o / M9.7l: build a `fn_name → "<TraitName>.<methodName>.default"`
  -- table for default-method body functions, sourced from
  -- `cc.llbcProgram.traitDecls`.
  let defaultRenameByName : Std.HashMap String String :=
    cc.llbcProgram.traitDecls.foldl (init := {}) fun acc td =>
      td.methods.foldl (init := acc) fun acc m =>
        if m.hasDefault then
          let bare := bareNameOfQualified td.itemMeta.name
          let fnQual := s!"{td.itemMeta.name}::{m.name}"
          let pretty := s!"{bare}.{m.name}.default"
          acc.insert fnQual pretty
        else acc
  -- M9.7o-E5b: per-function `LlbcFunDecl` lookup table, keyed by
  -- `fnId`. Used both by [translateFunWith] (so the walker has
  -- structured signature + per-local typing) and by the trait-bound
  -- enrichment pass below. A synthetic empty `LlbcFunDecl` is used
  -- as fallback for any cert function with no matching LLBC entry —
  -- shouldn't happen for a consistent crate.
  let lfById : Std.HashMap Nat Raw.LlbcFunDecl :=
    cc.llbcProgram.funDecls.foldl (init := {}) fun acc lf =>
      acc.insert lf.id lf
  let lookupLf (f : Raw.FunCert) : Raw.LlbcFunDecl :=
    lfById.getD f.fnId { id := f.fnId, itemMeta := { name := f.fnName } }
  let mut decls : Array Decl := #[]
  for i in [0:cc.functions.size] do
    let f := cc.functions[i]!
    let lf := lookupLf f
    match translateLoopFun f lf with
    | some loopDecls => decls := decls ++ loopDecls
    | none => decls := decls.push (translateFunWith tdm f lf traces[i]!)
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
  -- M9.5o / M9.7l: attach `traitBoundParams` to each decl by reading
  -- the function's trait clauses from
  -- `cc.llbcProgram.funDecls[matching].signature.generics.traitClauses`.
  decls := decls.map fun d =>
    let body := rewriteCalleeNames allCalleeRenames d.body
    let traitBoundParams : Array Pure.TraitBoundParam :=
      match cc.llbcProgram.funDecls.find? (·.itemMeta.name == d.qualifiedName) with
      | some fd =>
        fd.signature.generics.traitClauses.map
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
