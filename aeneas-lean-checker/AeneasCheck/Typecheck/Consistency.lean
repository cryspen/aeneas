import Std.Data.HashMap
import AeneasCheck.Raw.CertEvent
import AeneasCheck.Raw.LLBCProgram

/-!
# M9.7h — Cert v3 structural consistency (Level S)

This module pairs the cert's pre-existing "flat" metadata
(`typeDecls`, `traitDecls`, `traitImpls`, per-function signatures,
`fnId`/`fnName`) against the embedded `llbcProgram` and rejects the
cert at parse-time when the two halves disagree on something
structural — a name, a kind, an item count, or a cross-reference id.

The check is the M9.7h piece of the cert v3 redesign (plan §C.1).
The level-S checks here cover what the plan calls "structural
agreement"; per-event referential validity (Level R) is the M9.7i/j
follow-up that extends this same file.

When `cc.fmtVersion < 3` (cert v1 / v2) the check is a no-op, since
the embedded `llbcProgram` is `LlbcProgram.empty` and there is no
second half to validate against. Existing in-tree v2 fixtures keep
passing unchanged.
-/

namespace AeneasCheck.Typecheck.Consistency

open AeneasCheck.Raw

/-- One structural inconsistency. `context` identifies which part of
    the cert produced the error (e.g. `"typeDecls[3]"`,
    `"functions[5].events[12]"`); `msg` describes the disagreement. -/
structure ConsErr where
  context : String
  msg : String
  deriving Repr

def ConsErr.toString (e : ConsErr) : String :=
  s!"[{e.context}] {e.msg}"

instance : ToString ConsErr := ⟨ConsErr.toString⟩

abbrev CR α := Except (List ConsErr) α

private def err (context msg : String) : ConsErr := { context, msg }

/-! ## Id-indexed lookup tables

The cert's flat metadata is pairwise indexed by *id*, not by array
position, because `cc.typeDecls` may skip ids that Charon emitted as
opaque/global decls (and similarly for `cc.functions`). Build a
HashMap once per check and pair via lookup. -/

private def buildTypeDeclMap (ps : Array LlbcTypeDecl) :
    Std.HashMap Nat LlbcTypeDecl :=
  ps.foldl (init := {}) fun m d => m.insert d.id d

private def buildFunDeclMap (ps : Array LlbcFunDecl) :
    Std.HashMap Nat LlbcFunDecl :=
  ps.foldl (init := {}) fun m d => m.insert d.id d

private def buildTraitDeclMap (ps : Array LlbcTraitDecl) :
    Std.HashMap Nat LlbcTraitDecl :=
  ps.foldl (init := {}) fun m d => m.insert d.id d

private def buildTraitImplMap (ps : Array LlbcTraitImpl) :
    Std.HashMap Nat LlbcTraitImpl :=
  ps.foldl (init := {}) fun m d => m.insert d.id d

/-! ## Type-decl pairing

`cc.typeDecls[i].qualifiedName` (an M9.5n addition) is the
crate-prefixed name used as the pretty-printer key on the OCaml side.
`llbcProgram.type_decls[j].itemMeta.name` is the same key (Charon's
`item_meta.name`). They must agree when ids match.

Struct / Enum / Opaque kinds are paired symmetrically. Charon's
`Union` and `TAlias` kinds (not present in M9.5b-era cc.typeDecls)
land on the flat side as `.opaque`; we accept that as a downgrade. -/

private def fieldNamesMatch (cs : Array CertField)
    (ls : Array LlbcField) : Bool :=
  cs.size = ls.size &&
  (Array.zip cs ls).all fun (c, l) => c.name = l.name

private def variantNamesMatch (cs : Array CertVariant)
    (ls : Array LlbcVariant) : Bool :=
  cs.size = ls.size &&
  (Array.zip cs ls).all fun (c, l) =>
    c.name = l.name && fieldNamesMatch c.fields l.fields

private def checkTypeDeclPair (idx : Nat) (c : TypeDecl)
    (l : LlbcTypeDecl) : List ConsErr := Id.run do
  let ctx := s!"typeDecls[{idx}] id={c.id}"
  let mut errs : List ConsErr := []
  -- Qualified name agreement (qualifiedName is the M9.5n field on
  -- the flat side; absent in pre-M9.5n certs but those are all v2
  -- and short-circuit upstream).
  if c.qualifiedName ≠ "" && c.qualifiedName ≠ l.itemMeta.name then
    errs := errs ++ [err ctx s!"qualified name disagrees: cc={repr c.qualifiedName} lp={repr l.itemMeta.name}"]
  -- Kind agreement.
  match c.kind, l.kind with
  | .struct cfields, .struct lfields =>
    if cfields.size ≠ lfields.size then
      errs := errs ++ [err ctx s!"struct field count disagrees: cc={cfields.size} lp={lfields.size}"]
    else if !fieldNamesMatch cfields lfields then
      errs := errs ++ [err ctx "struct field names disagree"]
  | .enum cvars, .enum lvars =>
    if cvars.size ≠ lvars.size then
      errs := errs ++ [err ctx s!"enum variant count disagrees: cc={cvars.size} lp={lvars.size}"]
    else if !variantNamesMatch cvars lvars then
      errs := errs ++ [err ctx "enum variant / field names disagree"]
  | .opaque, .opaque => pure ()
  | .opaque, .union _ => pure ()  -- flat side falls back to .opaque for unions
  | .opaque, .tAlias _ => pure () -- and for type aliases
  | _, _ =>
    errs := errs ++ [err ctx s!"kind disagrees (cc and lp record different shapes)"]
  return errs

def checkTypeDecls (ccDecls : Array TypeDecl)
    (lpDecls : Array LlbcTypeDecl) : CR Unit := do
  let m := buildTypeDeclMap lpDecls
  let mut errs : List ConsErr := []
  for i in [0 : ccDecls.size] do
    let c := ccDecls[i]!
    match m.get? c.id with
    | none =>
      errs := errs ++ [err s!"typeDecls[{i}]"
        s!"id {c.id} ({c.qualifiedName}) is missing from llbcProgram.type_decls"]
    | some l =>
      errs := errs ++ checkTypeDeclPair i c l
  if errs.isEmpty then .ok () else .error errs

/-! ## Function-cert pairing

For each `cc.functions[i]`, the cert exposes `fnId` (a `FunDeclId`)
and `fnName` (the qualified callee name). The matching
`llbcProgram.fun_decls[j]` shares the id and carries the same name
in `itemMeta.name`. We additionally check input arity. -/

private def checkFunSigArity (ctx : String) (c : FnSignature)
    (l : LlbcSignature) : List ConsErr := Id.run do
  let mut errs : List ConsErr := []
  if c.inputs.size ≠ l.inputs.size then
    errs := errs ++ [err ctx s!"signature input arity disagrees: cc={c.inputs.size} lp={l.inputs.size}"]
  return errs

private def checkFunPair (idx : Nat) (c : FunCert) (l : LlbcFunDecl) :
    List ConsErr := Id.run do
  let ctx := s!"functions[{idx}] id={c.fnId} '{c.fnName}'"
  let mut errs : List ConsErr := []
  if c.fnName ≠ l.itemMeta.name then
    errs := errs ++ [err ctx s!"fnName disagrees: cc={repr c.fnName} lp={repr l.itemMeta.name}"]
  errs := errs ++ checkFunSigArity ctx c.signature l.signature
  return errs

def checkFunctions (ccFns : Array FunCert)
    (lpFns : Array LlbcFunDecl) : CR Unit := do
  let m := buildFunDeclMap lpFns
  let mut errs : List ConsErr := []
  for i in [0 : ccFns.size] do
    let c := ccFns[i]!
    match m.get? c.fnId with
    | none =>
      errs := errs ++ [err s!"functions[{i}]"
        s!"fnId {c.fnId} ('{c.fnName}') is missing from llbcProgram.fun_decls"]
    | some l =>
      errs := errs ++ checkFunPair i c l
  if errs.isEmpty then .ok () else .error errs

/-! ## Trait-decl pairing -/

private def checkTraitDeclPair (idx : Nat) (c : TraitDecl)
    (l : LlbcTraitDecl) : List ConsErr := Id.run do
  let ctx := s!"traitDecls[{idx}] id={c.id}"
  let mut errs : List ConsErr := []
  if c.qualifiedName ≠ l.itemMeta.name then
    errs := errs ++ [err ctx s!"qualified name disagrees: cc={repr c.qualifiedName} lp={repr l.itemMeta.name}"]
  if c.methods.size ≠ l.methods.size then
    errs := errs ++ [err ctx s!"method count disagrees: cc={c.methods.size} lp={l.methods.size}"]
  else
    for k in [0 : c.methods.size] do
      let cm := c.methods[k]!
      let lm := l.methods[k]!
      if cm.name ≠ lm.name then
        errs := errs ++ [err ctx s!"method[{k}] name disagrees: cc={repr cm.name} lp={repr lm.name}"]
  return errs

def checkTraitDecls (ccDecls : Array TraitDecl)
    (lpDecls : Array LlbcTraitDecl) : CR Unit := do
  let m := buildTraitDeclMap lpDecls
  let mut errs : List ConsErr := []
  for i in [0 : ccDecls.size] do
    let c := ccDecls[i]!
    match m.get? c.id with
    | none =>
      errs := errs ++ [err s!"traitDecls[{i}]"
        s!"id {c.id} ({c.qualifiedName}) is missing from llbcProgram.trait_decls"]
    | some l =>
      errs := errs ++ checkTraitDeclPair i c l
  if errs.isEmpty then .ok () else .error errs

/-! ## Trait-impl pairing -/

private def checkTraitImplPair (idx : Nat) (c : TraitImpl)
    (l : LlbcTraitImpl) : List ConsErr := Id.run do
  let ctx := s!"traitImpls[{idx}] id={c.id}"
  let mut errs : List ConsErr := []
  if c.qualifiedName ≠ l.itemMeta.name then
    errs := errs ++ [err ctx s!"qualified name disagrees: cc={repr c.qualifiedName} lp={repr l.itemMeta.name}"]
  if c.traitDeclId ≠ l.traitDeclId then
    errs := errs ++ [err ctx s!"traitDeclId disagrees: cc={c.traitDeclId} lp={l.traitDeclId}"]
  if c.methods.size ≠ l.methods.size then
    errs := errs ++ [err ctx s!"method count disagrees: cc={c.methods.size} lp={l.methods.size}"]
  else
    for k in [0 : c.methods.size] do
      let cm := c.methods[k]!
      let lm := l.methods[k]!
      if cm.name ≠ lm.name then
        errs := errs ++ [err ctx s!"method[{k}] name disagrees: cc={repr cm.name} lp={repr lm.name}"]
      if cm.fnId ≠ lm.fnId then
        errs := errs ++ [err ctx s!"method[{k}] fnId disagrees: cc={cm.fnId} lp={lm.fnId}"]
  return errs

def checkTraitImpls (ccImpls : Array TraitImpl)
    (lpImpls : Array LlbcTraitImpl) : CR Unit := do
  let m := buildTraitImplMap lpImpls
  let mut errs : List ConsErr := []
  for i in [0 : ccImpls.size] do
    let c := ccImpls[i]!
    match m.get? c.id with
    | none =>
      errs := errs ++ [err s!"traitImpls[{i}]"
        s!"id {c.id} ({c.qualifiedName}) is missing from llbcProgram.trait_impls"]
    | some l =>
      errs := errs ++ checkTraitImplPair i c l
  if errs.isEmpty then .ok () else .error errs

/-! ## Event reference checks

Per-event referential validity *against the embedded LLBC's id sets*
and *against the current function's declared locals*. Phase C
(M9.7h) shipped the id-set checks; Phase D (M9.7i / j) adds the
per-function place / arg-arity checks.

Covered here (M9.7h + M9.7i):

* `EvCall.fn` — the callee's `FunDeclId` (placeholder 0 accepted).
* `EvCall` argument count vs the resolved callee's input arity
  (when the callee name resolves to an `llbcProgram.fun_decls`
  entry; built-in / trait-method calls are accepted).
* `EvMatchArm.adtId` / `variantId` — the (typedecl, variant)
  being matched.
* Per-event place-root locals are in bounds of the function's
  declared `localsTypes`.

Deferred to M9.7j: full projection-path validity against the
declared local type, control-flow well-nestedness (EvJoin /
EvLoopInv / EvLoopEnd pairing), `EvEndAbs` lifecycle. -/

private def lookupVariant (td : LlbcTypeDecl) (vid : Nat) :
    Option LlbcVariant :=
  match td.kind with
  | .enum vs => vs.find? fun v => v.id = vid
  | _ => none

private def fnByName (lp : LlbcProgram) :
    Std.HashMap String LlbcFunDecl :=
  lp.funDecls.foldl (init := {}) fun m d => m.insert d.itemMeta.name d

/-- M9.7i: per-event places whose root local must be in bounds. The
    list isn't exhaustive — we surface only the explicit Place
    fields the cert constructors carry, not the SymExpr-nested
    places (those are reached transitively via the dst/src/place
    field, plus event-specific carrier fields handled below). -/
private def eventPlaceRefs : Event → Array (String × Place)
  | .mutBorrow _ p _ _ => #[("mutBorrow.place", p)]
  | .sharedBorrow _ _ p _ => #[("sharedBorrow.place", p)]
  | .assign d _ => #[("assign.dst", d)]
  | .move s d => #[("move.src", s), ("move.dst", d)]
  | .copy s d => #[("copy.src", s), ("copy.dst", d)]
  | .reborrow _ _ p _ _ => #[("reborrow.place", p)]
  | .call _ _ _ _ d _ _ => #[("call.dst", d)]
  | .binop _ _ _ d => #[("binop.dst", d)]
  | .proj _ p _ => #[("proj.place", p)]
  | _ => #[]

/-- M9.7i: collect the (label, place) pairs that a `SymExpr` reaches.
    Used to validate that places baked into the cert's symbolic-
    expression terms (move/copy) also point at declared locals. -/
private partial def symExprPlaceRefs : SymExpr → Array (String × Place)
  | .symCopy p => #[("symCopy", p)]
  | .symMove p => #[("symMove", p)]
  | .symVariant _ _ _ fs =>
    fs.foldl (init := #[]) fun acc f => acc ++ symExprPlaceRefs f
  | .symTuple fs =>
    fs.foldl (init := #[]) fun acc f => acc ++ symExprPlaceRefs f
  | .symRecord _ fs =>
    fs.foldl (init := #[]) fun acc (_, f) => acc ++ symExprPlaceRefs f
  | _ => #[]

/-- M9.7i: places that appear inside an `Event`'s rhs/args/witness
    `SymExpr` fields (not the top-level Place fields covered by
    `eventPlaceRefs`). -/
private def eventSymExprPlaces : Event → Array (String × Place)
  | .assign _ rhs => symExprPlaceRefs rhs
  | .endBorrow _ r => symExprPlaceRefs r.givenBack
  | .assert c _ => symExprPlaceRefs c
  | .binop _ l r _ => symExprPlaceRefs l ++ symExprPlaceRefs r
  | .call _ _ _ args _ _ _ =>
    args.foldl (init := #[]) fun acc a => acc ++ symExprPlaceRefs a
  | .endAbs _ vs _ _ =>
    vs.foldl (init := #[]) fun acc v => acc ++ symExprPlaceRefs v
  | .matchArm s _ _ _ => symExprPlaceRefs s
  | _ => #[]

/-- M9.7i: emit an error if `p.local_` is out of bounds against the
    function's declared local count. Empty `numLocals` (e.g. when
    the LLBC fun_decl has `body = None`) suppresses the check, since
    we can't validate without a known local table. -/
private def checkPlaceRoot (ctx : String) (label : String)
    (numLocals : Nat) (p : Place) : List ConsErr := Id.run do
  if numLocals = 0 then return []
  if p.local_ < numLocals then return []
  return [err ctx s!"{label}: local {p.local_} out of bounds (function has {numLocals} declared locals)"]

private def checkEventRefs1 (funCtx : String) (numLocals : Nat) (eIdx : Nat)
    (ev : Event)
    (tyMap : Std.HashMap Nat LlbcTypeDecl)
    (fnMap : Std.HashMap Nat LlbcFunDecl)
    (fnByName : Std.HashMap String LlbcFunDecl) : List ConsErr := Id.run do
  let ctx := s!"{funCtx}.events[{eIdx}]"
  let mut errs : List ConsErr := []
  -- M9.7i: place-root local-id bounds (covers all events that
  -- carry an explicit Place; SymExpr-nested places are walked
  -- below).
  for (label, p) in eventPlaceRefs ev do
    errs := errs ++ checkPlaceRoot ctx label numLocals p
  for (label, p) in eventSymExprPlaces ev do
    errs := errs ++ checkPlaceRoot ctx label numLocals p
  -- M9.7h + M9.7i: per-event id-set checks.
  match ev with
  | .call fnId _callId fnName args _dst _regionAbs _absSig =>
    -- M9.7h: the OCaml side (`src/interp/InterpStatements.ml`)
    -- emits `fn = FunDeclId 0` as a placeholder for builtin calls
    -- (`FBuiltin _`) and trait-method dispatches (`TraitMethod _`).
    -- The semantic callee for those cases lives in `fn_name` only.
    -- We can't structurally distinguish "real call to fn 0" from
    -- the placeholder, so a placeholder id is accepted; non-zero
    -- ids must exist in `llbcProgram.fun_decls`. Per-callee name
    -- agreement is *not* checked here because Charon's caller-side
    -- pretty-printer (`fn_ptr_kind_to_string`) emits `T@K`-style
    -- type-variable references and `'K` lifetimes, while the
    -- `itemMeta.name` on the decl-side uses surface
    -- type-parameter / lifetime names — the two strings agree
    -- structurally but differ literally. A normalised name
    -- comparison is in scope for Phase D / E once the structured
    -- callee path lands.
    if fnId ≠ 0 then
      if !fnMap.contains fnId then
        errs := errs ++ [err ctx
          s!"EvCall.fn={fnId} ('{fnName}') is missing from llbcProgram.fun_decls"]
    -- M9.7i: arg-count vs callee arity, when the callee name
    -- resolves to a regular fun_decl. Built-in / trait-method
    -- calls don't have a corresponding fun_decl entry in
    -- llbcProgram and are silently accepted (no arity info).
    match fnByName.get? fnName with
    | none => pure ()  -- builtin / trait-method
    | some callee =>
      let expected := callee.signature.inputs.size
      if args.size ≠ expected then
        errs := errs ++ [err ctx
          s!"EvCall '{fnName}' arg-count disagrees: got {args.size} expected {expected}"]
  | .matchArm _scr adtId variantId variantName =>
    match tyMap.get? adtId with
    | none =>
      errs := errs ++ [err ctx
        s!"EvMatchArm.adtId={adtId} is missing from llbcProgram.type_decls"]
    | some td =>
      match lookupVariant td variantId with
      | none =>
        errs := errs ++ [err ctx
          s!"EvMatchArm: variant id {variantId} not found in type_decls[{adtId}] ({td.itemMeta.name})"]
      | some v =>
        if variantName ≠ v.name then
          errs := errs ++ [err ctx
            s!"EvMatchArm variant name disagrees: cc={repr variantName} lp={repr v.name}"]
  | _ => pure ()
  return errs

def checkEventRefs (ccFns : Array FunCert) (lp : LlbcProgram) : CR Unit := do
  let tyMap := buildTypeDeclMap lp.typeDecls
  let fnMap := buildFunDeclMap lp.funDecls
  let nameMap := fnByName lp
  let mut errs : List ConsErr := []
  for i in [0 : ccFns.size] do
    let f := ccFns[i]!
    let funCtx := s!"functions[{i}] id={f.fnId}"
    -- M9.7i: local-id bounds come from the LLBC fun_decl's
    -- `localsTypes`. When the cert references a function not in
    -- the LLBC program (builtin / opaque), numLocals = 0 and the
    -- bounds check is suppressed.
    let numLocals : Nat :=
      match fnMap.get? f.fnId with
      | some lp => lp.localsTypes.size
      | none => 0
    for j in [0 : f.events.size] do
      let ev := f.events[j]!
      errs := errs ++ checkEventRefs1 funCtx numLocals j ev tyMap fnMap nameMap
  if errs.isEmpty then .ok () else .error errs

/-! ## Top-level driver -/

/-- Run the full Level-S structural consistency check against `cc`.
    No-op when `cc.fmtVersion < 3` (the embedded `llbcProgram` is
    `LlbcProgram.empty` under cert v1 / v2 — back-compat).

    Aggregates errors from every sub-check so a single mis-emit
    surfaces all the divergences at once instead of one at a time. -/
def checkLlbcVsCert (cc : CrateCert) : CR Unit := do
  if cc.fmtVersion < 3 then
    return ()
  let lp := cc.llbcProgram
  let mut errs : List ConsErr := []
  match checkTypeDecls cc.typeDecls lp.typeDecls with
  | .ok _ => pure ()
  | .error es => errs := errs ++ es
  match checkFunctions cc.functions lp.funDecls with
  | .ok _ => pure ()
  | .error es => errs := errs ++ es
  match checkTraitDecls cc.traitDecls lp.traitDecls with
  | .ok _ => pure ()
  | .error es => errs := errs ++ es
  match checkTraitImpls cc.traitImpls lp.traitImpls with
  | .ok _ => pure ()
  | .error es => errs := errs ++ es
  match checkEventRefs cc.functions lp with
  | .ok _ => pure ()
  | .error es => errs := errs ++ es
  if errs.isEmpty then .ok () else .error errs

end AeneasCheck.Typecheck.Consistency
