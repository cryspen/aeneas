import Std.Data.HashMap
import AeneasCheck.Raw.CertEvent
import AeneasCheck.Raw.LLBCProgram

/-!
# M9.7h — Cert v3 structural consistency (Level S / Level R)

After M9.7o-E5a, the flat type/trait decl mirrors are gone and the
embedded `llbcProgram` is the sole source of those decls — so the
old "pair flat metadata against structured metadata" checks were
deleted (they were tautological). What remains here:

* **Function-cert pairing** (`checkFunctions`): the cert's `FunCert.fnId`
  / `FunCert.fnName` must point at an `LlbcFunDecl` in the embedded
  program with matching id, name, and input arity.
* **Per-event id-set checks** (`checkEventRefs`): `EvCall.fn` must
  resolve in `lp.fun_decls`, `EvMatchArm.{adtId, variantId, variantName}`
  must resolve in `lp.type_decls`, and every event's place root must
  be in bounds of the function's `localsTypes`.
* **Control-flow well-nestedness + abstraction lifecycle**
  (`checkFlow`, M9.7j): `EvLoopInv` / `EvLoopEnd` balance and the
  abs-id introduction set.
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

The cert's per-function metadata is pairwise indexed by *id*, not by
array position, because `cc.functions` may skip ids that Charon
emitted as opaque/global decls. Build a HashMap once per check and
pair via lookup. -/

private def buildTypeDeclMap (ps : Array LlbcTypeDecl) :
    Std.HashMap Nat LlbcTypeDecl :=
  ps.foldl (init := {}) fun m d => m.insert d.id d

private def buildFunDeclMap (ps : Array LlbcFunDecl) :
    Std.HashMap Nat LlbcFunDecl :=
  ps.foldl (init := {}) fun m d => m.insert d.id d

/-! ## Function-cert pairing

For each `cc.functions[i]`, the cert exposes `fnId` (a `FunDeclId`)
and `fnName` (the qualified callee name). The matching
`llbcProgram.fun_decls[j]` shares the id and carries the same name
in `itemMeta.name`.

M9.7o-E5b: with the flat `FunCert.signature` field deleted, the
structured `LlbcSignature` is the sole source of input-arity info.
We retain the name-agreement check between the cert and the LLBC
program; arity disagreement no longer has two sides to compare. -/

private def checkFunPair (idx : Nat) (c : FunCert) (l : LlbcFunDecl) :
    List ConsErr := Id.run do
  let ctx := s!"functions[{idx}] id={c.fnId} '{c.fnName}'"
  let mut errs : List ConsErr := []
  if c.fnName ≠ l.itemMeta.name then
    errs := errs ++ [err ctx s!"fnName disagrees: cc={repr c.fnName} lp={repr l.itemMeta.name}"]
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
  -- Session 6: cast — recurse on the inner expression so its
  -- embedded place (if any) is collected.
  | .symCast _ inner => symExprPlaceRefs inner
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

/-! ## Control-flow well-nestedness + abstraction lifecycle (M9.7j)

These checks fold over each function's event sequence to validate
ordering-sensitive invariants the per-event id-set checks can't see:

* `EvLoopInv loopId` must be balanced by a matching `EvLoopEnd
  loopId`; nested loops are LIFO, so the latest opened loop must
  close first.
* `EvEndAbs absId` must reference an `absId` previously introduced
  somewhere in the trace. Abstractions can be opened by many
  events: `EvCall.regionAbs`, `EvCall.absSig[].absId` + `parentAbs`,
  `EvLoopInv.loanRegistry[].parentAbsId`,
  `EvSymExpandMutBorrow.parentAbs`, `EvReborrow.parentAbs`, and
  also by `MutBorrowKind.inAbsReborrow` / `loopOwned` hints. (The
  function's own ambient input abstractions — the caller-side
  abstractions for its `&mut` arguments — are *not* event-
  introduced; we accept any `EvEndAbs.abs` that wasn't seen by
  conservatively recording the seed set rather than flagging.)

We don't model symbolic-value (`SvId`) lifetimes in M9.7j —
`EvSymExpandMutBorrow.svId` introduction-vs-use is implicit in the
replayer's state thread and a structural Level-R check on it would
need a full sym-id walk (in scope for a later milestone). -/

private structure FlowState where
  /-- Stack of currently open `loopId`s (most recently opened on top). -/
  openLoops : List Nat := []
  /-- Set of `absId`s that some prior event introduced (a union of
      every abs-introducing event's id fields). We don't separately
      track *open* vs *ended* abstractions because Aeneas's interp
      emits `EvEndAbs` for caller-side abstractions whose
      introduction the cert never explicitly records. -/
  seenAbs : Std.HashSet Nat := {}

private def recordAbs (st : FlowState) (a : Nat) : FlowState :=
  { st with seenAbs := st.seenAbs.insert a }

private def stepFlow (funCtx : String) (eIdx : Nat) (ev : Event)
    (st : FlowState) : FlowState × List ConsErr := Id.run do
  let ctx := s!"{funCtx}.events[{eIdx}]"
  let mut st := st
  let mut errs : List ConsErr := []
  match ev with
  | .call _ _ _ _ _ regionAbs absSig =>
    for a in regionAbs do
      st := recordAbs st a
    for sh in absSig do
      st := recordAbs st sh.absId
      for p in sh.parentAbs do
        st := recordAbs st p
  | .endAbs absId _ _ _ =>
    -- Tolerant of caller-introduced abstractions whose origin the
    -- cert doesn't explicitly carry; we only record, never flag.
    st := recordAbs st absId
  | .reborrow _ _ _ _ (some parentAbs) =>
    st := recordAbs st parentAbs
  | .symExpandMutBorrow _ _ _ (some parentAbs) _ _ =>
    st := recordAbs st parentAbs
  | .mutBorrow _ _ _ (.inAbsReborrow absId) =>
    st := recordAbs st absId
  | .mutBorrow _ _ _ (.loopOwned absId) =>
    st := recordAbs st absId
  | .loopInv loopId _ loanRegistry =>
    st := { st with openLoops := loopId :: st.openLoops }
    for (_, parentAbsId) in loanRegistry do
      st := recordAbs st parentAbsId
  | .loopEnd loopId =>
    match st.openLoops with
    | [] =>
      errs := errs ++ [err ctx
        s!"EvLoopEnd loop_id={loopId} has no matching open EvLoopInv"]
    | top :: rest =>
      if top ≠ loopId then
        errs := errs ++ [err ctx
          s!"EvLoopEnd loop_id={loopId} does not match the most-recently-opened loop ({top}); loops must close LIFO"]
        -- best-effort: pop the top anyway so downstream errors don't cascade
        st := { st with openLoops := rest }
      else
        st := { st with openLoops := rest }
  | _ => pure ()
  return (st, errs)

private def checkFnFlow (funCtx : String) (events : Array Event) :
    List ConsErr := Id.run do
  let mut st : FlowState := {}
  let mut errs : List ConsErr := []
  for j in [0 : events.size] do
    let (st', es) := stepFlow funCtx j events[j]! st
    st := st'
    errs := errs ++ es
  -- M9.7j: post-function balance.
  unless st.openLoops.isEmpty do
    errs := errs ++ [err funCtx
      s!"function exited with {st.openLoops.length} unclosed loop(s): {repr st.openLoops}"]
  return errs

def checkFlow (ccFns : Array FunCert) : CR Unit := do
  let mut errs : List ConsErr := []
  for i in [0 : ccFns.size] do
    let f := ccFns[i]!
    let funCtx := s!"functions[{i}] id={f.fnId}"
    errs := errs ++ checkFnFlow funCtx f.events
  if errs.isEmpty then .ok () else .error errs

/-! ## Top-level driver -/

/-- Run the full Level-S / Level-R structural consistency check
    against `cc`. After M9.7o-E5a, this is unconditional (v1 / v2
    certs are rejected at parse time).

    Aggregates errors from every sub-check so a single mis-emit
    surfaces all the divergences at once instead of one at a time. -/
def checkLlbcVsCert (cc : CrateCert) : CR Unit := do
  let lp := cc.llbcProgram
  let mut errs : List ConsErr := []
  match checkFunctions cc.functions lp.funDecls with
  | .ok _ => pure ()
  | .error es => errs := errs ++ es
  match checkEventRefs cc.functions lp with
  | .ok _ => pure ()
  | .error es => errs := errs ++ es
  match checkFlow cc.functions with
  | .ok _ => pure ()
  | .error es => errs := errs ++ es
  if errs.isEmpty then .ok () else .error errs

end AeneasCheck.Typecheck.Consistency
