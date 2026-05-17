import Lean.Data.Json
import AeneasCheck.Raw.CertEvent
import AeneasCheck.Raw.LLBCProgram

/-!
JSON → Raw parser for the certificate format defined in
`src/cert/cert_schema.json` (format version 1).

Pattern: monadic `Except String α` helpers built on `Lean.Json`'s
core accessors (`getObjVal?`, `getArr?`, …). Constructor encoding
matches Serde's tagged-enum convention:
* nullary variants: JSON string `"VariantName"`
* payload variants: object `{"VariantName": <payload>}`

M9.7b: parsers for the LLBC subtree types in `Raw/LLBCProgram.lean`
(top-level entry `parseLlbcProgram`). The shape mirrors Charon's
own JSON-deserialiser (`charon-ml/src/generated/Generated_OfJson.ml`),
with simplifications where the Lean side flattens Charon's nested
`hash_consed` / `kind+ty` / index_vec shapes. The OCaml emitter for
the cert v3 `llbc_program` blob (Phase B) conforms to what this
parser expects; opaque fields whose Lean type is `Json := .null`
flow through as the raw sub-tree (or `.null` when absent).
-/

namespace AeneasCheck.Json

-- M9.7b: both `Lean.Json` and `AeneasCheck.Raw.Json` exist (the
-- latter as an `abbrev` introduced by `Raw/LLBCProgram.lean`). They
-- are definitionally equal, so we just pick the `Raw.Json` alias
-- here — opening `AeneasCheck.Raw` exposes it directly under the
-- bare name `Json`, while still letting us write `Lean.Json.*` to
-- reach the underlying methods.
open AeneasCheck.Raw

abbrev Result α := Except String α

private def fail {α} (msg : String) : Result α := .error msg

private def field (j : Json) (k : String) : Result Json := j.getObjVal? k
private def asNat (j : Json) : Result Nat := do
  let i ← j.getInt?
  if i < 0 then fail s!"expected nonneg int, got {i}" else return i.toNat
private def asBool (j : Json) : Result Bool := j.getBool?
private def asStr (j : Json) : Result String := j.getStr?
private def asArr (j : Json) : Result (Array Json) := j.getArr?

/-- Parse a single-key tagged variant: returns (tag, payload). Fails on
    multi-key objects so a malformed cert can't be confused with a
    well-formed one. -/
private def asTaggedObj (j : Json) : Result (String × Json) := do
  let kvs ← j.getObj?
  let arr := kvs.toArray
  if h : arr.size = 1 then
    return arr[0]
  else
    fail s!"expected single-key tagged variant, got {arr.size} keys"

/-! ## Primitive parsers -/

def intKindOfStr : String → Result IntKind
  | "U8" => .ok .u8 | "U16" => .ok .u16 | "U32" => .ok .u32
  | "U64" => .ok .u64 | "U128" => .ok .u128 | "Usize" => .ok .usize
  | "I8" => .ok .i8 | "I16" => .ok .i16 | "I32" => .ok .i32
  | "I64" => .ok .i64 | "I128" => .ok .i128 | "Isize" => .ok .isize
  | s => fail s!"unknown IntKind: {s}"

/-- Parse a scalar payload: `{"Unsigned": ["U32", "5"]}` or `{"Signed": …}`. -/
def parseScalar (j : Json) : Result (IntKind × Int) := do
  let (tag, payload) ← asTaggedObj j
  if tag ≠ "Unsigned" ∧ tag ≠ "Signed" then
    fail s!"scalar: expected Unsigned/Signed, got {tag}"
  else
    let arr ← asArr payload
    if h : arr.size = 2 then
      let k ← asStr arr[0] >>= intKindOfStr
      let s ← asStr arr[1]
      match s.toInt? with
      | some i => return (k, i)
      | none => fail s!"scalar: bad int literal {s}"
    else fail s!"scalar: expected 2-elt array, got {arr.size}"

def parseLiteral (j : Json) : Result Lit := do
  let (tag, payload) ← asTaggedObj j
  match tag with
  | "Scalar" =>
    let (k, v) ← parseScalar payload
    return .scalar k v
  | "Bool" => return .bool (← asBool payload)
  | "Char" => return .char (← asNat payload)
  | "Str" => return .str (← asStr payload)
  | "ByteStr" =>
    let arr ← asArr payload
    let bs ← arr.mapM asNat
    return .byteStr bs
  | "Float" => fail "literal: Float not supported in M4"
  | _ => fail s!"unknown literal tag: {tag}"

def parseProjElem (j : Json) : Result ProjElem := do
  match j with
  | .str "Deref" => return .deref
  | .str "PtrMetadata" => return .ptrMetadata
  | .str "ProjIndex" => return .projIndex
  | .str "Subslice" => return .subslice
  | .str s => fail s!"unknown ProjElem string: {s}"
  | _ =>
    let (tag, payload) ← asTaggedObj j
    match tag with
    | "Field" => return .field (← asNat payload)
    | _ => fail s!"unknown ProjElem tag: {tag}"

def parsePlace (j : Json) : Result Place := do
  let local_ ← asNat (← field j "local")
  let projJsons ← asArr (← field j "projection")
  let projection ← projJsons.mapM parseProjElem
  let tyRepr ← asStr (← field j "ty")
  -- M4: keep type as opaque string; M5 typechecker re-parses against llbc.json.
  return { local_, projection, ty := .opaque tyRepr }

partial def parseSymExpr (j : Json) : Result SymExpr := do
  let (tag, payload) ← asTaggedObj j
  match tag with
  | "SymVal" => return .symVal (← asNat payload)
  | "SymLit" => return .symLit (← parseLiteral payload)
  | "SymCopy" => return .symCopy (← parsePlace payload)
  | "SymMove" => return .symMove (← parsePlace payload)
  | "SymMutBorrowTok" => return .symMutBorrowTok (← asNat payload)
  | "SymVariant" =>
    let adtId ← asNat (← field payload "adt_id")
    let variantId ← asNat (← field payload "variant_id")
    let variantName ← asStr (← field payload "variant_name")
    -- M9.5f: the `fields` array carries one cert sym-expr per payload
    -- operand of an `AggregatedAdt`. Empty for C-style nullary
    -- variants. We tolerate a missing key for backward compatibility
    -- with M9.5d/M9.5e-vintage certs that pre-date the field.
    let fields ← match payload.getObjValD "fields" with
      | .null => pure (#[] : Array SymExpr)
      | fj =>
        let arr ← asArr fj
        arr.mapM parseSymExpr
    return .symVariant adtId variantId variantName fields
  | "SymTuple" =>
    -- M9.5p: tuple aggregate. Payload is a flat array of cert sym-exprs.
    let arr ← asArr payload
    let fields ← arr.mapM parseSymExpr
    return .symTuple fields
  | "SymRecord" =>
    -- M9.5p: named-field struct aggregate. Payload is
    -- `{ adt_id, fields = [{ name, value }, …] }`. Each entry carries
    -- the field's surface name (matching the cert type-decl's
    -- CertField.name; tuple-style structs use the `fieldK` fallback
    -- the OCaml side bakes in).
    let adtId ← asNat (← field payload "adt_id")
    let fieldArr ← asArr (← field payload "fields")
    let fields ← fieldArr.mapM fun fj => do
      let n ← asStr (← field fj "name")
      let v ← parseSymExpr (← field fj "value")
      return (n, v)
    return .symRecord adtId fields
  | _ => fail s!"unknown SymExpr tag: {tag}"

def parseRestoreInfo (j : Json) : Result RestoreInfo := do
  let gb ← parseSymExpr (← field j "given_back")
  return { givenBack := gb }

/-! ## M9.6 (Option C) hint parsers

Each parser accepts the Serde-tagged shape the OCaml `CertJson.ml`
emits in `cert_fmt_version = 2`. Nullary variants come through as
bare JSON strings (`"Direct"`, `"JoinSame"`, …); payload variants
come through as `{"VariantName": {...}}` — matching the existing
SymExpr / Event conventions. Each call site of these parsers in
`parseEvent` is wrapped in `(payload.getObjVal? "key").toOption` so
v1 certs (and v2 certs that omit the field) fall back to the
constructor default. -/

/-- M9.6: parse a `MutBorrowKind` (Option C hint). -/
def parseMutBorrowKind (j : Json) : Result MutBorrowKind := do
  match j with
  | .str "Direct" => return .direct
  | .str s => fail s!"unknown nullary MutBorrowKind: {s}"
  | _ =>
    let (tag, payload) ← asTaggedObj j
    match tag with
    | "Direct" => return .direct
    | "InAbsReborrow" => return .inAbsReborrow (← asNat (← field payload "abs"))
    | "LoopOwned" => return .loopOwned (← asNat (← field payload "loop"))
    | _ => fail s!"unknown MutBorrowKind tag: {tag}"

/-- M9.6: parse a `JoinRule` (Option C hint). -/
def parseJoinRule (j : Json) : Result JoinRule := do
  match j with
  | .str "JoinSame" => return .joinSame
  | .str "JoinVar" => return .joinVar
  | .str s => fail s!"unknown nullary JoinRule: {s}"
  | _ =>
    let (tag, payload) ← asTaggedObj j
    match tag with
    | "JoinSame" => return .joinSame
    | "JoinVar" => return .joinVar
    | "JoinSymbolic" => return .joinSymbolic (← asNat (← field payload "fresh_sv"))
    | "JoinMutBorrows" => do
      let l ← asNat (← field payload "left")
      let r ← asNat (← field payload "right")
      let f ← asNat (← field payload "fresh")
      let a ← asNat (← field payload "abs")
      return .joinMutBorrows l r f a
    | "JoinBottomOther" => return .joinBottomOther (← asNat (← field payload "abs"))
    | "JoinOtherBottom" => return .joinOtherBottom (← asNat (← field payload "abs"))
    | _ => fail s!"unknown JoinRule tag: {tag}"

/-- M9.6: parse one `JoinEntry`. -/
def parseJoinEntry (j : Json) : Result JoinEntry := do
  let localId ← asNat (← field j "local")
  let rule ← parseJoinRule (← field j "rule")
  return { localId, rule }

/-- M9.6: parse one `AbsRoleEntry` (Option C abs-shape role). -/
def parseAbsRoleEntry (j : Json) : Result AbsRoleEntry := do
  let (tag, payload) ← asTaggedObj j
  match tag with
  | "MutBorrow" => do
    let argIdx ← asNat (← field payload "arg_idx")
    let loan ← asNat (← field payload "loan")
    return .mutBorrow argIdx loan
  | "MutLoan" => return .mutLoan (← asNat (← field payload "loan"))
  | "SharedBorrow" => do
    let argIdx ← asNat (← field payload "arg_idx")
    let sb ← asNat (← field payload "sb_id")
    return .sharedBorrow argIdx sb
  | _ => fail s!"unknown AbsRoleEntry tag: {tag}"

/-- M9.6: parse one `AbsShape`. -/
def parseAbsShape (j : Json) : Result AbsShape := do
  let absId ← asNat (← field j "abs_id")
  let parentArr ← asArr (← field j "parent_abs")
  let parentAbs ← parentArr.mapM asNat
  let rolesArr ← asArr (← field j "roles")
  let roles ← rolesArr.mapM parseAbsRoleEntry
  return { absId, parentAbs, roles }

/-- M9.6: parse an optional hint field. Returns `default` when the
    key is absent (back-compat); otherwise runs `f` on the value. -/
@[inline] private def optField {α} (j : Json) (k : String) (default : α)
    (f : Json → Result α) : Result α :=
  match (j.getObjVal? k).toOption with
  | some v => f v
  | none => pure default

/-- M9.6: parse an optional array-of-T hint, defaulting to `#[]`. -/
@[inline] private def optArrayField {α} (j : Json) (k : String)
    (f : Json → Result α) : Result (Array α) :=
  optField j k #[] (fun v => do
    let arr ← asArr v
    arr.mapM f)

def parseStateSummary (j : Json) : Result StateSummary := do
  let envArr ← asArr (← field j "env")
  let env ← envArr.mapM fun ej => do
    let l ← asNat (← field ej "local")
    let v ← parseSymExpr (← field ej "value")
    return (l, v)
  let liveArr ← asArr (← field j "live_loans")
  let liveLoans ← liveArr.mapM asNat
  return { env, liveLoans }

def parseEvent (j : Json) : Result Event := do
  match j with
  | .str "EvPanic" => return .panic
  | .str "EvReturn" => return .retn
  | .str s => fail s!"unknown nullary Event: {s}"
  | _ =>
    let (tag, payload) ← asTaggedObj j
    match tag with
    | "EvMutBorrow" =>
      let loan ← asNat (← field payload "loan")
      let place ← parsePlace (← field payload "place")
      let symval ← asNat (← field payload "symval")
      -- M9.6: optional `kind_hint` (Option C). Absent ⇒ `.direct`.
      let kindHint ← optField payload "kind_hint" .direct parseMutBorrowKind
      return .mutBorrow loan place symval (kindHint := kindHint)
    | "EvSharedBorrow" =>
      let loan ← asNat (← field payload "loan")
      let sbId ← asNat (← field payload "shared_borrow_id")
      let place ← parsePlace (← field payload "place")
      let symval ← asNat (← field payload "symval")
      return .sharedBorrow loan sbId place symval
    | "EvAssign" =>
      let dst ← parsePlace (← field payload "dst")
      let rhs ← parseSymExpr (← field payload "rhs")
      return .assign dst rhs
    | "EvMove" =>
      let src ← parsePlace (← field payload "src")
      let dst ← parsePlace (← field payload "dst")
      return .move src dst
    | "EvCopy" =>
      let src ← parsePlace (← field payload "src")
      let dst ← parsePlace (← field payload "dst")
      return .copy src dst
    | "EvEndBorrow" =>
      let loan ← asNat (← field payload "loan")
      let restore ← parseRestoreInfo (← field payload "restore")
      return .endBorrow loan restore
    | "EvAssert" =>
      let cond ← parseSymExpr (← field payload "cond")
      let expected ← asBool (← field payload "expected")
      return .assert cond expected
    | "EvBinop" =>
      let op ← asStr (← field payload "op")
      let lhs ← parseSymExpr (← field payload "lhs")
      let rhs ← parseSymExpr (← field payload "rhs")
      let dst ← parsePlace (← field payload "dst")
      return .binop op lhs rhs dst
    | "EvReborrow" =>
      let child ← asNat (← field payload "child")
      let parent ← asNat (← field payload "parent")
      let place ← parsePlace (← field payload "place")
      -- M9.6: optional `parent_live` / `parent_abs` (Option C).
      let parentLive ← optField payload "parent_live" false asBool
      let parentAbs ← optField payload "parent_abs" none
        (fun v => do let n ← asNat v; pure (some n))
      return .reborrow child parent place
                       (parentLive := parentLive) (parentAbs := parentAbs)
    | "EvCall" =>
      let fn ← asNat (← field payload "fn")
      let fnName ← asStr (← field payload "fn_name")
      let callId ← asNat (← field payload "call_id")
      let argsArr ← asArr (← field payload "args")
      let args ← argsArr.mapM parseSymExpr
      let dst ← parsePlace (← field payload "dst")
      let raArr ← asArr (← field payload "region_abs")
      let regionAbs ← raArr.mapM asNat
      -- M9.6: optional `abs_sig` (Option C).
      let absSig ← optArrayField payload "abs_sig" parseAbsShape
      return .call fn callId fnName args dst regionAbs (absSig := absSig)
    | "EvEndAbs" =>
      let abs ← asNat (← field payload "abs")
      let fvArr ← asArr (← field payload "final_values")
      let finalValues ← fvArr.mapM parseSymExpr
      -- M9.5s: `released_loans` is optional for back-compat with
      -- pre-M9.5s certs (which had no implicit-end-loan tracking on
      -- EvEndAbs). Defaults to empty.
      let releasedLoans : Array Nat ←
        match (payload.getObjVal? "released_loans").toOption with
        | some rj => do
          let arr ← asArr rj
          arr.mapM asNat
        | none => pure #[]
      -- M9.6: optional `token_clear_locals` (Option C).
      let tokenClearLocals ← optArrayField payload "token_clear_locals" asNat
      return .endAbs abs finalValues releasedLoans
                     (tokenClearLocals := tokenClearLocals)
    | "EvProj" =>
      let abs ← asNat (← field payload "abs")
      let place ← parsePlace (← field payload "place")
      let symval ← asNat (← field payload "symval")
      return .proj abs place symval
    | "EvSymExpandMutBorrow" =>
      let svId ← asNat (← field payload "sv_id")
      let bid ← asNat (← field payload "bid")
      let innerSv ← asNat (← field payload "inner_sv")
      -- M9.6: optional `parent_abs` / `subst_locals` / `subst_loans`
      -- (Option C).
      let parentAbs ← optField payload "parent_abs" none
        (fun v => do let n ← asNat v; pure (some n))
      let substLocals ← optArrayField payload "subst_locals" asNat
      let substLoans ← optArrayField payload "subst_loans" asNat
      return .symExpandMutBorrow svId bid innerSv
                                 (parentAbs := parentAbs)
                                 (substLocals := substLocals)
                                 (substLoans := substLoans)
    | "EvJoin" =>
      let left ← parseStateSummary (← field payload "left")
      let right ← parseStateSummary (← field payload "right")
      let result ← parseStateSummary (← field payload "result")
      -- M9.6: optional `witnesses` (Option C).
      let witnesses ← optArrayField payload "witnesses" parseJoinEntry
      return .join left right result (witnesses := witnesses)
    | "EvLoopInv" =>
      let loopId ← asNat (← field payload "loop_id")
      let invariant ← parseStateSummary (← field payload "invariant")
      -- M9.6: optional `loan_registry` (Option C). Each entry is
      -- `{"borrow": N, "parent_abs": N}` — the fixpoint's
      -- (borrowId, parentAbsId) pair.
      let loanRegistry ← optArrayField payload "loan_registry" (fun ej => do
        let b ← asNat (← field ej "borrow")
        let p ← asNat (← field ej "parent_abs")
        pure (b, p))
      return .loopInv loopId invariant (loanRegistry := loanRegistry)
    | "EvLoopEnd" =>
      let loopId ← asNat (← field payload "loop_id")
      return .loopEnd loopId
    | "EvMatchArm" =>
      let scrutinee ← parseSymExpr (← field payload "scrutinee")
      let adtId ← asNat (← field payload "adt_id")
      let variantId ← asNat (← field payload "variant_id")
      let variantName ← asStr (← field payload "variant_name")
      return .matchArm scrutinee adtId variantId variantName
    | _ => fail s!"unknown Event tag: {tag}"

/-- M9.5o: parse one `{trait, type_param}` trait-clause record. -/
def parseTraitClause (j : Json) : Result TraitClause := do
  let traitQualifiedName ← asStr (← field j "trait")
  let typeParamIdx ← asNat (← field j "type_param")
  return { traitQualifiedName, typeParamIdx }

/-- Parse a signature record. Types are kept as opaque-tagged strings:
    M9.0b carries them verbatim from the OCaml `show_ty` output.

    M9.5i: `type_params` is optional for back-compat with pre-M9.5i
    certs (which carry no type-param info); the field defaults to
    empty when absent.

    M9.5o: `trait_clauses` is optional for back-compat with pre-M9.5o
    certs. -/
def parseSignature (j : Json) : Result FnSignature := do
  let inputsArr ← asArr (← field j "inputs")
  let inputs ← inputsArr.mapM fun ej => do
    let s ← asStr ej
    return RawTy.opaque s
  let outputStr ← asStr (← field j "output")
  let typeParams : Array String ← match (j.getObjVal? "type_params").toOption with
    | some tj => do
      let arr ← asArr tj
      arr.mapM asStr
    | none => pure #[]
  let traitClauses : Array TraitClause ←
    match (j.getObjVal? "trait_clauses").toOption with
    | some cj => do
      let arr ← asArr cj
      arr.mapM parseTraitClause
    | none => pure #[]
  return { inputs, output := .opaque outputStr, typeParams, traitClauses }

/-- Parse an optional source-span record. -/
def parseSourceSpan (j : Json) : Result SourceSpan := do
  let file ← asStr (← field j "file")
  let begLine ← asNat (← field j "beg_line")
  let begCol ← asNat (← field j "beg_col")
  let endLine ← asNat (← field j "end_line")
  let endCol ← asNat (← field j "end_col")
  return { file, begLine, begCol, endLine, endCol }

def parseFunCert (j : Json) : Result FunCert := do
  let fnId ← asNat (← field j "fn_id")
  let fnName ← asStr (← field j "fn_name")
  -- `signature` is required by the v1 schema (added in M9.0b). We
  -- still tolerate certs that omit it for forward-compat with hand-
  -- written negative fixtures.
  let signature ← match (j.getObjVal? "signature").toOption with
    | some sj => parseSignature sj
    | none => pure { inputs := #[], output := .opaque "" }
  let sourceSpan ← match (j.getObjVal? "source_span").toOption with
    | some sj => do let s ← parseSourceSpan sj; pure (some s)
    | none => pure none
  let evArr ← asArr (← field j "events")
  let events ← evArr.mapM parseEvent
  let finalState ← parseStateSummary (← field j "final_state")
  -- M9.5l: optional pre-computed Lean name (trait impl methods).
  let prettyName : Option String ← match (j.getObjVal? "pretty_name").toOption with
    | some pj => do let s ← asStr pj; pure (some s)
    | none => pure none
  return { fnId, fnName, signature, sourceSpan, events, finalState, prettyName }

/-- M9.5b: parse one `cert_field` JSON object into a `CertField`. -/
def parseCertField (j : Json) : Result CertField := do
  let idx ← asNat (← field j "idx")
  let name : Option String ← match (j.getObjVal? "name").toOption with
    | some nj => do let s ← asStr nj; pure (some s)
    | none => pure none
  let tyStr ← asStr (← field j "ty")
  return { idx, name, ty := RawTy.opaque tyStr }

/-- M9.5d: parse one `cert_variant` JSON object into a `CertVariant`. -/
def parseCertVariant (j : Json) : Result CertVariant := do
  let id ← asNat (← field j "id")
  let name ← asStr (← field j "name")
  let fieldsArr ← asArr (← field j "fields")
  let fields ← fieldsArr.mapM parseCertField
  return { id, name, fields }

/-- M9.5b: parse a `TypeDeclKind`. Nullary `"Opaque"`, `{"Struct": [<fields>]}`,
    or M9.5d `{"Enum": [<variants>]}`. -/
def parseTypeDeclKind (j : Json) : Result TypeDeclKind := do
  match j with
  | .str "Opaque" => return .opaque
  | _ =>
    let (tag, payload) ← asTaggedObj j
    match tag with
    | "Struct" =>
      let arr ← asArr payload
      let fields ← arr.mapM parseCertField
      return .struct fields
    | "Enum" =>
      let arr ← asArr payload
      let variants ← arr.mapM parseCertVariant
      return .enum variants
    | _ =>
      -- Forward-compat: unknown kinds (Union, Alias, …) downgrade to
      -- opaque so an early checker can still load a future cert.
      return .opaque

/-- M9.5b: parse one top-level `TypeDecl`.

    M9.5i: `type_params` is optional for back-compat with pre-M9.5i
    certs (and with monomorphic-only crates whose OCaml emitter ran
    before this milestone); the field defaults to empty when absent.

    M9.5l: `is_tuple_struct` is optional for the same reason and
    defaults to false. -/
def parseTypeDecl (j : Json) : Result TypeDecl := do
  let id ← asNat (← field j "id")
  let name ← asStr (← field j "name")
  let kind ← parseTypeDeclKind (← field j "kind")
  let typeParams : Array String ← match (j.getObjVal? "type_params").toOption with
    | some tj => do
      let arr ← asArr tj
      arr.mapM asStr
    | none => pure #[]
  let isTupleStruct : Bool ← match (j.getObjVal? "is_tuple_struct").toOption with
    | some bj => match bj with
      | .bool b => pure b
      | _ => pure false
    | none => pure false
  let sourceSpan ← match (j.getObjVal? "source_span").toOption with
    | some sj => do let s ← parseSourceSpan sj; pure (some s)
    | none => pure none
  -- M9.5n: `qualified_name` is optional for back-compat with pre-M9.5n
  -- certs; falls back to the bare `name` so the standard `bare_name`
  -- vs `qualified_name` distinction still works when the field is
  -- absent (the suppression check below just won't match anything).
  let qualifiedName : String ← match (j.getObjVal? "qualified_name").toOption with
    | some qj => asStr qj
    | none => pure ""
  return { id, name, kind, typeParams, isTupleStruct, sourceSpan, qualifiedName }

/-- M9.5l: parse one `TraitMethodDecl`. M9.5o adds optional
    `has_default` flag (defaults to false for back-compat). -/
def parseTraitMethodDecl (j : Json) : Result TraitMethodDecl := do
  let name ← asStr (← field j "name")
  let signature ← parseSignature (← field j "signature")
  let hasDefault : Bool ← match (j.getObjVal? "has_default").toOption with
    | some bj => match bj with
      | .bool b => pure b
      | _ => pure false
    | none => pure false
  return { name, signature, hasDefault }

/-- M9.5l: parse one top-level `TraitDecl`. -/
def parseTraitDecl (j : Json) : Result TraitDecl := do
  let id ← asNat (← field j "id")
  let name ← asStr (← field j "name")
  let qualifiedName ← match (j.getObjVal? "qualified_name").toOption with
    | some qj => asStr qj
    | none => pure name
  let methodArr ← asArr (← field j "methods")
  let methods ← methodArr.mapM parseTraitMethodDecl
  let sourceSpan ← match (j.getObjVal? "source_span").toOption with
    | some sj => do let s ← parseSourceSpan sj; pure (some s)
    | none => pure none
  return { id, name, qualifiedName, methods, sourceSpan }

/-- M9.5l: parse one `TraitImplMethod`. -/
def parseTraitImplMethod (j : Json) : Result TraitImplMethod := do
  let name ← asStr (← field j "name")
  let fnId ← asNat (← field j "fn_id")
  return { name, fnId }

/-- M9.5l: parse one top-level `TraitImpl`. `self_type_decl_id` is
    optional (the OCaml side emits it as `Some` only for the
    minimal-case ADT-Self impls).

    M9.5o: `self_type_var` is optional (set for blanket impls);
    `type_params` and `trait_clauses` are optional with empty
    defaults for back-compat. -/
def parseTraitImpl (j : Json) : Result TraitImpl := do
  let id ← asNat (← field j "id")
  let prettyName ← asStr (← field j "pretty_name")
  let qualifiedName ← match (j.getObjVal? "qualified_name").toOption with
    | some qj => asStr qj
    | none => pure prettyName
  let traitDeclId ← asNat (← field j "trait_decl_id")
  let selfTypeDeclId : Option Nat ← match (j.getObjVal? "self_type_decl_id").toOption with
    | some sj => do let n ← asNat sj; pure (some n)
    | none => pure none
  let selfTypeVar : Option String ←
    match (j.getObjVal? "self_type_var").toOption with
    | some sj => do let s ← asStr sj; pure (some s)
    | none => pure none
  let typeParams : Array String ←
    match (j.getObjVal? "type_params").toOption with
    | some tj => do let arr ← asArr tj; arr.mapM asStr
    | none => pure #[]
  let traitClauses : Array TraitClause ←
    match (j.getObjVal? "trait_clauses").toOption with
    | some cj => do let arr ← asArr cj; arr.mapM parseTraitClause
    | none => pure #[]
  let methodArr ← asArr (← field j "methods")
  let methods ← methodArr.mapM parseTraitImplMethod
  let sourceSpan ← match (j.getObjVal? "source_span").toOption with
    | some sj => do let s ← parseSourceSpan sj; pure (some s)
    | none => pure none
  return { id, prettyName, qualifiedName, traitDeclId, selfTypeDeclId,
           selfTypeVar, typeParams, traitClauses, methods, sourceSpan }

/-! ## M9.7b: LLBC program parser

The block below parses the structured Charon LLBC subtree introduced
in `Raw/LLBCProgram.lean` (M9.7a) and embedded in cert v3 under the
top-level `llbc_program` key. The JSON shape follows Charon's own
`Generated_OfJson.ml` deserialiser, with simplifications:

* `ty = ty_kind hash_consed` is flattened — we parse the `ty_kind`
  variant directly into `LlbcTy`.
* `place = { kind; ty }` is flattened to `{ local; projection; ty }`
  (the Charon `kind` recursion is converted to a flat projection
  list during cert-v3 emission, matching the existing M4 `Place`
  shape).
* `generic_args` (the type-application context) is *not* parsed here
  — we keep it as an opaque `Json` payload under `FnOperand.funDecl`
  / `traitMethod`. The `LlbcGenericParams` (decl-side) parser only
  pulls out the parameter *names*.
* Opaque slots (`attrInfo`, `extra`, `vtable`, `src`, `globalDecls`,
  `implTrait`, `impliedTraitRefs`, `reprOptions`, `ptrMetadata`) flow
  through as `Lean.Json` via `getObjValD k` (which returns `.null`
  for missing keys).

Required fields fail loudly with the parser name + key as prefix
(e.g. `parseLlbcTypeDecl[id]: …`). Optional fields with a clear
Lean-side default (typically `#[]` or `none` or a `.tOpaque ""`)
fall back silently. -/

/-- M9.7b: returns the JSON sub-value at `k`, or `none` when the key is
    missing or explicitly `.null`. Use for optional sub-trees. -/
private def fieldOpt (j : Json) (k : String) : Option Json :=
  match j.getObjValD k with
  | .null => none
  | other => some other

/-- M9.7b: capture an opaque sub-tree directly as `Lean.Json`. Missing
    keys flow through as `.null` per the `Raw.LLBCProgram` convention. -/
private def fieldOpaque (j : Json) (k : String) : Json := j.getObjValD k

/-- M9.7b: parse a signed integer (LLBC switchInt arms can be negative
    for signed-int scrutinees). -/
private def asInt (j : Json) : Result Int := j.getInt?

/-- M9.7b: parse `LitTy`. Mirrors Charon `literal_type_of_json`:
    nullary `"Bool"`/`"Char"`, tagged `Int`/`UInt`/`Float`. -/
def parseLitTy (j : Json) : Result LitTy := do
  match j with
  | .str "Bool" => return .bool
  | .str "Char" => return .char
  | _ =>
    let (tag, payload) ← asTaggedObj j
    match tag with
    | "Int" =>
      let s ← asStr payload
      let k ← intKindOfStr s
      return .int k
    | "UInt" =>
      let s ← asStr payload
      let k ← intKindOfStr s
      return .int k
    | "Float" =>
      -- payload is the float-type tag "F16"/"F32"/"F64"/"F128"
      let s ← asStr payload
      let bits := match s with
        | "F16" => 16 | "F32" => 32 | "F64" => 64 | "F128" => 128
        | _ => 0
      return .float bits
    | _ => fail s!"parseLitTy: unknown tag {tag}"

/-- M9.7b: parse `RefKind`. Mirrors Charon `ref_kind_of_json`:
    `"Mut"` / `"Shared"`. -/
def parseRefKind (j : Json) : Result RefKind := do
  match j with
  | .str "Mut" => return .mut
  | .str "Shared" => return .shared
  | _ => fail s!"parseRefKind: expected Mut/Shared, got {j.pretty}"

/-- M9.7b: parse an `LlbcTy`. Mirrors Charon's `ty_kind_of_json`.
    Recursive, hence `partial def`. -/
partial def parseLlbcTy (j : Json) : Result LlbcTy := do
  -- Charon nullary cases
  match j with
  | .str "Never" => return .tNever
  | .str "Str" => return .tStr
  | _ =>
    let (tag, payload) ← asTaggedObj j
    match tag with
    | "Literal" =>
      let lt ← parseLitTy payload
      return .litTy lt
    | "Adt" =>
      -- Charon's `type_decl_ref = { id; generics }`. `id` is `type_id`
      -- (Adt id N | "Tuple" | "Builtin" tag). For tuples we lift to
      -- `tTuple args`; for `TAdtId n` we lift to `tAdt n args`.
      let idJson ← field payload "id"
      let genericsJson ← field payload "generics"
      -- type-args from generics.types (Charon's `index_vec` shape:
      -- `[null|value, …]` after the OCaml indexing-loss bake-out;
      -- we expect a plain array of ty values from Phase B).
      let typesJson : Json := genericsJson.getObjValD "types"
      let argsArr ← match typesJson with
        | .null => pure (#[] : Array Json)
        | other => asArr other
      let args ← argsArr.mapM parseLlbcTy
      -- Dispatch on `id` shape.
      match idJson with
      | .str "Tuple" => return .tTuple args
      | _ =>
        let (idTag, idPayload) ← asTaggedObj idJson
        match idTag with
        | "Adt" =>
          let n ← asNat idPayload
          return .tAdt n args
        | "Builtin" =>
          -- e.g. `"Box"`, `"Str"`. Keep as opaque for now.
          let bs ← asStr idPayload
          return .tOpaque s!"Builtin({bs})"
        | _ => fail s!"parseLlbcTy[Adt.id]: unknown tag {idTag}"
    | "TypeVar" =>
      -- Charon's `TVar (Bound|Free) n`. Extract the trailing nat.
      match payload with
      | .str _ => fail "parseLlbcTy[TypeVar]: unexpected string"
      | _ =>
        let (vTag, vPay) ← asTaggedObj payload
        match vTag with
        | "Free" => return .tVar (← asNat vPay)
        | "Bound" =>
          -- `[de_bruijn_id, type_var_id]` — flatten to the var id.
          let arr ← asArr vPay
          if h : arr.size = 2 then
            let n ← asNat arr[1]
            return .tVar n
          else fail s!"parseLlbcTy[TypeVar.Bound]: expected 2-elt list, got {arr.size}"
        | _ => fail s!"parseLlbcTy[TypeVar]: unknown tag {vTag}"
    | "Ref" =>
      -- `[region, ty, ref_kind]` — region opaque for now (use 0).
      let arr ← asArr payload
      if h : arr.size = 3 then
        let inner ← parseLlbcTy arr[1]
        let kind ← parseRefKind arr[2]
        return .tRef 0 inner kind
      else fail s!"parseLlbcTy[Ref]: expected 3-elt list, got {arr.size}"
    | "RawPtr" =>
      let arr ← asArr payload
      if h : arr.size = 2 then
        let inner ← parseLlbcTy arr[0]
        let kind ← parseRefKind arr[1]
        return .tRawPtr inner kind
      else fail s!"parseLlbcTy[RawPtr]: expected 2-elt list, got {arr.size}"
    | "Array" =>
      -- `[ty, constant_expr]`. We only extract a numeric length when
      -- the constant is a literal scalar; otherwise fall back to
      -- `tOpaque`.
      let arr ← asArr payload
      if h : arr.size = 2 then
        let elem ← parseLlbcTy arr[0]
        -- Constant: `{kind: …, ty: …}`. Try to read a scalar literal
        -- length; if not, downgrade to opaque.
        let cExpr := arr[1]
        let lenOpt : Option Nat ← (do
          let kJson ← field cExpr "kind"
          match kJson with
          | _ =>
            let (cTag, cPay) ← asTaggedObj kJson
            if cTag ≠ "Literal" then return none
            let (lTag, lPay) ← asTaggedObj cPay
            if lTag ≠ "Scalar" then return none
            let (_k, v) ← parseScalar lPay
            if v < 0 then return none else return some v.toNat) <|> pure none
        match lenOpt with
        | some n => return .tArray elem n
        | none => return .tOpaque s!"Array(opaque-len)"
      else fail s!"parseLlbcTy[Array]: expected 2-elt list, got {arr.size}"
    | "Slice" =>
      let inner ← parseLlbcTy payload
      return .tSlice inner
    | "FnPtr" =>
      -- Opaque: a fully-fledged signature with region binders. We
      -- skip the binder and read the inner `inputs` / `output` when
      -- they're available, else fall back to opaque.
      return .tOpaque "FnPtr"
    | "FnDef" => return .tOpaque "FnDef"
    | "DynTrait" =>
      -- We have an inner trait-id somewhere; not introspecting it.
      return .tDynTrait 0
    | "PtrMetadata" => return .tOpaque "PtrMetadata"
    | "TraitType" => return .tOpaque "TraitType"
    | "Error" =>
      let s ← asStr payload
      return .tOpaque s!"Error({s})"
    | _ => return .tOpaque s!"Unknown({tag})"

/-- M9.7b: parse an `LlbcProjElem`. Mirrors Charon's
    `projection_elem_of_json`. Charon's `Field (proj_kind, field_id)`
    is unfolded so the resulting Lean carries `(type_decl_id,
    variant_id, field_id)`. Tuple projection `ProjTuple n` is folded
    to `field 0 none n` (type-decl-id 0 as a placeholder). -/
def parseLlbcProjElem (j : Json) : Result LlbcProjElem := do
  match j with
  | .str "Deref" => return .deref
  | .str "PtrMetadata" => return .ptrMetadata
  | _ =>
    let (tag, payload) ← asTaggedObj j
    match tag with
    | "Field" =>
      -- `[proj_kind, field_id]`. proj_kind = Adt(type_decl_id, var?)|Tuple n.
      let arr ← asArr payload
      if h : arr.size = 2 then
        let fid ← asNat arr[1]
        let pk := arr[0]
        match pk with
        | _ =>
          let (pTag, pPay) ← asTaggedObj pk
          match pTag with
          | "Adt" =>
            let pArr ← asArr pPay
            if h2 : pArr.size = 2 then
              let tdId ← asNat pArr[0]
              let variantId : Option Nat ← match pArr[1] with
                | .null => pure none
                | other => do let n ← asNat other; pure (some n)
              return .field tdId variantId fid
            else fail s!"parseLlbcProjElem[Field.Adt]: expected 2-elt list"
          | "Tuple" =>
            -- Tuple projection: synthesize a field with no variant
            -- and a placeholder type-decl id (0).
            return .field 0 none fid
          | _ => fail s!"parseLlbcProjElem[Field.proj_kind]: unknown tag {pTag}"
      else fail s!"parseLlbcProjElem[Field]: expected 2-elt list, got {arr.size}"
    | "Index" =>
      -- `{offset: <const_expr>, from_end: bool}`. We try to extract
      -- a numeric constant offset, else `none`.
      let offsetJson := payload.getObjValD "offset"
      let offset : Option Nat ← (do
        let kJson ← field offsetJson "kind"
        let (cTag, cPay) ← asTaggedObj kJson
        if cTag ≠ "Literal" then return none
        let (lTag, lPay) ← asTaggedObj cPay
        if lTag ≠ "Scalar" then return none
        let (_k, v) ← parseScalar lPay
        if v < 0 then return none else return some v.toNat) <|> pure none
      return .projIndex offset
    | "Subslice" =>
      -- `{from, to, from_end}` — `from`/`to` are constant_exprs; we
      -- best-effort extract their literal scalar values.
      let fromEnd ← asBool (payload.getObjValD "from_end")
      let extractNat (key : String) : Result (Option Nat) := (do
        let cJson := payload.getObjValD key
        let kJson ← field cJson "kind"
        let (cTag, cPay) ← asTaggedObj kJson
        if cTag ≠ "Literal" then return none
        let (lTag, lPay) ← asTaggedObj cPay
        if lTag ≠ "Scalar" then return none
        let (_k, v) ← parseScalar lPay
        if v < 0 then return none else return some v.toNat) <|> pure none
      let fromN ← extractNat "from"
      let toN ← extractNat "to"
      return .subslice fromN toN fromEnd
    | _ => fail s!"parseLlbcProjElem: unknown tag {tag}"

/-- M9.7b: parse an `LlbcPlace`. Phase-B emission flattens Charon's
    nested `place_kind` into `{local, projection, ty}`. -/
def parseLlbcPlace (j : Json) : Result LlbcPlace := do
  let local_ ← asNat (← field j "local")
  let projArr ← asArr (← field j "projection")
  let projection ← projArr.mapM parseLlbcProjElem
  let ty ← parseLlbcTy (← field j "ty")
  return { local_, projection, ty }

/-- M9.7b: parse a `Lit` payload as a literal-value sub-tree. Reuses
    `parseLiteral` to interpret a Serde-tagged `Scalar`/`Bool`/`Char`/
    `Str`/`ByteStr`. -/
private def parseLlbcConstLit (j : Json) : Result Lit := parseLiteral j

mutual

/-- M9.7b: parse an `LlbcOperand`. Mirrors Charon's
    `operand_of_json`: `{Copy}`/`{Move}`/`{Const}`. -/
partial def parseLlbcOperand (j : Json) : Result LlbcOperand := do
  let (tag, payload) ← asTaggedObj j
  match tag with
  | "Copy" => return .copy (← parseLlbcPlace payload)
  | "Move" => return .move (← parseLlbcPlace payload)
  | "Const" =>
    -- Charon's `constant_expr = {kind, ty}`. `kind` is a tagged
    -- variant; we only structure `Literal`, else fall back to opaque.
    let kJson ← field payload "kind"
    let (cTag, cPay) ← asTaggedObj kJson
    match cTag with
    | "Literal" =>
      let lit ← parseLlbcConstLit cPay
      return .const lit
    | _ => return .constOpaque s!"const:{cTag}"
  | _ => fail s!"parseLlbcOperand: unknown tag {tag}"

/-- M9.7b: parse an `AggregateKind`. Mirrors Charon's
    `aggregate_kind_of_json`. -/
partial def parseAggregateKind (j : Json) : Result AggregateKind := do
  match j with
  | .str "Tuple" => return .tuple
  | _ =>
    let (tag, payload) ← asTaggedObj j
    match tag with
    | "Adt" =>
      -- `[type_decl_ref, variant_id?, field_id?]`
      let arr ← asArr payload
      if h : arr.size = 3 then
        let tdRef := arr[0]
        let idJson ← field tdRef "id"
        let typeId : Nat ← match idJson with
          | _ =>
            let (idTag, idPay) ← asTaggedObj idJson
            match idTag with
            | "Adt" => asNat idPay
            | _ => pure 0
        let variantId : Option Nat ← match arr[1] with
          | .null => pure none
          | other => do let n ← asNat other; pure (some n)
        let fieldId : Option Nat ← match arr[2] with
          | .null => pure none
          | other => do let n ← asNat other; pure (some n)
        return .adt typeId variantId fieldId
      else fail s!"parseAggregateKind[Adt]: expected 3-elt list, got {arr.size}"
    | "Array" =>
      -- `[ty, constant_expr]`
      let arr ← asArr payload
      if h : arr.size = 2 then
        let ty ← parseLlbcTy arr[0]
        return .array ty
      else fail s!"parseAggregateKind[Array]: expected 2-elt list"
    | "RawPtr" =>
      -- `[ty, ref_kind]`
      let arr ← asArr payload
      if h : arr.size = 2 then
        let kind ← parseRefKind arr[1]
        return .raw_ptr kind
      else fail s!"parseAggregateKind[RawPtr]: expected 2-elt list"
    | "Closure" =>
      -- Best effort: extract a function-id; fall back to 0.
      let fid : Nat ← (asNat payload) <|> pure 0
      return .closure fid
    | _ => fail s!"parseAggregateKind: unknown tag {tag}"

/-- M9.7b: parse an `LlbcRvalue`. Mirrors Charon's `rvalue_of_json`. -/
partial def parseLlbcRvalue (j : Json) : Result LlbcRvalue := do
  let (tag, payload) ← asTaggedObj j
  match tag with
  | "Use" =>
    let op ← parseLlbcOperand payload
    return .use op
  | "Ref" =>
    -- Charon: `{place, kind, ptr_metadata}`. `kind` is `borrow_kind`
    -- (Shared/Mut/TwoPhaseMut/Shallow/UniqueImmutable). Map to
    -- `RefKind.mut`/`.shared` (lossy on TwoPhaseMut/Shallow).
    let place ← parseLlbcPlace (← field payload "place")
    let kindJson ← field payload "kind"
    let kind : RefKind ← match kindJson with
      | .str "Mut" => pure .mut
      | .str "TwoPhaseMut" => pure .mut
      | .str _ => pure .shared
      | _ => pure .shared
    return .ref place kind
  | "RawPtr" =>
    let place ← parseLlbcPlace (← field payload "place")
    let kind ← parseRefKind (← field payload "kind")
    return .rawPtr place kind
  | "BinaryOp" =>
    -- `[binop, op, op]`. binop is a string tag or `{Add: <overflow>}`-style.
    let arr ← asArr payload
    if h : arr.size = 3 then
      let opTag : String ← match arr[0] with
        | .str s => pure s
        | _ => (do let (t, _) ← asTaggedObj arr[0]; pure t) <|> pure "?"
      let lhs ← parseLlbcOperand arr[1]
      let rhs ← parseLlbcOperand arr[2]
      return .binaryOp opTag lhs rhs
    else fail s!"parseLlbcRvalue[BinaryOp]: expected 3-elt list"
  | "UnaryOp" =>
    -- `[unop, op]`. unop similarly tagged.
    let arr ← asArr payload
    if h : arr.size = 2 then
      let opTag : String ← match arr[0] with
        | .str s => pure s
        | _ => (do let (t, _) ← asTaggedObj arr[0]; pure t) <|> pure "?"
      let operand ← parseLlbcOperand arr[1]
      return .unaryOp opTag operand
    else fail s!"parseLlbcRvalue[UnaryOp]: expected 2-elt list"
  | "Discriminant" =>
    let p ← parseLlbcPlace payload
    return .discriminant p
  | "Aggregate" =>
    -- `[aggregate_kind, operand list]`
    let arr ← asArr payload
    if h : arr.size = 2 then
      let ak ← parseAggregateKind arr[0]
      let opArr ← asArr arr[1]
      let ops ← opArr.mapM parseLlbcOperand
      return .aggregate ak ops
    else fail s!"parseLlbcRvalue[Aggregate]: expected 2-elt list"
  | "Repeat" =>
    -- `[operand, ty, const_expr]`
    let arr ← asArr payload
    if h : arr.size = 3 then
      let op ← parseLlbcOperand arr[0]
      let ty ← parseLlbcTy arr[1]
      -- best-effort numeric count, else 0
      let cnt : Nat ← (do
        let kJson ← field arr[2] "kind"
        let (cTag, cPay) ← asTaggedObj kJson
        if cTag ≠ "Literal" then return 0
        let (lTag, lPay) ← asTaggedObj cPay
        if lTag ≠ "Scalar" then return 0
        let (_k, v) ← parseScalar lPay
        return if v < 0 then 0 else v.toNat) <|> pure 0
      return .repeat op cnt ty
    else fail s!"parseLlbcRvalue[Repeat]: expected 3-elt list"
  | _ => return .opaque s!"rvalue:{tag}"

end

/-! ### Statements / blocks / switches (mutually recursive) -/

mutual

/-- M9.7b: parse `LlbcStatement` (`{span, kind}` shape per Charon's
    `statement_of_json`; `comments_before` / `id` are ignored). -/
partial def parseLlbcStatement (j : Json) : Result LlbcStatement := do
  let span ← match fieldOpt j "span" with
    | some sj => do let s ← parseSourceSpan sj; pure (some s)
    | none => pure none
  let kindJson ← field j "kind"
  let k ← parseLlbcStatementKind kindJson
  return .mk k span

/-- M9.7b: parse `LlbcStatementKind`. Mirrors Charon's
    `statement_kind_of_json`. -/
partial def parseLlbcStatementKind (j : Json) : Result LlbcStatementKind := do
  match j with
  | .str "Return" => return .returnStmt
  | .str "Nop" => return .nop
  | _ =>
    let (tag, payload) ← asTaggedObj j
    match tag with
    | "Assign" =>
      -- `[place, rvalue]`
      let arr ← asArr payload
      if h : arr.size = 2 then
        let p ← parseLlbcPlace arr[0]
        let r ← parseLlbcRvalue arr[1]
        return .assign p r
      else fail s!"parseLlbcStatementKind[Assign]: expected 2-elt list"
    | "SetDiscriminant" =>
      let arr ← asArr payload
      if h : arr.size = 2 then
        let p ← parseLlbcPlace arr[0]
        let v ← asNat arr[1]
        return .setDiscriminant p v
      else fail s!"parseLlbcStatementKind[SetDiscriminant]: expected 2-elt list"
    | "StorageLive" =>
      let n ← asNat payload
      return .storageLive n
    | "StorageDead" =>
      let n ← asNat payload
      return .storageDead n
    | "Drop" =>
      -- Charon: `[place, fn_ptr, drop_kind]`. We only keep the place.
      let arr ← asArr payload
      if arr.size ≥ 1 then
        let p ← parseLlbcPlace arr[0]!
        return .drop p
      else fail s!"parseLlbcStatementKind[Drop]: expected non-empty list"
    | "Assert" =>
      -- `{assert: {cond, expected, ...}, on_failure: <abort_kind>}`
      let asrt ← field payload "assert"
      let cond ← parseLlbcOperand (← field asrt "cond")
      let expected ← asBool (← field asrt "expected")
      -- We don't structure `abort_kind`; store 0 as the failure id
      -- so the field stays meaningful.
      return .assert cond expected 0
    | "Call" =>
      -- payload is the full `call` record: `{func, args, dest}`.
      let funcJson ← field payload "func"
      let argsArr ← asArr (← field payload "args")
      let args ← argsArr.mapM parseLlbcOperand
      let dst ← parseLlbcPlace (← field payload "dest")
      let func ← (do
        let (fTag, fPay) ← asTaggedObj funcJson
        match fTag with
        | "Regular" =>
          -- fn_ptr = {kind, generics}; kind = {Fun: <fun_id>} | ...
          let fkJson ← field fPay "kind"
          let generics := fPay.getObjValD "generics"
          let (kTag, kPay) ← asTaggedObj fkJson
          match kTag with
          | "Fun" =>
            -- fun_id = {Regular: <fun_decl_id>} | {Builtin: ...}
            let (iTag, iPay) ← asTaggedObj kPay
            match iTag with
            | "Regular" =>
              let n ← asNat iPay
              return FnOperand.funDecl n generics
            | _ => return FnOperand.opaque s!"fun_id:{iTag}"
          | "TraitMethod" =>
            -- `[trait_impl_ref, method_name]` (Charon shape varies).
            let arr ← (asArr kPay) <|> pure #[]
            if h : arr.size = 2 then
              let implRef := arr[0]
              let methodName ← (asStr arr[1]) <|> pure ""
              -- Get trait_impl_id from the ref.
              let tiId : Nat ← (asNat (implRef.getObjValD "id")) <|> pure 0
              return FnOperand.traitMethod tiId methodName generics
            else return FnOperand.opaque s!"trait-method"
          | _ => return FnOperand.opaque s!"fn_ptr.kind:{kTag}"
        | "Dynamic" =>
          let op ← parseLlbcOperand fPay
          return FnOperand.closure op
        | _ => return FnOperand.opaque s!"func:{fTag}") <|>
        pure (FnOperand.opaque "func:opaque")
      return .call { func, args } dst
    | "Abort" => return .abort
    | "Break" =>
      let n ← asNat payload
      return .breakStmt n
    | "Continue" =>
      let n ← asNat payload
      return .continueStmt n
    | "Switch" =>
      let sw ← parseLlbcSwitch payload
      return .switch sw
    | "Loop" =>
      let b ← parseLlbcBlock payload
      return .loopStmt b
    | _ => return .opaque s!"stmt:{tag}"

/-- M9.7b: parse `LlbcBlock`. Mirrors Charon's `block_of_json`:
    `{span, statements}`. -/
partial def parseLlbcBlock (j : Json) : Result LlbcBlock := do
  let span ← match fieldOpt j "span" with
    | some sj => do let s ← parseSourceSpan sj; pure (some s)
    | none => pure none
  let stArr ← asArr (← field j "statements")
  let stmts ← stArr.mapM parseLlbcStatement
  return .mk span stmts

/-- M9.7b: parse `LlbcSwitch`. Mirrors Charon's `switch_of_json`:
    `If`/`SwitchInt`/`Match`. -/
partial def parseLlbcSwitch (j : Json) : Result LlbcSwitch := do
  let (tag, payload) ← asTaggedObj j
  match tag with
  | "If" =>
    let arr ← asArr payload
    if h : arr.size = 3 then
      let op ← parseLlbcOperand arr[0]
      let t ← parseLlbcBlock arr[1]
      let e ← parseLlbcBlock arr[2]
      return .ifBool op t e
    else fail s!"parseLlbcSwitch[If]: expected 3-elt list"
  | "SwitchInt" =>
    -- `[operand, literal_type, [(literal-list, block), ...], default-block]`
    let arr ← asArr payload
    if h : arr.size = 4 then
      let op ← parseLlbcOperand arr[0]
      -- literal_type → IntKind: only `Int`/`UInt` cases produce real
      -- ints; default to u32 if absent.
      let intK : IntKind ← (do
        let (lTag, lPay) ← asTaggedObj arr[1]
        match lTag with
        | "Int" => do let s ← asStr lPay; intKindOfStr s
        | "UInt" => do let s ← asStr lPay; intKindOfStr s
        | _ => pure .u32) <|> pure .u32
      let armsArr ← asArr arr[2]
      let arms ← armsArr.mapM fun pair => do
        let parr ← asArr pair
        if h : parr.size = 2 then
          let litList ← asArr parr[0]
          -- For multi-value arms we take the first literal's value
          -- (a forward-compat lossy decision; Lean side currently
          -- stores `Int × Block` per arm).
          let v : Int ← (do
            if litList.isEmpty then return 0
            let l0 ← parseLiteral litList[0]!
            match l0 with
            | .scalar _ i => return i
            | _ => return 0) <|> pure 0
          let b ← parseLlbcBlock parr[1]
          return (v, b)
        else fail s!"parseLlbcSwitch[SwitchInt.arm]: expected 2-elt pair"
      let dflt ← parseLlbcBlock arr[3]
      return .switchInt op intK arms dflt
    else fail s!"parseLlbcSwitch[SwitchInt]: expected 4-elt list"
  | "Match" =>
    -- `[place, [(variant-id-list, block), ...], default-block?]`
    let arr ← asArr payload
    if h : arr.size = 3 then
      -- Lean's `match_` carries an operand scrutinee; we synthesize
      -- a `LlbcOperand.move` from the place.
      let p ← parseLlbcPlace arr[0]
      let scrut := LlbcOperand.move p
      let armsArr ← asArr arr[1]
      let arms ← armsArr.mapM fun pair => do
        let parr ← asArr pair
        if h : parr.size = 2 then
          let vidArr ← asArr parr[0]
          let vids ← vidArr.mapM asNat
          let b ← parseLlbcBlock parr[1]
          return (vids, b)
        else fail s!"parseLlbcSwitch[Match.arm]: expected 2-elt pair"
      let dflt : Option LlbcBlock ← match arr[2] with
        | .null => pure none
        | other => do let b ← parseLlbcBlock other; pure (some b)
      return .match_ scrut arms dflt
    else fail s!"parseLlbcSwitch[Match]: expected 3-elt list"
  | _ => fail s!"parseLlbcSwitch: unknown tag {tag}"

end

/-! ### Decls -/

/-- M9.7b: parse `ItemMeta`. Charon emits the `name` as a list of
    `path_elem`; Phase B's emitter is expected to render a flat
    pretty-printed `name : String` for the cert. We tolerate both
    shapes: a JSON string is used directly; anything else is rendered
    via `Json.pretty`. -/
def parseItemMeta (j : Json) : Result ItemMeta := do
  let nameJson ← field j "name"
  let name : String := match nameJson with
    | .str s => s
    | other => other.pretty
  let attrInfo := fieldOpaque j "attr_info"
  let sourceText : Option String ← match fieldOpt j "source_text" with
    | some sj => match sj with
      | .str s => pure (some s)
      | _ => pure none
    | none => pure none
  let langItem : Option String ← match fieldOpt j "lang_item" with
    | some sj => match sj with
      | .str s => pure (some s)
      | _ => pure none
    | none => pure none
  let span ← match fieldOpt j "span" with
    | some sj => do
      -- Charon's `span` is `{data: {file_id, beg, end}, ...}`. The
      -- cert-v3 emitter is expected to flatten this to the legacy
      -- `SourceSpan` shape (`file`/`beg_line`/...). Tolerate both:
      -- try the legacy shape first, else `none`.
      (do let s ← parseSourceSpan sj; pure (some s)) <|> pure none
    | none => pure none
  let extra := fieldOpaque j "extra"
  return { name, attrInfo, sourceText, langItem, span, extra }

/-- M9.7b: parse `LlbcGenericParams`. Charon's `generic_params` is a
    big record; we only extract the *names* of regions / type params /
    const generics, plus the trait-clause list. -/
def parseLlbcGenericParams (j : Json) : Result LlbcGenericParams := do
  let extractNames (key : String) : Result (Array String) := do
    match fieldOpt j key with
    | none => pure #[]
    | some v =>
      let arr ← asArr v
      arr.mapM fun pj => do
        -- Each entry is a `{index, name}` (type_param, region_param, etc.).
        match fieldOpt pj "name" with
        | some nj => match nj with | .str s => pure s | _ => pure ""
        | none => pure ""
  let types ← extractNames "types"
  let regions ← extractNames "regions"
  let constGenerics ← extractNames "const_generics"
  let traitClauses : Array TraitClause ← match fieldOpt j "trait_clauses" with
    | some cj =>
      let arr ← asArr cj
      arr.mapM parseTraitClause
    | none => pure #[]
  return { types, regions, constGenerics, traitClauses }

/-- M9.7b: parse `LlbcSignature`. -/
def parseLlbcSignature (j : Json) : Result LlbcSignature := do
  -- Charon `fun_sig` = `{generics, inputs, output, is_unsafe, target}`.
  let inputs : Array LlbcTy ← match fieldOpt j "inputs" with
    | some ij => do
      let arr ← asArr ij
      arr.mapM parseLlbcTy
    | none => pure #[]
  let output : LlbcTy ← match fieldOpt j "output" with
    | some oj => parseLlbcTy oj
    | none => pure (.tOpaque "")
  let generics : LlbcGenericParams ← match fieldOpt j "generics" with
    | some gj => parseLlbcGenericParams gj
    | none => pure {}
  return { inputs, output, generics }

/-- M9.7b: parse `LlbcField` (struct or variant payload field).
    Charon's `field = {span, attr_info, name, ty}`. -/
def parseLlbcField (idx : Nat) (j : Json) : Result LlbcField := do
  let name : Option String ← match fieldOpt j "name" with
    | some nj => match nj with | .str s => pure (some s) | _ => pure none
    | none => pure none
  let ty ← match fieldOpt j "ty" with
    | some tj => parseLlbcTy tj
    | none => pure (.tOpaque "")
  let attrInfo := fieldOpaque j "attr_info"
  return { idx, name, ty, attrInfo }

/-- M9.7b: parse `LlbcVariant`. Charon's `variant = {id, span,
    attr_info, name, fields, discriminant}`. -/
def parseLlbcVariant (j : Json) : Result LlbcVariant := do
  let id ← match fieldOpt j "id" with
    | some ij => asNat ij
    | none => fail "parseLlbcVariant: missing required field 'id'"
  let name ← match fieldOpt j "name" with
    | some nj => asStr nj
    | none => fail "parseLlbcVariant: missing required field 'name'"
  let fieldsArr : Array Json ← match fieldOpt j "fields" with
    | some fj => asArr fj
    | none => pure #[]
  let fields ← fieldsArr.mapIdxM fun i fj => parseLlbcField i fj
  -- discriminant: Charon's `literal = {Scalar: {...}}` etc. Best effort.
  let discriminant : Option Int ← (do
    match fieldOpt j "discriminant" with
    | some dj =>
      let lit ← parseLiteral dj
      match lit with
      | .scalar _ i => pure (some i)
      | _ => pure none
    | none => pure none) <|> pure none
  let attrInfo := fieldOpaque j "attr_info"
  return { id, name, fields, discriminant, attrInfo }

/-- M9.7b: parse `LlbcTypeDeclKind`. Mirrors Charon's
    `type_decl_kind_of_json`. -/
def parseLlbcTypeDeclKind (j : Json) : Result LlbcTypeDeclKind := do
  match j with
  | .str "Opaque" => return .opaque
  | _ =>
    let (tag, payload) ← asTaggedObj j
    match tag with
    | "Struct" =>
      let arr ← asArr payload
      let fields ← arr.mapIdxM fun i fj => parseLlbcField i fj
      return .struct fields
    | "Enum" =>
      let arr ← asArr payload
      let variants ← arr.mapM parseLlbcVariant
      return .enum variants
    | "Union" =>
      let arr ← asArr payload
      let fields ← arr.mapIdxM fun i fj => parseLlbcField i fj
      return .union fields
    | "Alias" =>
      let target ← parseLlbcTy payload
      return .tAlias target
    | _ => return .opaque  -- forward-compat (e.g. TDeclError)

/-- M9.7b: parse `LlbcTypeDecl`. Required fields: `id`, `item_meta`.
    Charon's `def_id` is accepted as the canonical name; cert-v3
    emission uses `id` for symmetry with the rest of the cert. -/
def parseLlbcTypeDecl (j : Json) : Result LlbcTypeDecl := do
  let id ← match (fieldOpt j "id"), (fieldOpt j "def_id") with
    | some ij, _ => asNat ij
    | none, some dj => asNat dj
    | none, none => fail "parseLlbcTypeDecl: missing required field 'id'"
  let itemMeta ← match fieldOpt j "item_meta" with
    | some mj => parseItemMeta mj
    | none => fail "parseLlbcTypeDecl: missing required field 'item_meta'"
  let generics : LlbcGenericParams ← match fieldOpt j "generics" with
    | some gj => parseLlbcGenericParams gj
    | none => pure {}
  let kind : LlbcTypeDeclKind ← match fieldOpt j "kind" with
    | some kj => parseLlbcTypeDeclKind kj
    | none => pure .opaque
  let isTupleStruct : Bool ← match fieldOpt j "is_tuple_struct" with
    | some bj => match bj with | .bool b => pure b | _ => pure false
    | none => pure false
  let isGlobalInitializer : Bool ← match fieldOpt j "is_global_initializer" with
    | some bj => match bj with | .bool b => pure b | _ => pure false
    | none => pure false
  let reprOptions := fieldOpaque j "repr"
  let ptrMetadata := fieldOpaque j "ptr_metadata"
  let src := fieldOpaque j "src"
  return { id, itemMeta, generics, kind, isTupleStruct, reprOptions,
           ptrMetadata, src, isGlobalInitializer }

/-- M9.7b: parse `LlbcFunDecl`. Required: `id`, `item_meta`. -/
def parseLlbcFunDecl (j : Json) : Result LlbcFunDecl := do
  let id ← match (fieldOpt j "id"), (fieldOpt j "def_id") with
    | some ij, _ => asNat ij
    | none, some dj => asNat dj
    | none, none => fail "parseLlbcFunDecl: missing required field 'id'"
  let itemMeta ← match fieldOpt j "item_meta" with
    | some mj => parseItemMeta mj
    | none => fail "parseLlbcFunDecl: missing required field 'item_meta'"
  let signature : LlbcSignature ← match fieldOpt j "signature" with
    | some sj => parseLlbcSignature sj
    | none => pure {}
  -- Body: Charon's `body = {Structured: {body: <block>, locals: ...}}` |
  -- `{Unstructured: ...}` | `Opaque`. We pull the LLBC block when
  -- present, else `none`.
  let body : Option LlbcBlock ← (do
    match fieldOpt j "body" with
    | none => pure none
    | some bj => match bj with
      | .null => pure none
      | _ =>
        -- Try direct block-shape first, then nested under `Structured`.
        (do let b ← parseLlbcBlock bj; pure (some b)) <|>
        (do
          let (bTag, bPay) ← asTaggedObj bj
          match bTag with
          | "Structured" =>
            let inner := bPay.getObjValD "body"
            match inner with
            | .null => pure none
            | _ => do let b ← parseLlbcBlock inner; pure (some b)
          | _ => pure none) <|> pure none) <|> pure none
  -- locals types: Charon's `locals = {arg_count, locals: [{index, name, ty}, …]}`.
  let localsTypes : Array LlbcTy ← (do
    match fieldOpt j "locals" with
    | none => pure #[]
    | some lj =>
      -- accept either a direct array or a record with `locals`.
      let arr ← (asArr lj) <|> (do
        match fieldOpt lj "locals" with
        | some inner => asArr inner
        | none => pure #[])
      arr.mapM fun ej => do
        match fieldOpt ej "ty" with
        | some tj => parseLlbcTy tj
        | none => pure (.tOpaque "")) <|> pure #[]
  let isGlobalInitializer : Bool ← (do
    match fieldOpt j "is_global_initializer" with
    | some bj => match bj with
      | .bool b => pure b
      | .null => pure false
      | _ => pure true   -- a non-null `Some <id>` ⇒ initializer
    | none => pure false) <|> pure false
  let src := fieldOpaque j "src"
  return { id, itemMeta, signature, body, localsTypes,
           isGlobalInitializer, src }

/-- M9.7b: parse `LlbcTraitMethod`. -/
def parseLlbcTraitMethod (j : Json) : Result LlbcTraitMethod := do
  let name ← match fieldOpt j "name" with
    | some nj => asStr nj
    | none => fail "parseLlbcTraitMethod: missing required field 'name'"
  let signature : LlbcSignature ← match fieldOpt j "signature" with
    | some sj => parseLlbcSignature sj
    | none => pure {}
  let hasDefault : Bool ← match fieldOpt j "has_default" with
    | some bj => match bj with | .bool b => pure b | _ => pure false
    | none => pure false
  let defaultFnId : Option Nat ← match fieldOpt j "default_fn_id" with
    | some dj => do let n ← asNat dj; pure (some n)
    | none => pure none
  return { name, signature, hasDefault, defaultFnId }

/-- M9.7b: parse `LlbcTraitDecl`. Charon's shape carries `methods`
    as an indexed list `[ [method_id, binder<trait_method>], … ]`;
    we flatten by mapping each second-element binder's inner value. -/
def parseLlbcTraitDecl (j : Json) : Result LlbcTraitDecl := do
  let id ← match (fieldOpt j "id"), (fieldOpt j "def_id") with
    | some ij, _ => asNat ij
    | none, some dj => asNat dj
    | none, none => fail "parseLlbcTraitDecl: missing required field 'id'"
  let itemMeta ← match fieldOpt j "item_meta" with
    | some mj => parseItemMeta mj
    | none => fail "parseLlbcTraitDecl: missing required field 'item_meta'"
  let generics : LlbcGenericParams ← match fieldOpt j "generics" with
    | some gj => parseLlbcGenericParams gj
    | none => pure {}
  let methods : Array LlbcTraitMethod ← (do
    match fieldOpt j "methods" with
    | none => pure #[]
    | some mj =>
      let arr ← asArr mj
      arr.mapM fun entry => do
        -- Accept either a flat method object, or Charon's indexed
        -- shape `[id, binder<method>]`. Binders carry their inner
        -- value under `skip_binder`.
        match entry with
        | .arr e =>
          if h : e.size = 2 then
            let inner := e[1]
            let v : Json := inner.getObjValD "skip_binder"
            let target := if v.isNull then inner else v
            parseLlbcTraitMethod target
          else parseLlbcTraitMethod entry
        | _ =>
          let v : Json := entry.getObjValD "skip_binder"
          parseLlbcTraitMethod (if v.isNull then entry else v)) <|> pure #[]
  let assocTypes : Array String ← (do
    match fieldOpt j "types" with
    | none => pure #[]
    | some tj =>
      let arr ← asArr tj
      arr.mapM fun e => match e with
        | .arr ae => if h : ae.size ≥ 1 then asStr ae[0]! <|> pure "" else pure ""
        | _ => pure "") <|> pure #[]
  let assocConsts : Array (String × LlbcTy) ← (do
    match fieldOpt j "consts" with
    | none => pure #[]
    | some cj =>
      let arr ← asArr cj
      arr.mapM fun e => match e with
        | .arr ae => if h : ae.size ≥ 2 then do
            let nm ← (asStr ae[0]!) <|> pure ""
            let ty ← (parseLlbcTy ae[1]!) <|> pure (LlbcTy.tOpaque "")
            pure (nm, ty)
          else pure ("", LlbcTy.tOpaque "")
        | _ => pure ("", LlbcTy.tOpaque "")) <|> pure #[]
  let impliedClauses : Array TraitClause ← (do
    match fieldOpt j "implied_clauses" with
    | none => pure #[]
    | some cj =>
      let arr ← asArr cj
      arr.mapM parseTraitClause) <|> pure #[]
  let vtable := fieldOpaque j "vtable"
  return { id, itemMeta, generics, methods, assocTypes, assocConsts,
           impliedClauses, vtable }

/-- M9.7b: parse `LlbcTraitImplMethod`. -/
def parseLlbcTraitImplMethod (j : Json) : Result LlbcTraitImplMethod := do
  let name ← match fieldOpt j "name" with
    | some nj => asStr nj
    | none => fail "parseLlbcTraitImplMethod: missing required field 'name'"
  let fnId ← match (fieldOpt j "fn_id"), (fieldOpt j "id") with
    | some fj, _ => asNat fj
    | none, some ij => asNat ij
    | none, none => fail "parseLlbcTraitImplMethod: missing required field 'fn_id'"
  return { name, fnId }

/-- M9.7b: parse `LlbcTraitImpl`. -/
def parseLlbcTraitImpl (j : Json) : Result LlbcTraitImpl := do
  let id ← match (fieldOpt j "id"), (fieldOpt j "def_id") with
    | some ij, _ => asNat ij
    | none, some dj => asNat dj
    | none, none => fail "parseLlbcTraitImpl: missing required field 'id'"
  let itemMeta ← match fieldOpt j "item_meta" with
    | some mj => parseItemMeta mj
    | none => fail "parseLlbcTraitImpl: missing required field 'item_meta'"
  let traitDeclId ← match fieldOpt j "trait_decl_id" with
    | some tj => asNat tj
    | none =>
      -- Charon shape: `impl_trait.id` (a trait_decl_ref).
      match fieldOpt j "impl_trait" with
      | some itj => (asNat (itj.getObjValD "id")) <|> pure 0
      | none => pure 0
  let implTrait := fieldOpaque j "impl_trait"
  let selfTypeDeclId : Option Nat ← match fieldOpt j "self_type_decl_id" with
    | some sj => do let n ← asNat sj; pure (some n)
    | none => pure none
  let selfType : LlbcTy ← match fieldOpt j "self_type" with
    | some sj => parseLlbcTy sj
    | none => pure (.tOpaque "")
  let generics : LlbcGenericParams ← match fieldOpt j "generics" with
    | some gj => parseLlbcGenericParams gj
    | none => pure {}
  let methods : Array LlbcTraitImplMethod ← (do
    match fieldOpt j "methods" with
    | none => pure #[]
    | some mj =>
      let arr ← asArr mj
      arr.mapM fun entry => do
        -- Like for trait decls, accept indexed `[id, binder<method>]`
        -- or flat shapes.
        match entry with
        | .arr e =>
          if h : e.size = 2 then
            let inner := e[1]
            let v : Json := inner.getObjValD "skip_binder"
            let target := if v.isNull then inner else v
            -- A binder's inner value is a `fun_decl_ref` `{id, generics}`
            -- in the impl-method case; map it to a fnId.
            (parseLlbcTraitImplMethod target) <|>
            (do
              let fid ← (asNat (target.getObjValD "id")) <|> pure 0
              pure { name := "", fnId := fid })
          else parseLlbcTraitImplMethod entry
        | _ => parseLlbcTraitImplMethod entry) <|> pure #[]
  let assocConsts : Array (String × Nat) ← (do
    match fieldOpt j "consts" with
    | none => pure #[]
    | some cj =>
      let arr ← asArr cj
      arr.mapM fun e => match e with
        | .arr ae => if h : ae.size ≥ 2 then do
            let nm ← (asStr ae[0]!) <|> pure ""
            let gid ← (asNat (ae[1]!.getObjValD "id")) <|> pure 0
            pure (nm, gid)
          else pure ("", 0)
        | _ => pure ("", 0)) <|> pure #[]
  let assocTypes : Array (String × LlbcTy) ← (do
    match fieldOpt j "types" with
    | none => pure #[]
    | some tj =>
      let arr ← asArr tj
      arr.mapM fun e => match e with
        | .arr ae => if h : ae.size ≥ 2 then do
            let nm ← (asStr ae[0]!) <|> pure ""
            let ty ← (parseLlbcTy ae[1]!) <|> pure (LlbcTy.tOpaque "")
            pure (nm, ty)
          else pure ("", LlbcTy.tOpaque "")
        | _ => pure ("", LlbcTy.tOpaque "")) <|> pure #[]
  let impliedTraitRefs := fieldOpaque j "implied_trait_refs"
  let vtable := fieldOpaque j "vtable"
  return { id, itemMeta, traitDeclId, implTrait, selfTypeDeclId,
           selfType, generics, methods, assocConsts, assocTypes,
           impliedTraitRefs, vtable }

/-- M9.7b: top-level parser for the cert v3 `llbc_program` blob. All
    sub-arrays default to empty when absent; opaque blobs default to
    `.null`. -/
def parseLlbcProgram (j : Json) : Result LlbcProgram := do
  let typeDecls : Array LlbcTypeDecl ← match fieldOpt j "type_decls" with
    | some tj =>
      let arr ← asArr tj
      arr.mapM parseLlbcTypeDecl
    | none => pure #[]
  let funDecls : Array LlbcFunDecl ← match fieldOpt j "fun_decls" with
    | some fj =>
      let arr ← asArr fj
      arr.mapM parseLlbcFunDecl
    | none => pure #[]
  let traitDecls : Array LlbcTraitDecl ← match fieldOpt j "trait_decls" with
    | some tj =>
      let arr ← asArr tj
      arr.mapM parseLlbcTraitDecl
    | none => pure #[]
  let traitImpls : Array LlbcTraitImpl ← match fieldOpt j "trait_impls" with
    | some tj =>
      let arr ← asArr tj
      arr.mapM parseLlbcTraitImpl
    | none => pure #[]
  let globalDecls := fieldOpaque j "global_decls"
  let charonVersion : String ← match fieldOpt j "charon_version" with
    | some cj => match cj with | .str s => pure s | _ => pure ""
    | none => pure ""
  let extra := fieldOpaque j "extra"
  return { typeDecls, funDecls, traitDecls, traitImpls, globalDecls,
           charonVersion, extra }

def parseCrateCert (j : Json) : Result CrateCert := do
  let fmtVersion ← asNat (← field j "fmt_version")
  -- M9.6: accept both v1 (pre-Option-C) and v2 (Option C hint
  -- schema). All hint fields are optional under v2, so the parser
  -- behaves identically on a hint-free v2 cert.
  if fmtVersion ≠ 1 ∧ fmtVersion ≠ 2 then
    fail s!"unsupported cert fmt_version: {fmtVersion} (expected 1 or 2)"
  else
    let crateHash ← asStr (← field j "crate_hash")
    -- `type_decls` is optional for back-compat with pre-M9.5b certs.
    let typeDecls : Array TypeDecl ← match (j.getObjVal? "type_decls").toOption with
      | some tj => do
        let arr ← asArr tj
        arr.mapM parseTypeDecl
      | none => pure #[]
    -- M9.5l: `trait_decls` / `trait_impls` are optional for
    -- back-compat with pre-M9.5l certs.
    let traitDecls : Array TraitDecl ← match (j.getObjVal? "trait_decls").toOption with
      | some tj => do
        let arr ← asArr tj
        arr.mapM parseTraitDecl
      | none => pure #[]
    let traitImpls : Array TraitImpl ← match (j.getObjVal? "trait_impls").toOption with
      | some tj => do
        let arr ← asArr tj
        arr.mapM parseTraitImpl
      | none => pure #[]
    let fnArr ← asArr (← field j "functions")
    let functions ← fnArr.mapM parseFunCert
    return { fmtVersion, crateHash, typeDecls, traitDecls, traitImpls, functions }

/-- Top-level entry: parse a cert JSON string. -/
def parseCrateCertStr (s : String) : Result CrateCert := do
  let j ← Lean.Json.parse s
  parseCrateCert j

/-- Read a cert from disk. -/
def readCrateCert (path : System.FilePath) : IO CrateCert := do
  let s ← IO.FS.readFile path
  match parseCrateCertStr s with
  | .ok cc => return cc
  | .error e => throw (IO.userError s!"cert parse failed at {path}: {e}")

end AeneasCheck.Json
