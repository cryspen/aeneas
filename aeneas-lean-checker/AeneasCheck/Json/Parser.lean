import Lean.Data.Json
import AeneasCheck.Raw.CertEvent

/-!
JSON → Raw parser for the certificate format defined in
`src/cert/cert_schema.json` (format version 1).

Pattern: monadic `Except String α` helpers built on `Lean.Json`'s
core accessors (`getObjVal?`, `getArr?`, …). Constructor encoding
matches Serde's tagged-enum convention:
* nullary variants: JSON string `"VariantName"`
* payload variants: object `{"VariantName": <payload>}`
-/

namespace AeneasCheck.Json

open Lean (Json)
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
      return .mutBorrow loan place symval
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
      return .reborrow child parent place
    | "EvCall" =>
      let fn ← asNat (← field payload "fn")
      let fnName ← asStr (← field payload "fn_name")
      let callId ← asNat (← field payload "call_id")
      let argsArr ← asArr (← field payload "args")
      let args ← argsArr.mapM parseSymExpr
      let dst ← parsePlace (← field payload "dst")
      let raArr ← asArr (← field payload "region_abs")
      let regionAbs ← raArr.mapM asNat
      return .call fn callId fnName args dst regionAbs
    | "EvEndAbs" =>
      let abs ← asNat (← field payload "abs")
      let fvArr ← asArr (← field payload "final_values")
      let finalValues ← fvArr.mapM parseSymExpr
      return .endAbs abs finalValues
    | "EvProj" =>
      let abs ← asNat (← field payload "abs")
      let place ← parsePlace (← field payload "place")
      let symval ← asNat (← field payload "symval")
      return .proj abs place symval
    | "EvJoin" =>
      let left ← parseStateSummary (← field payload "left")
      let right ← parseStateSummary (← field payload "right")
      let result ← parseStateSummary (← field payload "result")
      return .join left right result
    | "EvLoopInv" =>
      let loopId ← asNat (← field payload "loop_id")
      let invariant ← parseStateSummary (← field payload "invariant")
      return .loopInv loopId invariant
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

def parseCrateCert (j : Json) : Result CrateCert := do
  let fmtVersion ← asNat (← field j "fmt_version")
  if fmtVersion ≠ 1 then
    fail s!"unsupported cert fmt_version: {fmtVersion} (expected 1)"
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
