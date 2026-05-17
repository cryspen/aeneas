import Lean.Data.Json
import AeneasCheck.Raw.CertEvent
import AeneasCheck.Raw.Literal

/-!
Raw, structured Lean mirrors of Charon's LLBC subtree (cert v3).

This file is the Lean side of the embedded `llbc_program` blob that
cert v3 (M9.7) carries alongside the per-function event traces. The
constructors mirror the relevant subset of Charon's OCaml AST as
generated under `charon/charon-ml/src/generated/Generated_Types.ml`,
`Generated_Expressions.ml`, and `Generated_LlbcAst.ml`. The mirror is
intentionally partial: we structure the parts the checker introspects
(types, places, statements, signatures, decls) and tolerate the rest
behind opaque `Lean.Json` payloads or `String` repr fallbacks. Any
field we don't recognize is preserved under a `Json := .null` slot so
the parser (Phase A.2) can keep stuffing it forward without losing
data on schema drift.

Phase A.1 of M9.7 (this file): types only — no parser, no replayer
glue, no `CrateCert` extension. Imports stay inside the existing Raw
layer + Lean core (`Lean.Data.Json`).

Convention recap (cf. `Raw/CertEvent.lean`):

* `namespace AeneasCheck.Raw` (close at bottom).
* Every type derives `Repr` and `Inhabited`. No `BEq` / `DecidableEq`
  unless a later milestone needs them.
* Nested inductives recurse through `Array` directly — Lean accepts
  this because `Array` is implemented via `List`, as `Raw.RawTy.adt`
  already exhibits.
* Re-use `Raw.SourceSpan` (from `Raw/CertEvent.lean`),
  `Raw.TraitClause`, `Raw.LitTy`, `Raw.IntKind`, `Raw.RefKind`,
  `Raw.Lit` (from `Raw/Types.lean` / `Raw/Literal.lean`).
-/

namespace AeneasCheck.Raw

/-- Local alias so we can write `Json` without the `Lean.` prefix. -/
abbrev Json := Lean.Json

/-- `Repr` instance for `Lean.Json` via its built-in pretty-printer.
    Lean's stdlib provides `Json.pretty` but no `Repr`, so we wire one
    up here so structures with `Json` fields can keep `deriving Repr`. -/
instance : Repr Json where
  reprPrec j _ := j.pretty

/-- `Inhabited` instance for `Lean.Json`, defaulting to `null`. -/
instance : Inhabited Json := ⟨.null⟩

/-- M9.7a: mirror of Charon's `item_meta` (`Generated_Types.ml:933`).

    Carries the pretty-printed `name` (OCaml-side has already resolved
    crate path / generics), the source span (when Charon has one),
    the optional language-item tag and source-text snippet, and an
    opaque `attrInfo` blob for the full `#[attr]` set. `extra`
    catches any field we haven't pulled out yet. -/
structure ItemMeta where
  name : String
  attrInfo : Json := .null
  sourceText : Option String := none
  langItem : Option String := none
  span : Option SourceSpan := none
  extra : Json := .null
  deriving Repr, Inhabited

/-! ## LLBC types -/

/-- M9.7a: structured replacement for `Raw.RawTy`'s opaque-string
    shape. Mirrors Charon's `ty` / `ty_kind` from
    `Generated_Types.ml`. Const-generic non-literal lengths and other
    things we can't structure yet fall back to `tOpaque`. -/
inductive LlbcTy
  /-- A primitive literal type (`bool`, `char`, integers, floats). -/
  | litTy (k : LitTy)
  /-- ADT application: a `TypeDeclId` head applied to type args. -/
  | tAdt (id : Nat) (args : Array LlbcTy)
  /-- Tuple type. -/
  | tTuple (args : Array LlbcTy)
  /-- Reference: shared `&'r T` or mutable `&'r mut T`. -/
  | tRef (region : Nat) (inner : LlbcTy) (kind : RefKind)
  /-- De-Bruijn-style type variable (Charon's `TVar (Free K)`). -/
  | tVar (index : Nat)
  /-- The never type `!`. -/
  | tNever
  /-- Raw pointer (`*const T` / `*mut T`). -/
  | tRawPtr (inner : LlbcTy) (kind : RefKind)
  /-- Fixed-length array. Const-generic non-literal lengths fall back
      to `tOpaque`. -/
  | tArray (elem : LlbcTy) (len : Nat)
  /-- Slice `[T]`. -/
  | tSlice (elem : LlbcTy)
  /-- The `str` type. -/
  | tStr
  /-- Function-pointer type `fn(T1, ..., Tn) -> R`. -/
  | tFn (inputs : Array LlbcTy) (output : LlbcTy)
  /-- `dyn Trait` — the trait obligations are kept opaque for now. -/
  | tDynTrait (traitId : Nat)
  /-- Fallback for any LLBC type we don't yet structure (closures,
      foreigns, const-generic-len arrays, …). -/
  | tOpaque (repr : String)
  deriving Repr, Inhabited

/-! ## Places, operands, rvalues -/

/-- M9.7a: structured projection element. Mirrors
    `Generated_Expressions.ml`'s `projection_elem`, with carried
    typing context for `field` (the existing flat `Raw.ProjElem.field`
    only has the field id). -/
inductive LlbcProjElem
  /-- `*p` — dereference. -/
  | deref
  /-- `p.field` (struct or variant). `variantId` is `some` only for
      enum-variant field projections; `typeDecl` is the ADT id. -/
  | field (typeDecl : Nat) (variantId : Option Nat) (fieldId : Nat)
  /-- The metadata half of a fat pointer. -/
  | ptrMetadata
  /-- Direct indexing into an array/slice. `constOffset` is `some` for
      compile-time-known indices. -/
  | projIndex (constOffset : Option Nat)
  /-- A subslice projection `&p[from..to]`. -/
  | subslice (from_ to_ : Option Nat) (fromEnd : Bool)
  deriving Repr, Inhabited

/-- M9.7a: a place — `local + projection*` with the place's static
    type. Mirrors `Generated_Expressions.ml`'s `place`. -/
structure LlbcPlace where
  local_ : Nat
  projection : Array LlbcProjElem
  ty : LlbcTy
  deriving Repr, Inhabited

/-- M9.7a: an operand. Mirrors `Generated_Expressions.ml:174`. -/
inductive LlbcOperand
  /-- Move-out of a place. -/
  | move (p : LlbcPlace)
  /-- Copy-from a place. -/
  | copy (p : LlbcPlace)
  /-- A primitive literal constant. -/
  | const (lit : Lit)
  /-- Fallback for any non-literal constant operand (function pointer,
      promoted constant, …). -/
  | constOpaque (repr : String)
  deriving Repr, Inhabited

/-- M9.7a: aggregate kinds for `LlbcRvalue.aggregate`. Mirrors
    `Generated_Expressions.ml`'s `aggregate_kind`. -/
inductive AggregateKind
  /-- ADT construction. `variantId` is `some` for enum variants;
      `fieldId` is `some` for the single-field "union" shape. -/
  | adt (typeId : Nat) (variantId : Option Nat) (fieldId : Option Nat)
  /-- Array literal `[e1, ..., en]`. -/
  | array (ty : LlbcTy)
  /-- Tuple literal `(e1, ..., en)`. -/
  | tuple
  /-- Closure capture aggregate. -/
  | closure (fnId : Nat)
  /-- Raw-pointer aggregate (`*const`/`*mut` construction). -/
  | raw_ptr (kind : RefKind)
  deriving Repr, Inhabited

/-- M9.7a: rvalue. Mirrors `Generated_Expressions.ml:247`. -/
inductive LlbcRvalue
  /-- `use` an operand directly. -/
  | use (op : LlbcOperand)
  /-- Take a reference to a place. -/
  | ref (place : LlbcPlace) (kind : RefKind)
  /-- Unary operator. The operator name is the flat string tag the
      OCaml side renders (e.g. `"Not"`, `"Neg"`). -/
  | unaryOp (op : String) (operand : LlbcOperand)
  /-- Binary operator. Like `unaryOp`, the operator name is the flat
      OCaml tag (`"Add"`, `"AddPanic"`, `"AddWrap"`, `"Eq"`, …). -/
  | binaryOp (op : String) (lhs rhs : LlbcOperand)
  /-- Reading from a global decl. -/
  | globalRef (globalId : Nat) (kind : RefKind)
  /-- Read the discriminant of a place. -/
  | discriminant (place : LlbcPlace)
  /-- Aggregate construction (ADT / array / tuple / closure / raw_ptr). -/
  | aggregate (kind : AggregateKind) (operands : Array LlbcOperand)
  /-- Repeat-expression `[op; count]`. -/
  | «repeat» (op : LlbcOperand) (count : Nat) (ty : LlbcTy)
  /-- Take a raw pointer to a place. -/
  | rawPtr (place : LlbcPlace) (kind : RefKind)
  /-- Fallback for any rvalue we can't structure yet. -/
  | opaque (repr : String)
  deriving Repr, Inhabited

/-! ## Function-call shape -/

/-- M9.7a: the callee in a function-call statement. -/
inductive FnOperand
  /-- Direct call to a known `FunDecl`. Generics are kept opaque
      until a later milestone needs them structured. -/
  | funDecl (id : Nat) (generics : Json)
  /-- Call dispatched through a trait impl. `methodName` is the
      trait's method name (matches `LlbcTraitMethod.name`). -/
  | traitMethod (traitImplId : Nat) (methodName : String) (generics : Json)
  /-- Call through a closure value. -/
  | closure (op : LlbcOperand)
  /-- Fallback for any callee shape we can't structure yet. -/
  | opaque (repr : String)
  deriving Repr, Inhabited

/-- M9.7a: a function-call descriptor used by `LlbcStatement.call`. -/
structure LlbcCall where
  func : FnOperand
  args : Array LlbcOperand
  deriving Repr, Inhabited

/-! ## Statements, blocks, switches

    Statements / blocks / switches are mutually recursive: a statement
    can hold a block (for loops, switch arms), and a block is a
    sequence of statements. We declare the `kind` as a mutually-
    recursive inductive group with `LlbcBlock` and `LlbcSwitch`, then
    wrap `LlbcStatementKind` in a struct that adds the span. -/

mutual

/-- M9.7a: statement-kind. Mirrors `Generated_LlbcAst.ml:11`. The
    span / wrapping struct is `LlbcStatement` below. -/
inductive LlbcStatementKind
  /-- `place = rhs`. -/
  | assign (place : LlbcPlace) (rhs : LlbcRvalue)
  /-- Explicit discriminant write (enum variant tag). -/
  | setDiscriminant (place : LlbcPlace) (variantId : Nat)
  /-- `StorageLive(local)`. -/
  | storageLive (local_ : Nat)
  /-- `StorageDead(local)`. -/
  | storageDead (local_ : Nat)
  /-- Run drop glue for `place`. -/
  | drop (place : LlbcPlace)
  /-- `assert cond == expected else <onFailure>`. -/
  | assert (cond : LlbcOperand) (expected : Bool) (onFailure : Nat)
  /-- A function call. `dst` is where the result is stored. -/
  | call (callee : LlbcCall) (dst : LlbcPlace)
  /-- No-op. -/
  | nop
  /-- A loop. The body re-enters until a `break`. -/
  | loopStmt (body : LlbcBlock)
  /-- A switch / match dispatch. -/
  | switch (sw : LlbcSwitch)
  /-- Sequence of statements (a nested block). -/
  | block (body : LlbcBlock)
  /-- `return`. -/
  | returnStmt
  /-- `abort` (panic, UB marker). -/
  | abort
  /-- `break depth`. -/
  | breakStmt (depth : Nat)
  /-- `continue depth`. -/
  | continueStmt (depth : Nat)
  /-- Fallback for any statement shape we can't structure yet. -/
  | opaque (repr : String)

/-- M9.7a: a block — a sequence of statements with an optional span.
    Mirrors `Generated_LlbcAst.ml:9`. -/
inductive LlbcBlock
  | mk (span : Option SourceSpan) (statements : Array LlbcStatement) : LlbcBlock

/-- M9.7a: a switch / match. Mirrors `Generated_LlbcAst.ml:79`. -/
inductive LlbcSwitch
  /-- `if op { then_ } else { else_ }`. -/
  | ifBool (op : LlbcOperand) (then_ else_ : LlbcBlock)
  /-- `switch op : intTy { v1 => arm1; ...; _ => default }`. Values
      are `Int` because they can be negative for signed-int switches. -/
  | switchInt
      (op : LlbcOperand)
      (intTy : IntKind)
      (arms : Array (Int × LlbcBlock))
      («default» : LlbcBlock)
  /-- `match scrutinee { variants_i => arm_i; ...; _ => default }`.
      Each arm covers a set of variant ids (the `Array Nat`). The
      default block is `none` when the match is exhaustive over the
      scrutinee's variants. -/
  | match_
      (scrutinee : LlbcOperand)
      (arms : Array (Array Nat × LlbcBlock))
      («default» : Option LlbcBlock)

/-- M9.7a: a full statement — kind plus span. -/
inductive LlbcStatement
  | mk (kind : LlbcStatementKind) (span : Option SourceSpan) : LlbcStatement

end

namespace LlbcStatement
/-- Build a statement with no span. -/
def ofKind (k : LlbcStatementKind) : LlbcStatement := .mk k none
end LlbcStatement

namespace LlbcBlock
/-- Empty block, no span, no statements. -/
def empty : LlbcBlock := .mk none #[]
end LlbcBlock

-- Recursive types built via `mutual` don't get a free `deriving`
-- block; provide manual `Inhabited` instances so downstream
-- structures can use `default`.
instance : Inhabited LlbcStatementKind := ⟨.nop⟩
instance : Inhabited LlbcBlock := ⟨.mk none #[]⟩
instance : Inhabited LlbcSwitch := ⟨.ifBool (.constOpaque "") .empty .empty⟩
instance : Inhabited LlbcStatement := ⟨.mk .nop none⟩

-- Manual `Repr` for the mutual block. Each clause prints the
-- constructor name + a token-budgeted argument list; sufficient for
-- debug output without committing to a pretty-printer.
mutual

partial def reprLlbcStatementKind : LlbcStatementKind → Nat → Std.Format
  | .assign p r, _ => f!"LlbcStatementKind.assign {repr p} {repr r}"
  | .setDiscriminant p v, _ => f!"LlbcStatementKind.setDiscriminant {repr p} {v}"
  | .storageLive l, _ => f!"LlbcStatementKind.storageLive {l}"
  | .storageDead l, _ => f!"LlbcStatementKind.storageDead {l}"
  | .drop p, _ => f!"LlbcStatementKind.drop {repr p}"
  | .assert c e f, _ => f!"LlbcStatementKind.assert {repr c} {e} {f}"
  | .call c d, _ => f!"LlbcStatementKind.call {repr c} {repr d}"
  | .nop, _ => "LlbcStatementKind.nop"
  | .loopStmt b, n => f!"LlbcStatementKind.loopStmt ({reprLlbcBlock b n})"
  | .switch sw, n => f!"LlbcStatementKind.switch ({reprLlbcSwitch sw n})"
  | .block b, n => f!"LlbcStatementKind.block ({reprLlbcBlock b n})"
  | .returnStmt, _ => "LlbcStatementKind.returnStmt"
  | .abort, _ => "LlbcStatementKind.abort"
  | .breakStmt d, _ => f!"LlbcStatementKind.breakStmt {d}"
  | .continueStmt d, _ => f!"LlbcStatementKind.continueStmt {d}"
  | .opaque s, _ => f!"LlbcStatementKind.opaque {repr s}"

partial def reprLlbcStatement : LlbcStatement → Nat → Std.Format
  | .mk k s, n => f!"LlbcStatement.mk ({reprLlbcStatementKind k n}) {repr s}"

partial def reprLlbcBlock : LlbcBlock → Nat → Std.Format
  | .mk s stmts, n =>
    let body := stmts.foldl (init := (Std.Format.nil : Std.Format))
      (fun acc st => acc ++ ", " ++ reprLlbcStatement st n)
    f!"LlbcBlock.mk {repr s} #[{body}]"

partial def reprLlbcSwitch : LlbcSwitch → Nat → Std.Format
  | .ifBool op t e, n =>
    f!"LlbcSwitch.ifBool {repr op} ({reprLlbcBlock t n}) ({reprLlbcBlock e n})"
  | .switchInt op ity arms d, n =>
    let armsFmt := arms.foldl (init := (Std.Format.nil : Std.Format))
      (fun acc (v, b) => acc ++ f!", ({v}, {reprLlbcBlock b n})")
    f!"LlbcSwitch.switchInt {repr op} {repr ity} #[{armsFmt}] ({reprLlbcBlock d n})"
  | .match_ s arms d, n =>
    let armsFmt := arms.foldl (init := (Std.Format.nil : Std.Format))
      (fun acc (vs, b) => acc ++ f!", ({repr vs}, {reprLlbcBlock b n})")
    let dFmt := match d with
      | some b => f!"some ({reprLlbcBlock b n})"
      | none => "none"
    f!"LlbcSwitch.match_ {repr s} #[{armsFmt}] {dFmt}"

end

instance : Repr LlbcStatementKind := ⟨reprLlbcStatementKind⟩
instance : Repr LlbcStatement := ⟨reprLlbcStatement⟩
instance : Repr LlbcBlock := ⟨reprLlbcBlock⟩
instance : Repr LlbcSwitch := ⟨reprLlbcSwitch⟩

/-! ## Signatures, generics, declarations -/

/-- M9.7a: generic params on a decl. Mirrors `Generated_Types.ml:485`
    with only the fields the checker needs. Region / const-generic
    bodies stay opaque names for now. -/
structure LlbcGenericParams where
  types : Array String := #[]
  constGenerics : Array String := #[]
  traitClauses : Array TraitClause := #[]
  regions : Array String := #[]
  deriving Repr, Inhabited

/-- M9.7a: a function signature in structured form. -/
structure LlbcSignature where
  inputs : Array LlbcTy := #[]
  output : LlbcTy := .tOpaque ""
  generics : LlbcGenericParams := {}
  deriving Repr, Inhabited

/-- M9.7a: a single ADT field (struct field or variant payload field). -/
structure LlbcField where
  idx : Nat
  /-- `none` for tuple-style positional fields; the emitter falls back
      to `fieldK`. -/
  name : Option String
  ty : LlbcTy
  attrInfo : Json := .null
  deriving Repr, Inhabited

/-- M9.7a: a single enum variant. `discriminant` is the explicit
    `Foo = 5` value when Charon recorded one, `none` otherwise. -/
structure LlbcVariant where
  id : Nat
  name : String
  fields : Array LlbcField := #[]
  discriminant : Option Int := none
  attrInfo : Json := .null
  deriving Repr, Inhabited

/-- M9.7a: kind of a type decl. -/
inductive LlbcTypeDeclKind
  | struct (fields : Array LlbcField)
  | enum (variants : Array LlbcVariant)
  | union (fields : Array LlbcField)
  | tAlias (target : LlbcTy)
  | opaque
  deriving Repr, Inhabited

/-- M9.7a: full structured type-decl. Mirrors `Generated_Types.ml`'s
    `type_decl`. `reprOptions` carries `#[repr(...)]` attributes and
    `ptrMetadata` carries Charon's ptr-metadata info, both opaque
    until a future milestone introspects them. -/
structure LlbcTypeDecl where
  id : Nat
  itemMeta : ItemMeta
  generics : LlbcGenericParams := {}
  kind : LlbcTypeDeclKind := .opaque
  isTupleStruct : Bool := false
  reprOptions : Json := .null
  ptrMetadata : Json := .null
  /-- Charon's `src` field: TopLevel / TraitDecl / TraitImpl source
      context. Kept opaque. -/
  src : Json := .null
  isGlobalInitializer : Bool := false
  deriving Repr, Inhabited

/-- M9.7a: full structured function-decl. `body = none` for opaque /
    extern functions. `localsTypes` is the per-local type table that
    Level R uses to typecheck place projections against the declared
    local type. -/
structure LlbcFunDecl where
  id : Nat
  itemMeta : ItemMeta
  signature : LlbcSignature := {}
  body : Option LlbcBlock := none
  /-- Types of every local in the body, in declaration order. Empty
      when `body = none`. -/
  localsTypes : Array LlbcTy := #[]
  isGlobalInitializer : Bool := false
  src : Json := .null
  deriving Repr, Inhabited

/-- M9.7a: one method declared in a trait. `defaultFnId` is `some`
    when `hasDefault = true` and points to the FunDeclId of the
    default body. -/
structure LlbcTraitMethod where
  name : String
  signature : LlbcSignature := {}
  hasDefault : Bool := false
  defaultFnId : Option Nat := none
  deriving Repr, Inhabited

/-- M9.7a: a full structured trait decl. -/
structure LlbcTraitDecl where
  id : Nat
  itemMeta : ItemMeta
  generics : LlbcGenericParams := {}
  methods : Array LlbcTraitMethod := #[]
  assocTypes : Array String := #[]
  assocConsts : Array (String × LlbcTy) := #[]
  impliedClauses : Array TraitClause := #[]
  /-- Dyn-compatible vtable struct ref. Opaque. -/
  vtable : Json := .null
  deriving Repr, Inhabited

/-- M9.7a: one method-impl pointer in a trait impl. `fnId` is the
    `FunDeclId` of the concrete body (also appears as a standalone
    entry in `LlbcProgram.funDecls`). -/
structure LlbcTraitImplMethod where
  name : String
  fnId : Nat
  deriving Repr, Inhabited

/-- M9.7a: a full structured trait impl. `selfTypeDeclId` is `some`
    when Self is a concrete ADT; otherwise the structured `selfType`
    is the source of truth. -/
structure LlbcTraitImpl where
  id : Nat
  itemMeta : ItemMeta
  traitDeclId : Nat
  /-- Full trait-ref instantiation (Self + generics applied). Opaque. -/
  implTrait : Json := .null
  selfTypeDeclId : Option Nat := none
  selfType : LlbcTy := .tOpaque ""
  generics : LlbcGenericParams := {}
  methods : Array LlbcTraitImplMethod := #[]
  /-- Associated-const impls: `(const-name, global-decl-id)`. -/
  assocConsts : Array (String × Nat) := #[]
  /-- Associated-type impls: `(type-name, concrete-type)`. -/
  assocTypes : Array (String × LlbcTy) := #[]
  /-- Parent-clause trait-refs (supertrait obligations resolved). -/
  impliedTraitRefs : Json := .null
  vtable : Json := .null
  deriving Repr, Inhabited

/-! ## Top-level program -/

/-- M9.7a: the top-level structured LLBC program embedded in a cert
    v3 file under `llbc_program`. `globalDecls` is kept opaque
    (Phase A doesn't introspect statics / consts); `charonVersion`
    and `extra` are forward-compat slots. -/
structure LlbcProgram where
  typeDecls : Array LlbcTypeDecl := #[]
  funDecls : Array LlbcFunDecl := #[]
  traitDecls : Array LlbcTraitDecl := #[]
  traitImpls : Array LlbcTraitImpl := #[]
  /-- Global / static decls. Opaque until a future milestone. -/
  globalDecls : Json := .null
  /-- Charon version that produced this program — for forward compat. -/
  charonVersion : String := ""
  /-- Catch-all for fields the parser doesn't recognize. -/
  extra : Json := .null
  deriving Repr, Inhabited

namespace LlbcProgram
/-- The empty program. Used as the default `CrateCert.llbcProgram`
    when a cert lacks the `llbc_program` field (back-compat with
    cert v2). -/
def empty : LlbcProgram := {}
end LlbcProgram

/-! ## Top-level cert (cert v3)

`CrateCert` was moved here from `Raw/CertEvent.lean` in M9.7c so it
can carry the structured `llbcProgram : LlbcProgram` field without
inducing an import cycle (LLBCProgram.lean already imports CertEvent
for `SourceSpan` / `TraitClause`).

The pre-M9.7 fields (`typeDecls`, `traitDecls`, `traitImpls`,
opaque-string signatures inside `functions[].signature`) are
preserved during Phases A–D so v2 fixtures stay valid mid-campaign;
Phase E retires the redundant flat fields once the translator reads
its structured input from `llbcProgram`. -/

/-- Top-level cert (M9.7c-extended). -/
structure CrateCert where
  fmtVersion : Nat
  crateHash : String
  /-- M9.5b: ADT type decls. May be empty for crates with no struct/
      enum types. The OCaml cert generator populates this from
      `crate.type_decls`; old certs that pre-date M9.5b have an empty
      array (the JSON parser tolerates a missing `type_decls` key). -/
  typeDecls : Array TypeDecl
  /-- M9.5l: trait declarations. Empty for crates with no traits;
      the parser tolerates a missing `trait_decls` key for
      back-compat with pre-M9.5l certs. -/
  traitDecls : Array TraitDecl := #[]
  /-- M9.5l: trait impls. Empty for crates with no impls; same
      back-compat treatment as `traitDecls`. -/
  traitImpls : Array TraitImpl := #[]
  functions : Array FunCert
  /-- M9.7c: the embedded structured LLBC program (cert v3). Empty
      under cert v1 / v2 — the JSON parser defaults to
      `LlbcProgram.empty` when the `llbc_program` field is absent.
      Phase C / D's consistency checks short-circuit when this is
      empty; Phase E flips the translator to read its structured
      input from here once Phase B populates the field. -/
  llbcProgram : LlbcProgram := LlbcProgram.empty
  deriving Repr, Inhabited

end AeneasCheck.Raw
