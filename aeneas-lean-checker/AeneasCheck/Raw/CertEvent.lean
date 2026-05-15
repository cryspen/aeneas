import AeneasCheck.Raw.Places
import AeneasCheck.Raw.Literal

/-!
Raw certificate events — Lean mirror of `src/cert/CertEvent.ml`.

Direct-borrow subset (M2-M8): mutBorrow, sharedBorrow, assign, move,
copy, endBorrow, assert, panic, return. The rest are stubs that parse
but the replayer rejects in milestone-specific ways.
-/

namespace AeneasCheck.Raw

/-- A symbolic value reference or constant in a cert event RHS. -/
inductive SymExpr
  | symVal (id : Nat)
  | symLit (l : Lit)
  | symCopy (p : Place)
  | symMove (p : Place)
  | symMutBorrowTok (borrowId : Nat)
  /-- M9.5d / M9.5f: an enum variant construction. `adtId` keys into the
      crate's `typeDecls` table; `variantName` is the bare constructor
      name. Used as the RHS of an `EvAssign` whose Charon source was
      a variant `AggregatedAdt`.

      M9.5d covered only the nullary case (empty [fields]); M9.5f
      extends this with one [SymExpr] per payload field. The Lean
      emitter renders nullary variants as `<adtName>.<variantName>`
      and payload-bearing ones as
      `<adtName>.<variantName> <e1> ... <eN>` (with the qualification
      resolved via the type-decl map). -/
  | symVariant (adtId variantId : Nat) (variantName : String)
               (fields : Array SymExpr)
  deriving Repr

/-- Restoration info for an EvEndBorrow event. -/
structure RestoreInfo where
  givenBack : SymExpr
  deriving Repr

/-- A coarse summary of state at a point in evaluation. -/
structure StateSummary where
  env : Array (Nat × SymExpr)
  liveLoans : Array Nat
  deriving Repr, Inhabited

/-- LLBC# trace events. Constructor names match `CertEvent.event`
    (without the `Ev` prefix). -/
inductive Event
  -- direct-borrow subset
  | mutBorrow (loan : Nat) (place : Place) (symval : Nat)
  | sharedBorrow (loan : Nat) (sharedBorrowId : Nat) (place : Place) (symval : Nat)
  | assign (dst : Place) (rhs : SymExpr)
  | move (src dst : Place)
  | copy (src dst : Place)
  | endBorrow (loan : Nat) (restore : RestoreInfo)
  | assert (cond : SymExpr) (expected : Bool)
  | panic
  | retn
  /-- M10.0: a Charon `Rvalue.BinaryOp` reduction. `op` is the flat
      string tag emitted by OCaml's `cert_binop_string` (arithmetic
      ops bake the overflow mode in: `AddPanic` / `AddWrap` /
      `AddUB`, etc.). -/
  | binop (op : String) (lhs rhs : SymExpr) (dst : Place)
  -- later milestones
  | reborrow (child parent : Nat) (place : Place)
  /-- M10.1: a function call. `fnName` is the qualified callee name
      (e.g. `core::num::{u32}::wrapping_add`); the translator
      consumes it directly so we don't need a builtin-id lookup
      table. `regionAbs` is the abstraction-id list that M10.2's
      End-Abstraction rule consumes. -/
  | call (fn callId : Nat) (fnName : String) (args : Array SymExpr)
      (dst : Place) (regionAbs : Array Nat)
  | endAbs (abs : Nat) (finalValues : Array SymExpr)
  | proj (abs : Nat) (place : Place) (symval : Nat)
  | join (left right result : StateSummary)
  | loopInv (loopId : Nat) (invariant : StateSummary)
  /-- M12.1: end-of-loop-body marker. Paired with the preceding
      `loopInv` carrying the same `loopId`; the events between the
      pair form the canonical loop body that the Lean translator
      lifts into a `<fn>_loop.body` decl. -/
  | loopEnd (loopId : Nat)
  /-- M9.5d: per-arm marker for a `match` on a symbolic ADT
      scrutinee. The `scrutinee` is the cert sym-expr for the
      matched value (typically `SymVal` of the symbolic id that
      was expanded). `variantId` / `variantName` identify which
      arm follows. The arm's body events run until the next
      `matchArm` for the same scrutinee, the closing `EvJoin`, or
      an `EvReturn` at depth 0. -/
  | matchArm (scrutinee : SymExpr) (adtId variantId : Nat) (variantName : String)
  deriving Repr, Inhabited

/-- A source span attached to a cert function. Used by the Lean
    emitter to build the per-function `Source: ...` docstring. -/
structure SourceSpan where
  file : String
  begLine : Nat
  begCol : Nat
  endLine : Nat
  endCol : Nat
  deriving Repr, Inhabited

/-- Lean-side view of the Rust signature: input + output types as
    pretty-printed LLBC type strings (kept opaque until M9 carries
    proper Charon types in the cert). -/
structure FnSignature where
  inputs : Array RawTy
  output : RawTy
  /-- M9.5i: the function's type-parameter names, in declaration
      order. Empty for monomorphic functions. The Forward translator
      renders these as implicit `{T : Type}` binders before the value
      parameters, and uses the index of each name as the de-Bruijn
      identifier that resolves `TVar (Free K)` references inside
      `inputs` / `output`. -/
  typeParams : Array String := #[]
  deriving Repr, Inhabited

/-- Per-function cert trace. -/
structure FunCert where
  fnId : Nat
  fnName : String
  signature : FnSignature
  /-- `none` when the OCaml side could not attach a span (synthetic
      items, builtins). -/
  sourceSpan : Option SourceSpan
  events : Array Event
  finalState : StateSummary
  /-- M9.5l: optional Lean-shaped name pre-computed by the OCaml
      cert generator. Set for trait-impl method bodies (e.g.
      `Tag.Insts.Traits_basicNumeric.value`); `none` for regular
      functions, in which case the emitter falls back to sanitizing
      `fnName`. The translator threads this through the `EvCall`
      callee lookup so caller sites see the same pretty name. -/
  prettyName : Option String := none
  deriving Repr, Inhabited

/-- M9.5b: a single field inside a [TypeDecl]. `name` is `none` for
    tuple-style positional fields; the emitter falls back to
    `field<idx>` in that case. `ty` is the cert's opaque-tagged LLBC
    type string. -/
structure CertField where
  idx : Nat
  name : Option String
  ty : RawTy
  deriving Repr, Inhabited

/-- M9.5d: a single variant of an enum ADT declaration. `fields` is
    empty for C-style enums (no payload); future milestones will
    populate it for payload-bearing variants. -/
structure CertVariant where
  id : Nat
  name : String
  fields : Array CertField
  deriving Repr, Inhabited

/-- M9.5b: kind of an ADT declaration. M9.5b supports struct; M9.5d
    adds enum. Other shapes (union, alias) come through as `opaque`. -/
inductive TypeDeclKind
  | struct (fields : Array CertField)
  | enum (variants : Array CertVariant)
  | opaque
  deriving Repr, Inhabited

/-- M9.5b: a crate-level ADT declaration. `id` is the LLBC
    `TypeDeclId.id` that appears inside `TAdt {id = TAdtId N; ...}` in
    cert-event place types; the Lean checker uses `id`→`name` lookups
    to translate borrowed-struct signatures and field projections. -/
structure TypeDecl where
  id : Nat
  name : String
  kind : TypeDeclKind
  /-- M9.5i: the ADT's type-parameter names, in declaration order.
      Empty for monomorphic ADTs (Pair, Sign, NumOrZero, …). The
      Lean translator renders these as `(T : Type)` parameters on
      the emitted `inductive` / `structure` header and uses each
      name's position as the de-Bruijn-style index that resolves
      `TVar (Free K)` references inside the decl's variant /
      field types. -/
  typeParams : Array String := #[]
  /-- M9.5l: tuple-style positional fields (or a unit struct's empty
      field list). When set on a struct kind, the Lean emitter
      renders the decl as `@[reducible] def <Name> := Unit` (zero
      fields) or as a `structure` with positional `fieldK` names
      (tuple struct with N fields). Defaults to false on the Lean
      side when the cert key is absent (pre-M9.5l certs). -/
  isTupleStruct : Bool := false
  /-- M9.5l: source span for the type decl's source-code definition.
      Optional for back-compat (pre-M9.5l certs have no span). -/
  sourceSpan : Option SourceSpan := none
  deriving Repr, Inhabited

/-- M9.5l: one method declared in a trait. Mirrors `cert_trait_method`
    on the OCaml side; the signature uses the same opaque-tagged
    shape as `FnSignature` so the existing `RawTy` parser recovers
    parameter / return types. -/
structure TraitMethodDecl where
  name : String
  signature : FnSignature
  deriving Repr, Inhabited

/-- M9.5l: a crate-level trait declaration. M9.5l only handles the
    minimal shape: no associated types, no associated consts, no
    parent traits, no const generics, no default methods, no extra
    generics beyond the implicit `Self`. -/
structure TraitDecl where
  id : Nat
  name : String
  /-- Crate-prefixed qualified name (`traits_basic::Numeric`) used in
      the Lean per-decl docstring. -/
  qualifiedName : String
  methods : Array TraitMethodDecl
  sourceSpan : Option SourceSpan := none
  deriving Repr, Inhabited

/-- M9.5l: one method implemented in a trait impl. `fnId` is the
    `FunDeclId` of the concrete body (which also appears as a
    standalone entry in `CrateCert.functions`). `name` is the trait
    method's bare name (as it appears in the trait declaration),
    not the impl method's qualified name. -/
structure TraitImplMethod where
  name : String
  fnId : Nat
  deriving Repr, Inhabited

/-- M9.5l: a crate-level trait impl. `prettyName` is the
    standard-Aeneas Lean impl name pre-computed by the OCaml side
    (e.g. `Tag.Insts.Traits_basicNumeric`). `selfTypeDeclId` is the
    Self-ADT's `TypeDeclId`, or `none` when Self is not a
    user-declared ADT (out of M9.5l scope). -/
structure TraitImpl where
  id : Nat
  prettyName : String
  /-- Crate-prefixed qualified name
      (`traits_basic::{traits_basic::Numeric for traits_basic::Tag}`)
      used in the Lean per-decl docstring. -/
  qualifiedName : String
  traitDeclId : Nat
  selfTypeDeclId : Option Nat
  methods : Array TraitImplMethod
  sourceSpan : Option SourceSpan := none
  deriving Repr, Inhabited

/-- Top-level cert. -/
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
  deriving Repr, Inhabited

end AeneasCheck.Raw
