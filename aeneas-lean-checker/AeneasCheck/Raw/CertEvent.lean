import AeneasCheck.Raw.Places
import AeneasCheck.Raw.Literal

/-!
Raw certificate events — Lean mirror of `src/cert/CertEvent.ml`.

Direct-borrow subset (M2-M8): mutBorrow, sharedBorrow, assign, move,
copy, endBorrow, assert, panic, return. The rest are stubs that parse
but the replayer rejects in milestone-specific ways.

M9.6 (Option C): rule-choice hints are layered onto existing event
constructors as optional fields with back-compat defaults — see the
`MutBorrowKind` / `JoinRule` / `AbsRoleEntry` / `AbsShape` block
below and the per-constructor `M9.6` docstrings.
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
  /-- M9.5p: a tuple aggregate construction, e.g. `(x, y)` on the RHS
      of an `EvAssign`. The Lean translator renders this as
      `(e1, e2, …, eN)`. -/
  | symTuple (fields : Array SymExpr)
  /-- M9.5p: a named-field struct aggregate construction, e.g.
      `Pair { x, y }`. Each entry carries the field's surface name as
      resolved by the OCaml cert generator (using the type-decl's
      `field_name`; tuple-style structs fall back to `fieldK`). The
      Lean translator renders this as `{ x := e1, y := e2 }`. -/
  | symRecord (adtId : Nat) (fields : Array (String × SymExpr))
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

/-! ## Option C (M9.6) hint schema

These types are the Lean mirror of the JSON hints introduced in
`cert_fmt_version = 2`. They are carried as optional fields on the
existing `Event` constructors (with defaults that preserve the
pragmatic behaviour of v1 certs). The Lean checker's "strict path"
(landed across plan §7.1 commits #13-#23) consumes them; the JSON
parser fills the defaults for any v1 cert or any v2 cert that omits
the field. See `documentation/option-c-implementation-plan.md` §1 for
the per-field specification and `documentation/cert-format-and-soundness.md`
§3.2 for the pragmatic shortcuts each hint eliminates. -/

/-- M9.6: classification of an `EvMutBorrow`. Subsumes the
    pragmatic M9.5w (Deref-projection ⇒ reborrow-class) and M9.5aa
    (in-loop ⇒ lazyExpand) shortcuts:

    * `direct` — in-body `&mut p` with no Deref in its projection
      and no enclosing loop; must be explicitly ended before
      function exit.
    * `inAbsReborrow absId` — a `&mut (*x).f`-shaped borrow whose
      lifetime is owned by the named region abstraction (typically
      a caller-input abstraction); allowed to leak past exit.
    * `loopOwned loopId` — a direct `&mut local` issued inside an
      open loop body; the loop's region abstraction owns its
      lifetime. -/
inductive MutBorrowKind
  | direct
  | inAbsReborrow (absId : Nat)
  | loopOwned (loopId : Nat)
  deriving Repr, Inhabited

/-- M9.6: per-local witness of which Fig. 11 (paper) rule the OCaml
    interpreter applied to derive a `EvJoin` result entry. Carried
    inside `JoinEntry`; one entry per result-env local in declaration
    order. -/
inductive JoinRule
  /-- Both branches agreed on this local's value. -/
  | joinSame
  /-- Branches differed on a value containing no borrows/loans; the
      OCaml side introduced a fresh symbolic value `freshSv` and the
      result is `SymVal freshSv`. -/
  | joinSymbolic (freshSv : Nat)
  /-- Both branches held a `&mut` with different loan ids; the join
      introduced a fresh borrow id `l_fresh` inside a fresh region
      abstraction `abs` (Collapse-Dup-MutBorrow). -/
  | joinMutBorrows (l_left l_right l_fresh : Nat) (abs : Nat)
  /-- `Join-Var` rule (paper Fig. 11): a whole region abstraction is
      folded into the result. (Marker only in this milestone; the
      surrounding `EvEndAbs` carries the absorbed abstraction's
      contents.) -/
  | joinVar
  /-- Left side is `⊥`; right side is wrapped into the abstraction
      `abs`. -/
  | joinBottomOther (abs : Nat)
  /-- Mirror of `joinBottomOther`. -/
  | joinOtherBottom (abs : Nat)
  deriving Repr, Inhabited

/-- M9.6: one entry of `EvJoin.witnesses`. -/
structure JoinEntry where
  localId : Nat
  rule : JoinRule
  deriving Repr, Inhabited

/-- M9.6: per-`avalue` role of a `tavalue` inside a function-call's
    input region abstraction (paper §4.1 `A_in(ρ)` content). Carried
    inside `AbsShape.roles`. -/
inductive AbsRoleEntry
  /-- The abstraction holds a mutable input borrow whose loan id is
      `loanId`; `argIdx` is the call-site argument position the
      borrow originated from. -/
  | mutBorrow (argIdx : Nat) (loanId : Nat)
  /-- The abstraction owns the loan side of `loanId` — i.e. when the
      abstraction ends, the loan is released and any held
      `mutLoan loanId` token is cleared. -/
  | mutLoan (loanId : Nat)
  /-- A shared borrow owned by the abstraction. -/
  | sharedBorrow (argIdx : Nat) (sharedBorrowId : Nat)
  deriving Repr, Inhabited

/-- M9.6: the shape of one region abstraction freshened by `EvCall`.
    Mirrors the paper's `A_in(ρ) { borrow^m ℓ _, loan^m ℓ' }` shape:
    an abstraction id, its ancestor ids (for nested-borrow contracts),
    and one `AbsRoleEntry` per `tavalue` held. -/
structure AbsShape where
  absId : Nat
  parentAbs : Array Nat
  roles : Array AbsRoleEntry
  deriving Repr, Inhabited

/-- LLBC# trace events. Constructor names match `CertEvent.event`
    (without the `Ev` prefix). -/
inductive Event
  -- direct-borrow subset
  /-- M9.6 `kindHint` (Option C) subsumes M9.5w + M9.5aa: the OCaml
      side declares whether this `&mut` is direct, reborrow-class
      (held inside a named region abstraction), or loop-owned.
      Defaults to `.direct` for back-compat with pre-M9.6 certs;
      the M9.5w/aa pragmatic inference in `Step.lean` is the
      fallback while the hint is absent. -/
  | mutBorrow (loan : Nat) (place : Place) (symval : Nat)
              (kindHint : MutBorrowKind := .direct)
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
  /-- M9.6 `parentLive` / `parentAbs` (Option C): the OCaml side
      asserts whether the parent borrow is still live in the
      caller-state (`parentLive = true` requires
      `st.loans.contains parent`) and which abstraction owns it.
      Defaults to `false` / `none` for back-compat — the
      `stepReborrow` pragmatic "pre-add a fake `.reborrow` parent
      if missing" branch is the fallback while the hints are
      absent. -/
  | reborrow (child parent : Nat) (place : Place)
             (parentLive : Bool := false)
             (parentAbs : Option Nat := none)
  /-- M10.1: a function call. `fnName` is the qualified callee name
      (e.g. `core::num::{u32}::wrapping_add`); the translator
      consumes it directly so we don't need a builtin-id lookup
      table. `regionAbs` is the abstraction-id list that M10.2's
      End-Abstraction rule consumes.

      M9.6 `absSig` (Option C): one `AbsShape` per region
      abstraction freshened by this call (one-to-one with
      `regionAbs`). Encodes the paper's `A_in(ρ)` content (per-arg
      mut/shared borrows the call owns + the loan ids whose
      lifetime flows into the abstraction). Defaults to empty for
      back-compat — while absent, abstraction ids stay opaque
      tokens and `EvEndAbs.releasedLoans` alone drives release. -/
  | call (fn callId : Nat) (fnName : String) (args : Array SymExpr)
      (dst : Place) (regionAbs : Array Nat)
      (absSig : Array AbsShape := #[])
  /-- M10.2 / M9.5s: a region abstraction just closed. `finalValues`
      carries one symbolic-value reference per [AEndedMutBorrow] the
      abstraction held, in left-to-right order — the Forward
      translator pairs each entry with the most recent EvCall's
      [region_abs] field to bind post-state names. `releasedLoans`
      (M9.5s) lists the loan ids whose lifetime the abstraction owned
      and which the OCaml interpreter implicitly ended when destroying
      the abstraction (paper.rs `call_choose` pattern: input borrows
      that flowed into the call's abstraction and were never
      explicitly ended via [EvEndBorrow]). The Lean replayer drops
      each released loan from [SymState.loans] and the typechecker
      moves it from [liveLoans] to [endedLoans], so the
      "function ended with live borrow(s)" post-condition passes for
      these implicitly-ended loans. Defaults to empty for back-compat
      with pre-M9.5s certs.

      M9.6 `tokenClearLocals` (Option C) strengthens
      `releasedLoans`: explicitly lists the locals whose `mutLoan`
      token must be cleared when this abstraction ends. Defaults
      to empty — while absent, `stepEndAbs` falls back to the
      scan-env behaviour. -/
  | endAbs (abs : Nat) (finalValues : Array SymExpr)
           (releasedLoans : Array Nat := #[])
           (tokenClearLocals : Array Nat := #[])
  | proj (abs : Nat) (place : Place) (symval : Nat)
  /-- M9.5r: lazy mut-borrow expansion. The OCaml interpreter just
      replaced symbolic value `svId` (some [&mut T]-typed value) with
      a concrete mut-borrow whose id is `bid` and whose inner value is
      a fresh symbolic value `innerSv`. The Lean replayer scans every
      local / loan-given holding `.sym svId`, replaces with `.mutLoan
      bid`, and registers loan `bid` with `given := .sym innerSv` —
      so a subsequent in-body `EvEndBorrow loan=bid` (paper.rs
      `test_choose` pattern) can resolve.

      M9.6 `parentAbs` / `substLocals` / `substLoans` (Option C)
      eliminate the M9.5r env-scan: `parentAbs` names the
      abstraction that owns the now-expanded borrow, `substLocals`
      lists every env local whose value was `.sym svId` (and is
      now `.mutLoan bid`), and `substLoans` lists every loan-given
      slot that was likewise rewritten. All default to empty/none
      for back-compat. -/
  | symExpandMutBorrow (svId bid innerSv : Nat)
                       (parentAbs : Option Nat := none)
                       (substLocals : Array Nat := #[])
                       (substLoans : Array Nat := #[])
  /-- M9.6 `witnesses` (Option C): per-result-env-local rule
      witness from the join algebra (paper Fig. 11). When
      non-empty, drives the strict per-entry check; when empty,
      `stepJoin` falls back to the pragmatic
      `symExprBeq` + `isFreshSym` shortcut (M9.5y). -/
  | join (left right result : StateSummary)
         (witnesses : Array JoinEntry := #[])
  /-- M9.6 `loanRegistry` (Option C): explicit
      `(borrowId, parentAbsId)` registry from the OCaml side's
      `compute_loop_entry_fixed_point` output. When non-empty,
      `Replay.stepEvent` for `loopInv` consumes it directly
      (M9.5z scan-env fallback retained while empty). -/
  | loopInv (loopId : Nat) (invariant : StateSummary)
            (loanRegistry : Array (Nat × Nat) := #[])
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

/-- M9.5o: one trait obligation on a generic parameter, e.g.
    `T: Trait1` lowers to `{ traitQualifiedName := "crate::Trait1",
    typeParamIdx := 0 }`. The qualified name is what the cert
    carries (rendered against the `traitDecls` table later to derive
    the bare trait name). -/
structure TraitClause where
  traitQualifiedName : String
  typeParamIdx : Nat
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
  /-- M9.5o: per-clause trait obligations on the function's type
      parameters. Each entry binds a `TraitX` bound to the K-th
      `typeParams` entry. Empty for signatures without trait
      obligations. Optional in the JSON cert for back-compat. -/
  traitClauses : Array TraitClause := #[]
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
  /-- M9.5n: crate-prefixed qualified name (e.g.
      `core::option::Option`, `alloc::alloc::Global`,
      `issue_194_recursive_struct_projector::AVLNode`). Used by the
      Driver's stdlib-suppression list to skip re-emitting ADTs that
      already have a Lean equivalent — without this, the emitted
      `inductive Option (T : Type) where …` would shadow Lean's
      built-in `Option` and break the file's `open Aeneas Aeneas.Std`
      scope. Defaults to empty for back-compat with pre-M9.5n
      certs (which only carry the bare `name`). -/
  qualifiedName : String := ""
  deriving Repr, Inhabited

/-- M9.5l: one method declared in a trait. Mirrors `cert_trait_method`
    on the OCaml side; the signature uses the same opaque-tagged
    shape as `FnSignature` so the existing `RawTy` parser recovers
    parameter / return types. -/
structure TraitMethodDecl where
  name : String
  signature : FnSignature
  /-- M9.5o: true iff this method carries a default implementation
      in the trait declaration. The Lean translator emits these
      with a `Trait.<method>.default` shape (the default takes the
      trait itself as a bound). Defaults to false on the parsing
      side for back-compat. -/
  hasDefault : Bool := false
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
  /-- M9.5o: for a blanket impl (Self is a type variable), this carries
      the variable's name (e.g. `"T"`). `none` when Self is a concrete
      ADT (the `selfTypeDeclId` case). -/
  selfTypeVar : Option String := none
  /-- M9.5o: type-parameter names declared on the impl itself. Empty
      for monomorphic impls. -/
  typeParams : Array String := #[]
  /-- M9.5o: trait obligations on the impl's type parameters. -/
  traitClauses : Array TraitClause := #[]
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
