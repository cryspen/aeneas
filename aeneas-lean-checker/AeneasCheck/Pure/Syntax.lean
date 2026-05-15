import AeneasCheck.Raw.Types
import AeneasCheck.Raw.Literal
import AeneasCheck.Raw.CertEvent

/-!
Pure IR — the target language of the LLBC# → Pure translation.

Mirrors `src/pure/Pure.ml` (OCaml side), restricted to what the
direct-borrow subset needs:
* `let x = e1 in e2`
* variables (de-bruijn–free; we use fresh names)
* literals
* function application (binops, ctor application)
* `.ok e` / `.error e` for the Result monad

Generated Lean source references `Aeneas.Std.Result`, so the Pure IR
*does not* embed a Result-monad constructor; instead, the LeanEmit
backend wraps every function's body in `Result.ok` when emitting.
-/

namespace AeneasCheck.Pure

open AeneasCheck.Raw

/-- Pure types — direct-borrow subset only. -/
inductive PTy
  | unit
  | lit (k : LitTy)
  | adt (name : String) (args : Array PTy)
  | tuple (args : Array PTy)
  /-- The Aeneas Result monad result type (constructor wraps in
      `Result α`). -/
  | result (inner : PTy)
  /-- M12.2a-2: a (non-monadic) function type `α → β`. Used for the
      backward-function slot in the output of `&mut`-taking helpers:
      `Result (T_out × (T_borrow → (T_arg₁ × ... × T_argₙ)))`. -/
  | arrow (dom cod : PTy)
  /-- M9.5c: a fixed-length Rust array `[T; N]`. The standard Aeneas
      backend renders this as `Array <elem> <N>#usize`, where `<N>` is
      the const-generic length expressed as a `Std.Usize` literal. We
      keep the length as a `Nat` here (rather than wrapping it in
      `PExpr.lit`) because const generics flow through the type
      system, not the value layer; the pretty-printer is responsible
      for the `<N>#usize` rendering. -/
  | array (elem : PTy) (length : Nat)
  /-- M9.5g: a runtime-sized Rust slice `[T]` (always behind a borrow
      `&[T]` or `&mut [T]` at the value-level). The standard Aeneas
      backend renders this as `Slice <elem>` — no const-generic
      length, distinguishing it from the fixed-size `Array` case
      above. The borrow shape (shared vs mut) flows through the
      function signature only; at the pure-value layer a `&mut [T]`
      and a `[T]` post-state share the same `PTy.slice` shape. -/
  | slice (elem : PTy)
  /-- M9.5i: a type variable reference (e.g. `T` inside the body of
      a generic function or enum). The string is the parameter name
      verbatim from the surrounding `Decl.typeParams` /
      `EnumDecl.typeParams` / `StructDecl.typeParams` list — there is
      no separate de-Bruijn-style numbering at the Pure layer
      (resolution happens at translation time inside Forward.lean,
      which converts `RawTy.tyVar K` to `PTy.tyVar "T"` using the
      surrounding decl's typeParams list). The pretty-printer just
      emits the name. -/
  | tyVar (name : String)
  deriving Repr, Inhabited

/-- Pure expressions. -/
inductive PExpr
  | var (name : String)
  | lit (l : Lit)
  | app (head : String) (args : Array PExpr)
  /-- `let x : ty := e1; e2` -/
  | letIn (name : String) (ty : PTy) (e1 e2 : PExpr)
  /-- The `Result.ok` constructor — emitted only in tail position. -/
  | ok (inner : PExpr)
  /-- M11.2: an `if cond then thenE else elseE` expression. Both
      branches are full do-blocks (sequences of `letIn` chains ending
      in `ok`/`var`/`lit`). The standard Aeneas backend prints this
      as `if cond then <thenE> else <elseE>`. -/
  | ifThenElse (cond thenE elseE : PExpr)
  /-- M12.2a-2: a tuple expression `(e₁, e₂, ...)`. Used to assemble
      the forward-and-backward pair returned by `&mut`-taking
      helpers, and to destructure the call result on the caller side. -/
  | tuple (args : Array PExpr)
  /-- M12.2a-2: a non-monadic lambda `fun x₁ ... xₙ => body`. Used
      for backward closures emitted by `&mut`-taking helpers. -/
  | lam (params : Array (String × PTy)) (body : PExpr)
  /-- M12.2a-2: a non-monadic let `let x := e1; e2`. Used for the
      backward-closure binding inside the do-block (the standard
      Aeneas backend emits `let back := fun x1 => ...`). -/
  | letPure (name : String) (ty : PTy) (e1 e2 : PExpr)
  /-- M12.2a-2: a monadic let with a tuple pattern on the LHS:
      `let (x₁, ..., xₙ) ← e1; e2`. Used on the caller side of a
      `&mut`-returning call to destructure the forward/backward pair. -/
  | letPat (pat : Array String) (ty : PTy) (e1 e2 : PExpr)
  /-- M9.5b: a struct record-update expression `{ base with field := value }`.
      Used as the post-state value of a `&mut Pair` input after an
      EvAssign through `[Deref, Field K]`. The pretty-printer emits
      `{ <base> with <field> := <value> }`. Single-field updates only
      for now; chained-field updates (`{ p with fst := a, snd := b }`)
      can be modelled as nested `structUpdate`s. -/
  | structUpdate (base : PExpr) (field : String) (value : PExpr)
  /-- M9.5d / M9.5e: a `match scrutinee with | Ctor1 b₁ … bₙ => body1 | …`
      expression. M9.5d supported only nullary-constructor patterns
      (C-style enums); M9.5e extends each arm with an optional binder
      list so payload-bearing variants like `Num(u32)` can introduce
      `n` in the arm scope. Each arm is encoded as a triple
      `(ctor, binders, body)`; an empty `binders` array reproduces
      the M9.5d nullary shape. The pretty-printer renders binders
      space-separated after the ctor token, e.g. `| Foo.Num n => …`.
      The constructor name is rendered verbatim by the pretty-printer
      (the translator pre-qualifies it as `<EnumName>.<VariantName>`).
      We keep the arm encoding flat (`Array (String × Array String × PExpr)`)
      rather than introducing a mutually-recursive `MatchArm` type —
      Lean's `inductive ... mutual` block doesn't compose with the
      `deriving Repr, Inhabited` pattern the rest of the IR uses. -/
  | matchE (scrutinee : PExpr) (arms : Array (String × Array String × PExpr))
  /-- M9.5n: a struct field projection `<base>.<field>`. Emitted by
      the place walker when an `EvAssign` / `EvCopy` / `EvMove`
      source carries a trailing `[Field K]` projection on a place
      whose root local has a struct type registered in the
      `TypeDeclMap`. The standard Aeneas backend uses Lean's
      dot-notation `x.value` rather than a `match`-based projection
      lemma since `structure` decls auto-generate field accessors. -/
  | fieldAccess (base : PExpr) (field : String)
  deriving Repr, Inhabited

/-- Parameter declaration: `(name : ty)`. -/
structure Param where
  name : String
  ty : PTy
  deriving Repr, Inhabited

/-- M9.5o: a trait-bound binder slot, e.g. `(Trait1Inst : Trait1 T)`.
    Emitted between type-param binders and value params on functions
    + trait impls that carry trait obligations. `binderName` is the
    surface name (typically `<TraitName>Inst`); `traitName` is the
    bare trait name; `selfTypeName` is the name of the type
    parameter being constrained. The pretty-printer renders this as
    `({binderName} : {traitName} {selfTypeName})`. -/
structure TraitBoundParam where
  binderName : String
  traitName : String
  selfTypeName : String
  deriving Repr, Inhabited

/-- M9.5b: a struct field declaration (`name : ty`). -/
structure StructField where
  name : String
  ty : PTy
  deriving Repr, Inhabited

/-- M9.5b: a `structure Foo where …` declaration. `qualifiedName` is
    the original Rust `crate::path::Foo` form (used for the per-decl
    docstring); `name` is the bare name within its namespace. -/
structure StructDecl where
  name : String
  qualifiedName : String
  fields : Array StructField
  sourceSpan : Option Raw.SourceSpan := none
  /-- M9.5i: type-parameter names for a generic struct. Empty for a
      monomorphic struct (M9.5b's `Pair`-style fixtures). The pretty-
      printer renders these as `(T : Type)` parameters on the
      `structure` header. -/
  typeParams : Array String := #[]
  /-- M9.5l: true iff the struct uses tuple-style (positional) fields,
      OR is a unit struct (`struct Tag;` — zero-field tuple struct).
      For a zero-field tuple struct the pretty-printer emits
      `@[reducible] def <Name> := Unit` (no `structure` block);
      for N-field tuple structs it would emit field names like
      `field0`, `field1`, … (deferred — out of M9.5l scope for now
      since the fixture only exercises the unit case). Defaults to
      false (named-field struct, the M9.5b shape). -/
  isTupleStruct : Bool := false
  deriving Repr, Inhabited

/-- M9.5d / M9.5e: a single variant in an `EnumDecl`. M9.5d's C-style
    fixtures had `fields` empty; M9.5e populates it for payload-bearing
    variants (e.g. `Num(u32)` becomes `name := "Num"`, `fields :=
    #[{ name := "field0", ty := .lit (.int .u32) }]`). The pretty
    printer emits `| Num : Std.U32 → Enum` when fields is non-empty,
    and the bare `| Num : Enum` when it's empty. -/
structure EnumVariant where
  name : String
  fields : Array StructField := #[]
  deriving Repr, Inhabited

/-- M9.5d: an `inductive Foo where | A : Foo | B : Foo …` declaration.
    Mirrors `StructDecl` in shape. -/
structure EnumDecl where
  name : String
  qualifiedName : String
  variants : Array EnumVariant
  sourceSpan : Option Raw.SourceSpan := none
  /-- M9.5i: type-parameter names for a generic enum. Empty for a
      monomorphic enum (M9.5d/e's `Sign` / `NumOrZero` fixtures). The
      pretty-printer renders these as `(T : Type)` parameters on the
      `inductive` header and appends them to the trailing
      `: <Enum> T` of each variant's signature. -/
  typeParams : Array String := #[]
  deriving Repr, Inhabited

/-- A pure function declaration.

    `qualifiedName` is the original Rust `crate::path::fn` form,
    preserved for the per-function Aeneas-style docstring. `name` is
    the bare def name within its (possibly nested) namespace block —
    the Lean emitter strips the leading crate segment from
    `qualifiedName` to produce `name`.

    `sourceSpan` flows into the `Source: ...` docstring line; `none`
    suppresses that line.

    `note` is an optional translator-emitted disclaimer prepended to
    the `def` as a Lean block comment. M12.0 uses this to flag loop-
    containing functions whose body is a placeholder sentinel until
    M12.1 lands the real loop-translation rule. -/
structure Decl where
  name : String
  qualifiedName : String
  params : Array Param
  retTy : PTy
  body : PExpr
  sourceSpan : Option Raw.SourceSpan := none
  note : Option String := none
  /-- M12.1: Lean attribute names to attach to the `def`. Rendered as
      `@[a1, a2, ...]\n` immediately before `def`. The standard
      Aeneas backend uses this for `rust_loop` / `rust_loop_body` /
      `reducible` on the synthesised loop decls. -/
  attributes : Array String := #[]
  /-- M9.5i: type-parameter names for a generic function. Empty for
      monomorphic functions (every M9.5a-h fixture). The pretty-
      printer renders these as implicit `{T : Type}` binders BEFORE
      the value parameters, matching the standard Aeneas backend's
      shape (`def get {T : Type} (x : MyOption T) (default : T)
      : Result T := do …`). -/
  typeParams : Array String := #[]
  /-- M9.5o: trait-bound binders inserted between type-param binders
      and value-param binders. Empty when the function carries no
      trait obligations. Renders as `(Trait1Inst : Trait1 T)
      (Trait2Inst : Trait2 U)` after the `{T : Type} {U : Type}`
      type-param binders. -/
  traitBoundParams : Array TraitBoundParam := #[]
  /-- M9.5j: optional trailing keyword line emitted on its own line
      *after* the do-body, before the namespace's `end` marker. Used
      for `partial_fixpoint` on self-recursive functions, which the
      standard Aeneas backend appends so Lean's elaborator does not
      reject a definition that does not pass the structural-recursion
      check by shape alone. `none` for non-recursive functions. -/
  trailer : Option String := none
  deriving Repr, Inhabited

/-- M9.5l: one method declared in a trait. `name` is the bare method
    name (`value`). `ty` is the method's Lean-level type signature
    *as a function type from `Self` to the result*, e.g.
    `Self → Result Std.U32`. We keep the full type as a single `PTy`
    (`.arrow (.tyVar "Self") (.result …)` etc.) rather than splitting
    into `params + retTy` so the pretty-printer can render the method
    body uniformly. -/
structure TraitMethod where
  name : String
  ty : PTy
  deriving Repr, Inhabited

/-- M9.5l: a `structure <Name> (Self : Type) where …` declaration —
    the standard Aeneas backend's encoding of a Rust trait. M9.5l only
    handles single-method, no-associated-types, no-default-methods
    traits. The pretty-printer renders each method as one
    `<name> : <ty>` line under the structure header. -/
structure TraitDecl where
  name : String
  qualifiedName : String
  methods : Array TraitMethod
  sourceSpan : Option Raw.SourceSpan := none
  deriving Repr, Inhabited

/-- M9.5l: one method's body binding inside a trait impl. `name` is
    the trait method's bare name (matches an entry in the trait's
    `methods` array). `body` is the qualified Lean name of the body
    function (e.g. `Tag.Insts.Traits_basicNumeric.value`) — pre-
    computed by the OCaml cert side and threaded through the
    translator. The instance literal renders as
    `{ <name> := <body> }`. -/
structure TraitImplMethod where
  name : String
  body : String
  deriving Repr, Inhabited

/-- M9.5l: an `@[reducible] def <Name> : <TraitName> <SelfTy> := { … }`
    declaration — the standard Aeneas backend's encoding of a Rust
    trait impl. `name` is the standard-backend's full Lean name
    (e.g. `Tag.Insts.Traits_basicNumeric`); `traitName` is the bare
    trait name (`Numeric`); `selfTy` is the Self ADT (e.g. `.adt "Tag" #[]`).
    M9.5l only handles single-method, concrete-Self impls. -/
structure TraitImpl where
  name : String
  qualifiedName : String
  traitName : String
  selfTy : PTy
  methods : Array TraitImplMethod
  sourceSpan : Option Raw.SourceSpan := none
  /-- M9.5o: type-parameter names on the impl (`{T : Type}`).
      Empty for concrete-Self impls. -/
  typeParams : Array String := #[]
  /-- M9.5o: trait-bound binders on the impl
      (`(Trait1Inst : Trait1 T)`). Empty for impls without
      where-clauses. The pretty-printer renders these between the
      `def <name>` and `: <traitName> <selfTy>`. -/
  traitBoundParams : Array TraitBoundParam := #[]
  deriving Repr, Inhabited

/-- M9.5b: a crate-level emit unit. The translator now interleaves
    struct / enum decls and function decls so the emitter can render
    them in cert order (with type decls forced to come before any
    function that uses them, in [LeanEmit]'s ordering pass).

    M9.5d added `enum`. M9.5l added `traitDecl` + `traitImpl` so trait
    + impl blocks can be emitted alongside structs / enums in the
    crate namespace. -/
inductive TopDecl
  | struct (sd : StructDecl)
  | enum (ed : EnumDecl)
  | function (d : Decl)
  | traitDecl (td : TraitDecl)
  | traitImpl (ti : TraitImpl)
  deriving Repr, Inhabited

/-- M9.5b: derive the `crate::…` qualified name of a top decl, for
    namespace grouping in [LeanEmit]. -/
def TopDecl.qualifiedName : TopDecl → String
  | .struct sd => sd.qualifiedName
  | .enum ed => ed.qualifiedName
  | .function d => d.qualifiedName
  | .traitDecl td => td.qualifiedName
  | .traitImpl ti => ti.qualifiedName

end AeneasCheck.Pure
