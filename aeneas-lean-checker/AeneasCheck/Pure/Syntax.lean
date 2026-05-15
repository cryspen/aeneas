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
  deriving Repr, Inhabited

/-- Parameter declaration: `(name : ty)`. -/
structure Param where
  name : String
  ty : PTy
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
  deriving Repr, Inhabited

/-- M9.5b: a crate-level emit unit. The translator now interleaves
    struct / enum decls and function decls so the emitter can render
    them in cert order (with type decls forced to come before any
    function that uses them, in [LeanEmit]'s ordering pass).

    M9.5d added `enum`. -/
inductive TopDecl
  | struct (sd : StructDecl)
  | enum (ed : EnumDecl)
  | function (d : Decl)
  deriving Repr, Inhabited

/-- M9.5b: derive the `crate::…` qualified name of a top decl, for
    namespace grouping in [LeanEmit]. -/
def TopDecl.qualifiedName : TopDecl → String
  | .struct sd => sd.qualifiedName
  | .enum ed => ed.qualifiedName
  | .function d => d.qualifiedName

end AeneasCheck.Pure
