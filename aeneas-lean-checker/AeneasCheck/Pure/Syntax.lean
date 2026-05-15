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
  deriving Repr, Inhabited

/-- Parameter declaration: `(name : ty)`. -/
structure Param where
  name : String
  ty : PTy
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
  deriving Repr, Inhabited

end AeneasCheck.Pure
