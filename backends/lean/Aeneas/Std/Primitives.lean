module
public import Lean
public meta import Aeneas.Std.Global
public import Aeneas.Extract
public import AeneasMeta.BvEnumToBitVec
public import Aeneas.Data.Coinductive.ITree
public import Aeneas.Data.Coinductive.Effect
public section

namespace Aeneas

namespace Std

/-!
# Assert Command
-/

open Lean Elab Command Term Meta
open Aeneas.Data.Coinductive

syntax (name := elabSyntax) "#elab" term: command

@[command_elab elabSyntax]
meta unsafe
def elabImpl : CommandElab := fun (stx: Syntax) => do
  runTermElabM (fun _ => do
    /- Simply elaborate the syntax to check that it is correct -/
    let (_, _) ← Elab.Term.elabTerm stx[1] none |>.run
    pure ())

#elab 3

/-!
# Results and Monadic Combinators
-/

@[expose] section

inductive Error where
   | panic: Error
   | undef: Error
deriving Repr, BEq

open Error

inductive RustEffect.Input : Type where
| fail : Error → RustEffect.Input

def RustEffect.Output (i : RustEffect.Input) : Type :=
  match i with
  | .fail _ => PEmpty

def RustEffect : Effect := {
  I := RustEffect.Input
  O := RustEffect.Output
}

-- We need RustM to be irreducble outside this file (to not break metaprograms which normalize types),
-- but reducible within. The `unseal` command only affects the local scope.
@[irreducible]
def RustM (α : Type u) : Type u := ITree RustEffect α
unseal RustM

def RustM.ok {α} (a : α) : RustM α := .ret a

def RustM.vis {α} (eff : RustEffect.Input) (k : RustEffect.Output eff → RustM α) : RustM α := ITree.vis eff k

/- `RustM.fail` is deliberately kept opaque: we do *not* mark it with `simp`/`grind` so that it
   never gets unfolded to a `RustM.vis`. All the reasoning about `fail` should go through the
   dedicated lemmas below (`bind_fail`, `spec_fail`, ...). -/
def RustM.fail {α} (e : Error) : RustM α := RustM.vis (.fail e) PEmpty.elim

theorem RustM.fail_eq_vis {α} (e : Error) :
  (RustM.fail e : RustM α) = RustM.vis (.fail e) PEmpty.elim := rfl

def RustM.div {α} : RustM α := ITree.div

def bind {α : Type u} {β : Type v} (x: RustM α) (f: α → RustM β) : RustM β :=
  ITree.bind x f

instance : Monad RustM where
  pure := .ok
  bind := bind

@[elab_as_elim, cases_eliminator]
def RustM.cases {R}
    {motive : RustM R → Sort v}
    (t : RustM R)
    (ret : ∀ r, motive (RustM.ok r))
    (vis : ∀ i k, motive (RustM.vis i k))
    (div :  motive (RustM.div))
    : motive t := ITree.cases ret div vis t

inductive MatchResult (α : Type u) : Type u where
| ok : (a : α) → MatchResult α
| div : MatchResult α
| vis : (eff : RustEffect.Input) → (RustEffect.Output eff → RustM α) → MatchResult α

/-!
Can simulate a match on the Result type by matching on the output of this function.
-/
def RustM.match.{u} {α : Type u} (r : RustM α) : MatchResult α :=
  r.cases .ok .vis .div

@[simp, grind =]
theorem RustM.match.ok {α : Type u} {a : α} : (RustM.ok a).match = .ok a := by
  simp [RustM.match, RustM.ok, RustM.cases]
@[simp, grind =]
theorem RustM.match.vis {α : Type u} {e k} : (@RustM.vis α e k).match = .vis e k := by
  simp [RustM.match, RustM.vis, RustM.cases]
@[simp, grind =]
theorem RustM.match.div {α : Type u} : RustM.div.match = @MatchResult.div α := by
  simp [RustM.match, RustM.div, RustM.cases]
@[simp, grind =]
theorem RustM.match.fail {α : Type u} {e} :
  (RustM.fail e : RustM α).match = .vis (.fail e) PEmpty.elim := by
  simp [RustM.fail_eq_vis]

/-- The `Repr` instance for `RustM`, so that `#eval` on `RustM`-producing expressions prints `Aeneas.Std.RustM.ok`/`fail`/`div`. -/
instance RustM.reprInst {α : Type u} [Repr α] : Repr (RustM α) where
  reprPrec r _ :=
    match RustM.match r with
    | .ok a => "Aeneas.Std.RustM.ok " ++ repr a
    | .div => "Aeneas.Std.RustM.div"
    | .vis (.fail e) _ => "Aeneas.Std.RustM.fail " ++ repr e

/-!
`RustM` not being an inductive type it has no built-in constructor facts that grind
can leverage. As we do not want to abuse e-matching, because it risks saturating
the context, we mark lemmas like `ok_not_vis` only as `simp`. This is not a problem
as only few proofs rely on this fact, and they should all be limited to the Aeneas
library (put aside rare cases, client code should not need these facts).

Injectivity is different: `@[grind inj]` is a specialized mechanism (it registers a left inverse
rather than an E-matching pattern), and it is stated purely in terms of the constructors, so it
does not reveal how `RustM` is represented.
-/

@[grind inj]
theorem RustM.ok_injective {α} : Function.Injective (@RustM.ok α) := by
  intro a b h; simpa using congrArg RustM.match h

/-- `RustM.fail` is opaque, so its injectivity has to be stated separately. -/
@[grind inj]
theorem RustM.fail_injective {α} : Function.Injective (@RustM.fail α) := by
  intro a b h; simpa using congrArg RustM.match h

/-! The disequality lemmas for the constructors of `RustM`. They all follow from the fact that
`RustM.match` maps the constructors to *distinct* constructors of the inductive `MatchResult`. -/

@[simp]
theorem ok_not_vis {α} {a : α} {eff k} : ¬ RustM.ok a = .vis eff k := by
  intro h; simpa using congrArg RustM.match h
@[simp]
theorem vis_not_ok {α} {a : α} {eff k} : ¬ .vis eff k = RustM.ok a := by
  intro h; simpa using congrArg RustM.match h
@[simp]
theorem ok_not_div {α} {a : α} : ¬ RustM.ok a = .div := by
  intro h; simpa using congrArg RustM.match h
@[simp]
theorem div_not_ok {α} {a : α} : ¬ RustM.div = .ok a := by
  intro h; simpa using congrArg RustM.match h
@[simp]
theorem vis_not_div {α} {eff k} : ¬ @RustM.vis α eff k = .div := by
  intro h; simpa using congrArg RustM.match h
@[simp]
theorem div_not_vis {α} {eff k} : ¬ .div = @RustM.vis α eff k := by
  intro h; simpa using congrArg RustM.match h
@[simp]
theorem ok_not_fail {α} {a : α} {e} : ¬ RustM.ok a = .fail e := by
  intro h; simpa using congrArg RustM.match h
@[simp]
theorem fail_not_ok {α} {a : α} {e} : ¬ RustM.fail e = .ok a := by
  intro h; simpa using congrArg RustM.match h
@[simp]
theorem fail_not_div {α} {e} : ¬ (RustM.fail e : RustM α) = .div := by
  intro h; simpa using congrArg RustM.match h
@[simp]
theorem div_not_fail {α} {e} : ¬ (RustM.div : RustM α) = .fail e := by
  intro h; simpa using congrArg RustM.match h

@[simp]
theorem RustM.ok.injEq {α} {a b : α} : (RustM.ok a = .ok b) = (a = b) := by
  simp only [eq_iff_iff]
  exact ⟨fun h => RustM.ok_injective h, fun h => by simp [h]⟩

@[simp]
theorem RustM.fail.injEq {α} {a b : Error} : ((RustM.fail a : RustM α) = .fail b) = (a = b) := by
  simp only [eq_iff_iff]
  exact ⟨fun h => RustM.fail_injective h, fun h => by simp [h]⟩

-- TODO: when necessary, we may need a stronger version of this which outputs ≍ for the continuations
theorem RustM.vis.injEq {α} {a b} {k1 k2} : (@RustM.vis α a k1 = .vis b k2) → (a = b) := by
  intro h
  have h := congrArg RustM.match h
  simp only [RustM.match.vis, MatchResult.vis.injEq] at h
  exact h.left

@[simp]
theorem RustM.match.isOk {α : Type u} {a : α} {r : RustM α} : (r.match = .ok a) ↔ r = .ok a := by
  cases r <;> grind
@[simp]
theorem RustM.match.isVis {α : Type u} {e k} {r : RustM α} : (r.match = .vis e k) ↔ r = .vis e k := by
  cases r <;> grind
@[simp]
theorem RustM.match.isDiv {α : Type u} {r : RustM α} : (r.match = .div) ↔ r = .div := by
  cases r <;> grind

/-- `r.reducesTo expected` is `true` iff `r` evaluates to `ok expected`. -/
def RustM.reducesTo {R : Type} [BEq R] (r : RustM R) (expected : R) : Bool :=
  match r.match with
  | .ok x => x == expected
  | _ => false

open RustM

instance RustM_Inhabited (α : Type u) : Inhabited (RustM α) :=
  Inhabited.mk (fail panic)

instance RustM_Nonempty (α : Type u) : Nonempty (RustM α) :=
  Nonempty.intro div

/-!
# Helpers
-/

def massert (b : Prop) [Decidable b] : RustM Unit :=
  if b then ok () else fail panic

@[simp]
def RustM.ofOption {a : Type u} (x : Option a) (e : Error) : RustM a :=
  match x with
  | some x => ok x
  | none => fail e

@[simp] abbrev liftFun1 {α β} (f : α → β) : α → RustM β := fun x => ok (f x)
@[simp] abbrev liftFun2 {α β γ : Type} (f : α → β → γ) : α → β → RustM γ := fun x y => ok (f x y)
@[simp] abbrev liftFun3 {α β γ δ} (f : α → β → γ → δ) : α → β → γ → RustM δ := fun x y z => ok (f x y z)
@[simp] abbrev liftFun4 {α β γ δ ε} (f : α → β → γ → δ → ε) : α → β → γ → δ → RustM ε := fun x y z a => ok (f x y z a)

/-!
# Do-DSL Support
-/

@[simp] theorem bind_ok (x : α) (f : α → RustM β) : bind (.ok x) f = f x :=
  by simp [bind, ok]
@[simp] theorem bind_vis (e k) (f : α → RustM β) : bind (.vis e k) f = .vis e (fun x => bind (k x) f) :=
  by simp [bind, vis]
     rfl
@[simp] theorem bind_fail (e : Error) (f : α → RustM β) : bind (.fail e) f = .fail e := by
  simp only [RustM.fail_eq_vis, bind_vis]
  apply congrArg
  funext x
  exact x.elim

@[simp] theorem bind_div (f : α → RustM β) : bind .div f = .div := by simp [bind, div]



/-- Left identity. -/
protected theorem pure_bind {α : Type u} {β : Type v} (x : α) (f : α → RustM β) :
    bind (.ok x) f = f x := bind_ok x f

/-- Right identity. -/
@[simp] protected theorem bind_pure {α : Type u} (x : RustM α) : bind x .ok = x := by
  change ITree.bind x ITree.ret = x
  exact _root_.bind_pure (m := ITree RustEffect) x

/-- Associativity. -/
@[simp] protected theorem bind_assoc {α : Type u} {β : Type v} {γ : Type w}
    (x : RustM α) (f : α → RustM β) (g : β → RustM γ) :
    bind (bind x f) g = bind x (fun x => bind (f x) g) := by
  change ITree.bind (ITree.bind x f) g = ITree.bind x (fun x => ITree.bind (f x) g)
  ext n
  induction n generalizing x
  · rfl
  · rw [ITree.bind.eq_def x, ITree.bind.eq_def x]
    split
    · simp
    · simp
    · simp [*]

instance : LawfulMonad RustM := LawfulMonad.mk' RustM
  (id_map := Std.bind_pure)
  (pure_bind := Std.pure_bind)
  (bind_assoc := Std.bind_assoc)

/-- Normalize the typeclass bind (`>>=`) to `Std.bind`. -/
theorem bind_tc_eq {α β : Type u} (x : RustM α) (f : α → RustM β) :
    Bind.bind x f = bind x f := rfl

/-- Normalize the typeclass `pure` to `RustM.ok`. -/
theorem pure_tc_eq {α : Type u} (x : α) : (pure x : RustM α) = .ok x := rfl

@[simp] theorem bind_tc_ok (x : α) (f : α → RustM β) :
  (do let y ← .ok x; f y) = f x := by simp [bind, Bind.bind, ok]

@[simp] theorem bind_tc_vis (e k) (f : α → RustM β) :
  (do let y ← RustM.vis e k; f y) = .vis e (fun x => do let y ← k x; f y) := by
  simp [bind, Bind.bind, vis]
  rfl

@[simp] theorem bind_tc_fail (e : Error) (f : α → RustM β) :
  (do let y ← RustM.fail e; f y) = .fail e := by
  simp [Bind.bind]

@[simp] theorem bind_tc_div (f : α → RustM β) :
  (do let y ← div; f y) = div := by simp [bind, Bind.bind, div]

/-- `Std.bind_assoc` for the typeclass bind (whose computations live in the same universe). -/
@[simp] theorem bind_assoc_eq {a b c : Type u}
  (e : RustM a) (g :  a → RustM b) (h : b → RustM c) :
  (Bind.bind (Bind.bind e g) h) =
  (Bind.bind e (λ x => Bind.bind (g x) h)) := Std.bind_assoc e g h

end

unseal RustM
open RustM

/-!
# Partial Fixpoint
-/

section Order

open Lean.Order

instance : PartialOrder (RustM α) := instPartialOrderCoIndOfInhabitedPUnit (ITreeF RustEffect α)
noncomputable instance : CCPO (RustM α) := instCCPOCoIndOfInhabitedPUnit (ITreeF RustEffect α)
noncomputable instance : MonoBind RustM := instMonoBindITree

@[partial_fixpoint_monotone]
theorem bind_mono {R : Type a} {α} {S : Type b} [PartialOrder α]
  (f : α → RustM R) (g : α → R → RustM S) :
  monotone f →
  monotone g →
  monotone (λ x => bind (f x) (g x)) := by
    simp [bind]
    apply Aeneas.Data.Coinductive.bind_mono

-- TODO: when we add more effects, use Aeneas.Data.Coinductive.ITree.vis_mono
-- to instantiate monotonicity theorems for those effects.
-- This will allow partial fixpoint definitions that call the effects.

end Order

/-- Aeneas-internal version of `Function.uncurry` for tuple destructuring in bind
continuations. We use our own copy so that none of the `simp`/`step` attribute
manipulations we perform on it impact user-written specs that use `Function.uncurry`
directly.

`uncurry` is purely internal to Aeneas' elaboration pipeline and should never
be directly manipulated by the user. -/
@[expose, inline] def uncurry {α β γ} (f : α → β → γ) : α × β → γ :=
  fun (a, b) => f a b

@[simp, grind =] theorem uncurry_apply_pair {α β γ} (f : α → β → γ) (a : α) (b : β) :
    uncurry f (a, b) = f a b :=
  /- This proof is intentionally not `:= rfl`: `simp` would flag this lemma as
     a reflexivity lemma, meaning it would not apply it but would directly use
     `rfl` in the proofs, triggering unwanted whnf reductions in some calls
     to `step`. -/
  id rfl

/- reduction lemmas for `uncurry` restricted to functions whose end
result is `Prop`. Used by `step` to clean up spec post-conditions that
arrived as `uncurry p x` but where the call site didn't destructure further.

We restrict the final return type to `Prop` so the simp lemmas cannot fire on
bind continuations. `uncurry_eq_prop` handles the base case and
`uncurry_eq_prop_arrow` handles the curried case. -/

theorem uncurry_eq_prop {α β} (x : α × β) (p : α → β → Prop) :
    uncurry p x = p x.fst x.snd := by cases x; rfl

theorem uncurry_eq_prop_arrow {α β σ} (x : α × β) (p : α → β → σ → Prop) :
    uncurry p x = p x.fst x.snd := by cases x; rfl

/- Allow `partial_fixpoint` to see through `uncurry` in bind continuations.
This is needed because the custom `do` elaborator generates
`bind e (uncurry fun a b => rest)` for tuple-destructuring `let (a, b) ← e`. -/
section
open Lean.Order

@[partial_fixpoint_monotone]
theorem monotone_uncurry
    {α : Type u} {β : Type v} {φ : Sort w} [PartialOrder φ]
    {γ : Sort z} [PartialOrder γ]
    (f : γ → α → β → φ)
    (hmono : monotone f) :
    monotone (fun x => uncurry (f x)) := by
  intro x y hxy p
  simp [uncurry]
  exact monotone_apply p.2 _ (monotone_apply p.1 _ hmono) x y hxy

@[partial_fixpoint_monotone]
theorem monotone_uncurry_applied
    {α : Type u} {β : Type v} {φ : Sort w} [PartialOrder φ]
    {γ : Sort z} [PartialOrder γ]
    (f : γ → α → β → φ) (p : α × β)
    (hmono : monotone f) :
    monotone (fun x => uncurry (f x) p) := by
  intro x y hxy
  simp [uncurry]
  exact monotone_apply p.2 _ (monotone_apply p.1 _ hmono) x y hxy

end

attribute [simp, grind =] Function.uncurry_apply_pair

/-!
# Lift
-/

/-- We use this to lift pure function calls to monadic calls.
    We don't mark this as reducible so that **let-bindings don't get simplified away**.

    In the generated code if regularly happens that we want to lift pure function calls so
    that `step` can reason about them. For instance, `U32.wrapping_add` has type `U32 → U32 → U32`,
    but we provide a `step` theorem with an informative post-condition, and which matches the pattern
    `lift (wrapping_add x y)`. This theorem can only be looked up and appliced if the code is of the
    following shape:
    ```
    let z ← U32.wrapping_add x y
    ...
    ```

    The downside is that using `lift` forces users to write `step` theorems for pure expressions
    which appear inside a `lift`. As only a specific set of functions from the standard library are
    purified (i.e., don't live in `RustM`), this should not be a big issue in practice.
  -/
@[expose] def lift {α : Type u} (x : α) : RustM α := RustM.ok x

/-!
# Loops
-/

@[expose] section

inductive ControlFlow (α : Type u) (β : Type v) where
  | cont (v : α) -- continue
  | done (v : β) -- break
deriving Repr, BEq

def loop {α : Type u} {β : Type v} (body : α → RustM (ControlFlow α β)) (x : α) : RustM β := do
  bind (body x) fun r =>
  match r with
  | ControlFlow.cont x => loop body x
  | ControlFlow.done x => ok x
partial_fixpoint

end

/-!
# Misc
-/

/-- The Never type in Rust -/
inductive Never where

instance SubtypeBEq [BEq α] (p : α → Prop) : BEq (Subtype p) where
  beq v0 v1 := v0.val == v1.val

instance SubtypeLawfulBEq [BEq α] (p : α → Prop) [LawfulBEq α] : LawfulBEq (Subtype p) where
  eq_of_beq {a b} h := by cases a; cases b; simp_all [BEq.beq]
  rfl := by intro a; cases a; simp [BEq.beq]

/- A helper function that converts failure (and any effects) to none and success to some
   TODO: move up to Core module? -/
@[expose] def Option.ofRustM {a : Type u} (x : RustM a) :
  Option a :=
  match x.match with
  | .ok x => .some x
  | _ => .none

/-!
# bv_decide
-/

#define_bv_decide_toBitVec PUnit

/-!
# Dyn
-/

structure Dyn (Trait : Type u → Type v) where
  /-- The type Self -/
  self : Type u
  /-- The trait instance -/
  inst : Trait self
  /-- The value itself -/
  value : self

end Std

end Aeneas
