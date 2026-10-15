module
public import Aeneas.Std.Primitives
public import Aeneas.Std.Delab
public import Std.Do
public import Aeneas.Tactic.Solver.Grind.Init
public import Aeneas.Tactic.Step.DspecInduction
public meta import Aeneas.Std.Spec
public meta import Aeneas.Std.Delab
public import Aeneas.Data.Coinductive.ITree
public import Aeneas.Data.Coinductive.Effect
public import Aeneas.Data.Coinductive.ITreeWP
import all Init.Internal.Order.Basic
public section

namespace Aeneas.Std.WP

open Std RustM
open Aeneas.Data.Coinductive
open Lean.Order

@[expose] def Post α := (α -> Prop)
@[expose] def Pre := Prop

@[expose] def Wp α := Post α → Pre

@[expose] def wp_return (x:α) : Wp α := fun p => p x

section ResultImplementation

unseal RustM

@[expose] section

/-- The WP of the effects of Rust programs (`RustEffect`). -/
@[reducible]
def effectWP : EffectWP RustEffect where
  State := Unit
  wp effect _ _ :=
    match effect with
    | .fail _ => False

instance : EffectWP.Monotonic effectWP where
  wp_monotonic _ := False.elim

instance : EffectWP.Conjunctive effectWP where
  wp_conj := by
    intro _ _ _ hNonempty hAll
    obtain ⟨C₀, hC₀⟩ := hNonempty
    exact (hAll C₀ hC₀).elim

instance : EffectWP.ExcludedMiracle effectWP where
  wp_excludedMiracle := by
    rintro ⟨⟩ _ h
    exact h

def spec (m : RustM α) (p : Post α) : Prop :=
  DWP effectWP m (fun value _ => p value) ()

def dspec (m : RustM α) (p : Post α) : Prop :=
  DWLP effectWP m (fun value _ => p value) ()

theorem spec_dspec (α) (x : RustM α) (p: Post α) : spec x p → dspec x p :=
  DWP.toPartial

theorem dspec_admissible {α} (p : Post α) :
    admissible (fun x => dspec x p) :=
  DWLP.admissible effectWP _ ()

end

/-- The shape the `dspec_induction` tactic needs to discharge the admissibility
side-goal it generates for a partial specification about a recursive function. -/
@[dspec_admissible]
theorem dspec_func_admissible {α : Sort v} {β} (arg : α) (p : Post β) :
    admissible (fun f : α → RustM β => dspec (f arg) p) :=
  admissible_apply (fun _ m => dspec m p) arg (dspec_admissible p)

/-- Variant of `uncurry` used to decompose tuples in post-conditions.

Similar to `uncurry` but delaborated differently:
`uncurry'` is delaborated as `x y => ...` (separate binders), while
`uncurry` is delaborated as `(x, y) => ...` (tuple binder).
We use this in the Hoare triple notation `⦃ ⦄`.

Example: `f 0 ⦃ x y z => ... ⦄` desugars to
`spec (f 0) (uncurry' fun x => uncurry' fun y z => ...)`.
-/

@[expose]
def uncurry' {α β γ : Type _} (p : α → β → γ) : α × β → γ :=
  fun (x, y) => p x y

@[simp] theorem uncurry'_pair x y (p : α → β → γ) : uncurry' p (x, y) = p x y := by simp [uncurry']
@[defeq] theorem uncurry'_eq x (p : α → β → γ) : uncurry' p x = p x.fst x.snd := by simp [uncurry']

@[simp, grind =, agrind =]
theorem spec_ok (x : α) : spec (ok x) p ↔ p x := DWP.ret_iff

@[simp, grind =, agrind =]
theorem spec_vis (e k) : spec (.vis e k) p ↔ False := ⟨fun h => DWP.vis_view h, False.elim⟩

@[simp, grind =, agrind =]
theorem spec_fail (e : Error) : spec (fail e) p ↔ False := by simp [RustM.fail_eq_vis]

@[simp, grind =, agrind =]
theorem spec_div : spec div p ↔ False := ⟨DWP.div_false, False.elim⟩

/-! ### `spec_*` for tuple posts

Needed now with the new `uncurry`-based pattern matching. -/

@[simp, grind =, agrind =]
theorem spec_ok_pair {α β} (a : α) (b : β) (f : α → β → Prop) :
    spec (ok (a, b)) (uncurry f) ↔ f a b := by
  simp [spec_ok]

@[simp, grind =, agrind =]
theorem spec_fail_pair (e : Error) (f : α → β → Prop) :
    spec (fail e) (uncurry f) ↔ False := by simp

@[simp, grind =, agrind =]
theorem spec_div_pair (f : α → β → Prop) :
    spec div (uncurry f) ↔ False := by simp

/-- Mono rule used by `step`. -/
theorem spec_mono {α} {P₁ : Post α} {m : RustM α} {P₀ : Post α} (h : spec m P₀):
  (∀ x, P₀ x → P₁ x) → spec m P₁ :=
  fun HMonPost => DWP.mono h fun value _ => HMonPost value

/-- Bind rule used by `step`. It is stated on `Std.bind` rather than on `>>=`, which is
what a translated program binds with. -/
theorem spec_bind {α β} {k : α -> RustM β} {Pₖ : Post β} {m : RustM α} {Pₘ : Post α} :
  spec m Pₘ →
  (∀ x, Pₘ x → spec (k x) Pₖ) →
  spec (Std.bind m k) Pₖ :=
  fun Hm Hk => DWP.bind (k := k) Hm fun value _ => Hk value

theorem spec_and {m : RustM α} {p q : Post α} (h₁ : spec m p) (h₂ : spec m q) :
    spec m (fun value => p value ∧ q value) :=
  DWP.and_iff.mpr ⟨h₁, h₂⟩

theorem spec_exists {m : RustM α} {p : Post α} (h : spec m p) : ∃ value, p value :=
  let ⟨value, _, hp⟩ := DWP.exists h
  ⟨value, hp⟩

-- `dspec` theorems
theorem dspec_mono {α} {P₁ : Post α} {m : RustM α} {P₀ : Post α} (h : dspec m P₀):
  (∀ x, P₀ x → P₁ x) → dspec m P₁ :=
  fun HMonPost => DWLP.mono h fun value _ => HMonPost value

theorem dspec_bind {α β} {k : α -> RustM β} {Pₖ : Post β} {m : RustM α} {Pₘ : Post α} :
  dspec m Pₘ →
  (∀ x, Pₘ x → dspec (k x) Pₖ) →
  dspec (Std.bind m k) Pₖ :=
  fun Hm Hk => DWLP.bind (k := k) Hm fun value _ => Hk value

@[simp, grind =, agrind =]
theorem dspec_ok (x : α) : dspec (ok x) p ↔ p x := DWLP.ret_iff

@[simp, grind =, agrind =]
theorem dspec_vis (e k) : dspec (.vis e k) p ↔ False := ⟨fun h => DWLP.vis_view h, False.elim⟩

@[simp, grind =, agrind =]
theorem dspec_div : dspec (div : RustM α) p ↔ True := iff_true_intro DWLP.div

@[simp, grind =, agrind =]
theorem dspec_fail (e : Error) : dspec (fail e) p ↔ False := by simp [RustM.fail_eq_vis]

theorem dspec_and {m : RustM α} {p q : Post α} (h₁ : dspec m p) (h₂ : dspec m q) :
    dspec m (fun value => p value ∧ q value) :=
  DWLP.and_iff.mpr ⟨h₁, h₂⟩

end ResultImplementation

end Aeneas.Std.WP

/-
We want the notations to live in the namespace `Aeneas`, not `Aeneas.Std.WP`
TODO: use https://github.com/leanprover/lean4/pull/11355
-/
namespace Aeneas

open Std WP RustM

/-!
# Hoare triple notation and elaboration
-/

/- We use a priority of 55 for the inner term, which is exactly the priority for `|||`.
This way we can expressions like: `x + y ⦃ z => ... ⦄` without having to put parentheses around `x + y`. -/
scoped syntax:54 term:55 " ⦃ " term+ " => " term " ⦄" : term
scoped syntax:54 term:55 " ⦃ " term " ⦄" : term

-- for dspec
scoped syntax:54 term:55 " ⦃ " term+ " => " term " ⦄div" : term
scoped syntax:54 term:55 " ⦃ " term " ⦄div" : term

open Lean PrettyPrinter

/-- Build a `Std.uncurry` chain wrapping a curried lambda over `xs`.

Given `x0`, ..., `xn` and `body`, generates the (syntactic) term `fun (x0, ..., xn) => body`.
-/
meta partial def buildUncurryLam (xs : List (TSyntax `term)) (body : TSyntax `term) :
    MacroM (TSyntax `term) := do
  let uncurryIdent := mkIdent ``Std.uncurry
  match xs with
  | [] => pure body
  | [x] => `(fun $x => $body)
  | [a, b] => `($uncurryIdent (fun $a $b => $body))
  | a :: rest =>
    let inner ← buildUncurryLam rest body
    `($uncurryIdent (fun $a => $inner))

/-- Helper to elaborate `binder => body` when binder is a tuple - this supports nested tuples. -/
meta partial def mkBinderFun (depth : Nat) (binder : Term) (body : Term) : MacroM Term := do
  match binder with
  | `( ($a, $bs,*) ) =>
    let xs : List Term := a :: bs.getElems.toList
    let mut leafIdents : List Term := []
    let mut wrappedBody := body
    for (x, idx) in xs.zipIdx.reverse do
      match x with
      | `( ($_, $_,*) ) =>
        -- Fresh identifier from depth + index
        let freshIdent := mkIdent $ .mkSimple s!"_p_{depth}_{idx}"
        let inner ← mkBinderFun (depth + 1) x wrappedBody
        wrappedBody ← `($inner $freshIdent)
        leafIdents := freshIdent :: leafIdents
      | _ =>
        leafIdents := x :: leafIdents
    buildUncurryLam leafIdents wrappedBody
  | _ => `(fun $binder => $body)

meta def mk_function_syntax (p : TSyntax `term) (depth : Nat) (xs : List Term) : MacroM Term := do
  match xs with
  | [] => `($p)
  | [x] => mkBinderFun depth x p
  | x :: xs =>
    let xs ← mk_function_syntax p (depth + 1) xs
    let inner ← mkBinderFun depth x xs
    `(uncurry' $inner)

/-- If `stx` is a bare identifier or a juxtaposition (application) of bare
identifiers — i.e. a binder group like `a b c` — return the identifiers in
order.  Otherwise return `none`, so anonymous constructors `⟨a, b⟩`, tuple
patterns, and other structured terms are left untouched. -/
private meta partial def binderGroupIdents? (stx : Syntax) : Option (Array Term) :=
  if stx.isIdent then some #[⟨stx⟩]
  else if stx.getKind == ``Lean.Parser.Term.app || stx.getKind == Lean.nullKind then
    stx.getArgs.foldlM (init := (#[] : Array Term)) fun acc s =>
      (binderGroupIdents? s).map (acc ++ ·)
  else none

/-- Expand a binder that shares one type ascription across several names —
`(a b c : T)` — into the list of single binders `[(a : T), (b : T), (c : T)]`,
so each name becomes its own product component (exactly as if written
separately).  Tuple/pattern binders `(a, b)`, `(⟨a, b⟩ : T)`, single binders
`(a : T)`, and bare identifiers are returned unchanged. -/
private meta def expandGroupedBinder (binder : Term) : MacroM (List Term) := do
  match binder with
  | `(($e : $t)) =>
    match binderGroupIdents? e.raw with
    | some ids =>
      if ids.size ≤ 1 then pure [binder]
      else ids.toList.mapM fun id => `(($id : $t))
    | none => pure [binder]
  | _ => pure [binder]

/-- Flatten grouped binders across the whole binder list. -/
private meta def expandBinders (xs : List Term) : MacroM (List Term) := do
  let mut out : Array Term := #[]
  for x in xs do
    out := out ++ (← expandGroupedBinder x).toArray
  pure out.toList

/-- Build the postcondition term for `⦃ xs => p ⦄`, expanding grouped binders
into one component per name first. -/
private meta def mkPost (p : Term) (xs : List Term) : MacroM Term := do
  mk_function_syntax p 0 (← expandBinders xs)

/-- Macro expansion for a single element (may expand to several via a grouped binder) -/
macro_rules
  | `($e ⦃ $x => $p ⦄) => do
    let post ← mkPost p [x]
    `(Aeneas.Std.WP.spec $e $post)
  | `($e ⦃ $x => $p ⦄div) => do
    let post ← mkPost p [x]
    `(Aeneas.Std.WP.dspec $e $post)

/-- Macro expansion for multiple elements -/
macro_rules
  | `($e ⦃ $x $xs:term* => $p ⦄) => do
    let post ← mkPost p (x :: xs.toList)
    `(Aeneas.Std.WP.spec $e $post)
  | `($e ⦃ $x $xs:term* => $p ⦄div) => do
    let post ← mkPost p (x :: xs.toList)
    `(Aeneas.Std.WP.dspec $e $post)

/-- Macro expansion for predicate with no arrow -/
macro_rules
  | `($e ⦃ $p ⦄) => do `(_root_.Aeneas.Std.WP.spec $e $p)
  | `($e ⦃ $p ⦄div) => do `(_root_.Aeneas.Std.WP.dspec $e $p)

/-!
# Pretty-printing

The `⦃ ⦄` macro produces postconditions using three wrappers:
- `uncurry' (fun x => ...)` — separate binders, printed as `x y z => ...`
- `uncurry (fun a b => ...)` — tuple binder, printed as `(a, b) => ...`
- Plain `fun x => ...` — scalar binder

`uncurry'` is never nested: it only appears at the outermost level to separate
top-level product components. `uncurry` can be nested inside `uncurry'` or other
`uncurry` applications (for sub-tuples like `((a, b), c)`).

**Examples of elaborated postconditions:**

| Source | Elaborated form |
|---|---|
| `⦃ r => body ⦄` | `fun r => body` |
| `⦃ (a, b) => body ⦄` | `uncurry (fun a b => body)` |
| `⦃ x y z => body ⦄` | `uncurry' (fun x => uncurry' (fun y z => body))` |
| `⦃ (a, b) c => body ⦄` | `uncurry' (uncurry (fun a b => fun c => body))` |
| `⦃ a (b, c) => body ⦄` | `uncurry' (fun a => uncurry (fun b c => body))` |
| `⦃ ((a,b), c) => body ⦄` | `uncurry (fun _p c => (uncurry (fun a b => body)) _p)` |
| `⦃ ((a,b), (c,d)) => body ⦄` | `uncurry (fun _p₀ _p₁ => (uncurry (fun a b => (uncurry (fun c d => body)) _p₁)) _p₀)` |

The delaborator reverses this: given a `spec e post` expression, it peels the
wrapper layers to recover the binder patterns and body, producing `⦃ ... => ... ⦄`.

The `uncurry`/lambda machinery (`enterLams`, `enterUncurryChain`, `delabBinders`)
is reused from `Do.Delab` (which handles the same `uncurry` chains in `do`-notation).
The only WP-specific logic is the `uncurry'`-peeling loop on top.
-/

open Delaborator SubExpr
open Std.Delab (enterLams enterUncurryChain delabBinders buildTupleTerm delabUncurryAsTuple)

/-- Enter exactly the binders of a single `uncurry` level (up to 2).
Unlike `enterUncurryChain` (which flattens everything), this stops after 2 binders
so the continuation lambdas are left untouched.

Example: on `fun a b => fun c => body`, collects `[a, b]` and leaves the reader
at `fun c => body`. -/
private meta partial def enterUncurryOnce (acc : Array Std.Delab.BinderEntry)
    (k : Array Std.Delab.BinderEntry → DelabM α) : DelabM α := do
  match (← getExpr) with
  | .lam n _ _ _ =>
    let pos ← getPos
    withBindingBody' n pure fun fv => do
      let acc' := acc.push (fv.fvarId!, n, pos)
      if acc'.size >= 2 then k acc'
      else if (← getExpr).isAppOfArity ``Std.uncurry 4 then
        withAppArg <| enterUncurryOnce acc' k
      else enterUncurryOnce acc' k
  | _ => k acc

/-- Is the expression an `uncurry'` or `uncurry` wrapper? -/
private meta def isPostBinderWrapper (e : Expr) : Bool :=
  match_expr e.consumeMData with
  | uncurry' _ _ _ _ => true
  | uncurry _ _ _ _ => true
  | _ => false

/-- Walk the postcondition expression, peeling `uncurry'`/`uncurry`/lambda layers.
Returns `(binders, bodyTerm)` where each binder is a `Term` (either a plain
name like `x` or a (potentially nested) tuple pattern like `(a, b)`).
-/
private meta partial def delabPostBinders : DelabM (Array Term × Term) := do
  match_expr (← getExpr).consumeMData with
  | uncurry' _ _ _ _ =>
    /- `uncurry' f`: dive into `f` (arg 3) and peel one binder.
       If `f = uncurry g`, the binder is a tuple `(a, b)`.
       If `f = fun x => rest`, the binder is scalar `x`. -/
    withNaryArg 3 do
      match_expr (← getExpr).consumeMData with
      | uncurry _ _ _ _ =>
        -- Tuple binder: peel one uncurry level, then recurse for more binders
        withAppArg <| enterUncurryOnce #[] fun tupleBinders => do
          let (pats, (moreBinders, body)) ← delabBinders tupleBinders.toList delabPostBinders
          let tupleTerm ← buildTupleTerm pats
          return (#[tupleTerm] ++ moreBinders, body)
      | _ => delabLamsThenRecurse
  | uncurry _ _ _ _ =>
    /- Single tuple binder `(a, b) => body` (no `uncurry'` wrapper). -/
    let tuplePos ← getPos
    withAppArg do
      let (tupleTerm, body) ← delabUncurryAsTuple delab
      let tupleTerm : Term := annotatePos tuplePos tupleTerm
      addTermInfo tuplePos tupleTerm.raw (← getExpr) (isBinder := true)
      return (#[tupleTerm], body)
  | _ => delabLamsThenRecurse
where
  /-- Peel plain lambda binders, then either recurse or terminate.

  This is used in two situations:
  - Inside `uncurry'`, when the argument is a plain lambda (not `uncurry`):
    e.g., `uncurry' (fun x => uncurry' (fun y z => body))` — after entering
    `fun x =>`, the body starts with another `uncurry'`, so we recurse.
  - At the top level, when the postcondition is a plain lambda without any
    `uncurry'`/`uncurry` wrapper: e.g., `fun r => body`.

  The key logic: if `enterLams` peels exactly one lambda and the body is a
  wrapper (`uncurry'` or `uncurry`), this lambda is a scalar binder in a
  multi-binder postcondition — recurse via `delabPostBinders` to peel more.
  Otherwise these are terminal binders (e.g., `fun y z => body` at the last
  `uncurry'` level) — delab the body directly. -/
  delabLamsThenRecurse : DelabM (Array Term × Term) := do
    if (← getExpr).consumeMData.isLambda then
      enterLams #[] fun binders => do
        if binders.size == 1 && isPostBinderWrapper (← getExpr) then
          let (pats, (moreBinders, body)) ← delabBinders binders.toList delabPostBinders
          return (pats ++ moreBinders, body)
        else
          let (pats, body) ← delabBinders binders.toList delab
          return (pats, body)
    else
      return (#[], ← delab)

/-- Delaborator for `WP.spec e post` → `e ⦃ binders => body ⦄`. -/
@[scoped delab app.Aeneas.Std.WP.spec]
meta def delabSpec : Delab := do
  guard $ (← getExpr).isAppOfArity' ``spec 3
  let monadExpr ← withNaryArg 1 delab
  let (binders, bodyTerm) ← withNaryArg 2 delabPostBinders
  if binders.size == 0 then
    `($monadExpr ⦃ $bodyTerm ⦄)
  else
    `($monadExpr ⦃ $(binders[0]!) $(binders.drop 1)* => $bodyTerm ⦄)

/-- Delaborator for `WP.dspec e post` → `e ⦃ binders => body ⦄div`. -/
@[scoped delab app.Aeneas.Std.WP.dspec]
meta def delabDSpec : Delab := do
  guard $ (← getExpr).isAppOfArity' ``dspec 3
  let monadExpr ← withNaryArg 1 delab
  let (binders, bodyTerm) ← withNaryArg 2 delabPostBinders
  if binders.size == 0 then
    `($monadExpr ⦃ $bodyTerm ⦄div)
  else
    `($monadExpr ⦃ $(binders[0]!) $(binders.drop 1)* => $bodyTerm ⦄div)

/-!
# Tests
-/

/-- error: unsolved goals
⊢ ok 0 ⦃ r => r = 0 ⦄ -/
#guard_msgs in example : ok 0 ⦃ r => r = 0 ⦄ := by done
/-- error: unsolved goals
⊢ ok 0 ⦃ x✝ => True ⦄ -/
#guard_msgs in example : spec (ok 0) fun _ => True := by done
/-- error: unsolved goals
⊢ ok 0 ⦃ x✝ => True ⦄ -/
#guard_msgs in example : ok 0 ⦃ _ => True ⦄ := by done
/-- error: unsolved goals
⊢ ok (0, 1) ⦃ x✝ =>
    match x✝ with
    | (x, y) => x = 0 ∧ y = 1 ⦄ -/
#guard_msgs in example : spec (ok (0, 1)) fun (x, y) => x = 0 ∧ y = 1 := by done
/-- error: unsolved goals
⊢ ok (0, 1) ⦃ (x, y) => x = 0 ∧ y = 1 ⦄ -/
#guard_msgs in example : ok (0, 1) ⦃ (x, y) => x = 0 ∧ y = 1 ⦄ := by done
/-- error: unsolved goals
⊢ ok (0, 1) ⦃ x y => x = 0 ∧ y = 1 ⦄ -/
#guard_msgs in example : ok (0, 1) ⦃ x y => x = 0 ∧ y = 1 ⦄ := by done
/-- error: unsolved goals
⊢ ok (0, 1, 2) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = 2 ⦄ -/
#guard_msgs in example : ok (0, 1, 2) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = 2 ⦄ := by done
/-- error: unsolved goals
⊢ ok (0, 1, true) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = true ⦄ -/
#guard_msgs in example : ok (0, 1, true) ⦃ x y z => x = 0 ∧ y = 1 ∧ z ⦄ := by done
/-- error: unsolved goals
⊢ let P := fun x => x = 0;
  ok 0 ⦃ P ⦄ -/
#guard_msgs in example : let P (x : Nat) := x = 0; ok 0 ⦃ P ⦄ := by done

/-! ### Mixed tuple / scalar binders -/

/-- error: unsolved goals
⊢ ok ((0, 1), 2) ⦃ (a, b) c => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in -- Tuple followed by scalar
example : ok ((0, 1), 2) ⦃ (a, b) c => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2) ⦃ ((a, b), c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in -- Same but with nesting
example : ok ((0, 1), 2) ⦃ ((a, b), c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok (0, 1, 2) ⦃ a (b, c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in -- Scalar followed by tuple
example : ok (0, (1, 2)) ⦃ a (b, c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok (0, 1, 2) ⦃ (a, (b, c)) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in -- Same but with nesting
example : ok (0, (1, 2)) ⦃ (a, (b, c)) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2, 3) ⦃ (a, b) (c, d) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ -/
#guard_msgs in -- Two tuples in sequence
example : ok ((0, 1), (2, 3)) ⦃ (a, b) (c, d) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2, 3) ⦃ ((a, b), (c, d)) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ -/
#guard_msgs in -- Same but with nesting
example : ok ((0, 1), (2, 3)) ⦃ ((a, b), (c, d)) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2) ⦃ ((a, b), c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in -- A single nested tuple
example : ok ((0, 1), 2) ⦃ ((a, b), c) => a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2, 3) ⦃ ((a, b), (c, d)) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ -/
#guard_msgs in -- Two nested tuples
example : ok ((0, 1), (2, 3)) ⦃ ((a, b), (c, d)) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ := by done

/-- error: unsolved goals
⊢ ok (0, (1, 2), 3, 4, 5) ⦃ a (b, c) (d, (e, f)) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ∧ f = 5 ⦄ -/
#guard_msgs in -- Scalar, tuple, nested tuple
example : ok (0, (1, 2), (3, (4, 5))) ⦃ a (b, c) (d, (e, f)) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ∧ f = 5 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1, 2, 3), 4) ⦃ ((a, (b, (c, d))), e) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ⦄ -/
#guard_msgs in -- More nesting
example : ok ((0, (1, (2, 3))), 4) ⦃ ((a, (b, (c, d))), e) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ⦄
  := by done

/-! ### Pretty-printing round-trip checks -/

/-- error: unsolved goals
⊢ ok (0, 1, 2) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = 2 ⦄ -/
#guard_msgs in example : ok (0, 1, 2) ⦃ x y z => x = 0 ∧ y = 1 ∧ z = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2) ⦃ (a, b) c => a = 0 ∧ b = 1 ∧ c = 2 ⦄ -/
#guard_msgs in example : ok ((0, 1), 2) ⦃ (a, b) c =>
    a = 0 ∧ b = 1 ∧ c = 2 ⦄ := by done

/-- error: unsolved goals
⊢ ok ((0, 1), 2, 3) ⦃ (a, b) (c, d) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ -/
#guard_msgs in example : ok ((0, 1), (2, 3)) ⦃ (a, b) (c, d) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ⦄ := by done

/-- error: unsolved goals
⊢ ok (0, (1, 2), (3, 4, 5), 6) ⦃ a (b, c) ((d, e, f), g) => a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ∧ f = 5 ∧ g = 6 ⦄ -/
#guard_msgs in example : ok (0, (1, 2), ((3, 4, 5), 6)) ⦃ a (b, c) ((d, e, f), g) =>
    a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3 ∧ e = 4 ∧ f = 5 ∧ g = 6 ⦄ := by done

end Aeneas

namespace Aeneas.Std.WP

section
  variable (U32 : Type) [HAdd U32 U32 (RustM U32)]
  variable (x y : U32)

  #elab x + y ⦃ _ => True ⦄
  #elab True → x + y ⦃ _ => True ⦄
  #elab True ∧ x + y ⦃ _ => True ⦄

  -- Checking what happpens if we put post-conditions inside post-conditions
  example (f : Nat → RustM (Nat × (Nat → RustM Nat)))
          (_ : ∀ x, f x ⦃ (y, g) => y > 0 ∧ ∀ x, g x ⦃ z => z > y ⦄ ⦄ ∧ True)
   : True := by simp only
end

def add1 (x : Nat) := RustM.ok (x + 1)
theorem  add1_spec (x : Nat) : add1 x ⦃ y => y = x + 1⦄ :=
  by simp [add1]

/-- Example with a single output. -/
example (x : Nat) :
  (do
    let y ← add1 x
    add1 y) ⦃ y => y = x + 2 ⦄ := by
    -- step as ⟨ y, z ⟩
    apply spec_bind (add1_spec _)
    intro y h
    -- step as ⟨ y1, z1⟩
    apply spec_mono (add1_spec _)
    intro y' h
    --
    grind

def add2 (x : Nat) := RustM.ok (x + 1, x + 2)

theorem  add2_spec (x : Nat) : add2 x ⦃ (y, z) => y = x + 1 ∧ z = x + 2⦄ :=
  by simp [add2]

/-- Example with a tuple output. -/
example (x : Nat) :
  (do
    let (y, _) ← add2 x
    add2 y) ⦃ (y, _) => y = x + 2 ⦄ := by
    -- step as ⟨ y, z ⟩
    apply spec_bind
    . apply add2_spec
    simp only [Prod.forall, uncurry_apply_pair, and_imp]
    intro y z h0 h1
    -- step as ⟨ y1, z1⟩
    apply spec_mono
    . apply add2_spec
    simp only [Prod.forall, uncurry_apply_pair, and_imp]
    intro y1 z1 h2 h3
    grind

theorem  add2_spec' (x : Nat) : add2 x ⦃ y z => y = x + 1 ∧ z = x + 2⦄ :=
  by simp [add2]

/-- The same with separate binders: the post-condition is wrapped in the `uncurry'` marker,
which is reduced when rewriting the goal with separate output quantifiers. -/
example (x : Nat) :
  (do
    let (y, _) ← add2 x
    add2 y) ⦃ y _ => y = x + 2 ⦄ := by
    -- step as ⟨ y, z ⟩
    apply spec_bind
    . apply add2_spec'
    simp only [Prod.forall, uncurry'_pair, and_imp]
    intro y z h0 h1
    -- step as ⟨ y1, z1⟩
    apply spec_mono
    . apply add2_spec'
    simp only [Prod.forall, uncurry'_pair, and_imp]
    intro y1 z1 h2 h3
    grind

private theorem massert_spec' (b : Prop) [Decidable b] (h : b) :
  massert b ⦃ _ => True ⦄ := by
  grind [massert]

/-- Example with a function outputting `()` (we need to eliminate the quantifier) -/
example :
  (do
    massert (0 < 1);
    massert (1 < 2)
    ) ⦃ _ => True ⦄
  := by
  --
  apply spec_bind
  · apply massert_spec'; decide
  simp only [forall_const]
  --
  apply spec_mono
  · apply massert_spec'; decide
  simp only [forall_const]

/- Example with a post-condition manipulating an ∃ -/
example (zero : List Nat → RustM (List Nat))
    (zero_spec : ∀ s, zero s ⦃ s' =>
      ∃ (h : s'.length = s.length),
      (∀ i, (_ : i < s.length) → s'[i]'(by grind) = 0) ⦄)
    (s : List Nat) :
    (do
      let _ ← zero s
      pure ()) ⦃ _ => True ⦄ := by
  apply spec_bind
  · apply zero_spec
  rintro _ ⟨_, _⟩
  --
  simp only [pure, spec_ok]


end Aeneas.Std.WP

namespace Aeneas.Std.WP

/-!
# mvcgen
-/

open Std RustM
open Std.Do

-- mvcgen does not support all types of effects, and currently this implementation only works with fail and div.
-- This option is set here so that this same code works for any extension to RustEffect.Input
set_option match.ignoreUnusedAlts true
-- There are three types of exceptions in the type: the Error from RustM.fail,
-- a dummy exception thrown when any other effect is used, and RustM.div.
instance RustM.instWP : WP RustM.{u} (.except (ULift Error) (.except PUnit (.except PUnit .pure))) where
  wp x := {
    trans Q := match x.match with
      | .ok a => Q.1 a
      | .vis eff _ =>
        match eff with
        | .fail e => Q.2.1 (ULift.up e)
        | _ => Q.2.2.1 PUnit.unit
      | .div => Q.2.2.2.1 .unit
    conjunctiveRaw Q₁ Q₂ := by
      apply SPred.bientails.of_eq
      cases x <;> simp
  }
set_option match.ignoreUnusedAlts false

instance RustM.instWPMonad : WPMonad RustM (.except (ULift Error) (.except PUnit (.except PUnit .pure))) where
  wp_pure a := by apply PredTrans.ext; intro Q; simp [PredTrans.apply, wp, WP.wp]; rfl
  wp_bind x f := by
    apply PredTrans.ext
    intro Q
    simp [PredTrans.apply, wp, WP.wp]
    cases x
    · cbv
    · simp
      rename_i i k
      cases i <;> cbv
    · cbv


theorem RustM.of_wp {α : Type u} {x : RustM α} (P : RustM α → Prop) :
    (⊢ₛ wp⟦x⟧ (fun a => ⌜P (.ok a)⌝,
                  fun e => ⌜P (.fail e.down)⌝,
                  fun _ => ⌜False⌝, -- unreachable: `RustEffect` currently only has the `fail` effect.
                  fun .unit => ⌜P .div⌝, .unit)) → P x := by
    intro hspec
    simp only [WP.wp, PredTrans.apply] at hspec
    split at hspec <;> simp_all
    rename_i x eff heq a
    cases eff
    have : heq = PEmpty.elim := by funext; contradiction
    simp [*] at *
    try trivial


/-- Lift an Aeneas step spec to an mvcgen-compatible `Triple`. -/
theorem spec_to_mvcgen {α : Type u} {x : RustM α} {Q : α → Prop}
    (h : spec x Q) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ Q r ⌝ ⦄ := by
  cases x <;> simp_all [Triple, WP.wp, PredTrans.apply]

theorem dspec_to_mvcgen {α : Type u} {x : RustM α} {Q : α → Prop}
    (h : dspec x Q) :
    ⦃ ⌜ ¬ x = .div ⌝ ⦄ x ⦃ ⇓ r => ⌜ Q r ⌝ ⦄ := by
  simp [Triple, WP.wp, PredTrans.apply, SPred.pure]
  cases x <;> simp [*] at *
  trivial

end Aeneas.Std.WP

namespace Aeneas.Std

/-!
# Loops
-/

/-- General spec for loops with a termination measure.

It is meant to derive lemmas to reason about loops: in most situations, one shouldn't
have to use it directly when verifying programs.
-/
theorem loop.spec {α : Type u} {β : Type v} {γ : Type w}
  (measure : α → γ)
  [wf : WellFoundedRelation γ]
  (inv : α → Prop)
  (post : β → Prop)
  (body : α → RustM (ControlFlow α β)) (x : α)
  (hBody :
    ∀ x, inv x → body x ⦃ r =>
      match r with
      | .done y => post y
      | .cont x' => inv x' ∧ wf.rel (measure x') (measure x) ⦄)
  (hInv : inv x) :
  loop body x ⦃ post ⦄ := by
  suffices ∀ x' x, measure x = x' → inv x → loop body x ⦃ post ⦄
    by apply this <;> first | rfl | assumption
  apply @wf.wf.fix γ (fun x' =>
    ∀ x, measure x = x' →
    inv x → loop body x ⦃ post ⦄)
  intro y ih x eq ix
  subst eq
  unfold loop
  apply WP.spec_bind (hBody x ix)
  intro r hr
  cases r with
  | done z => simpa using hr
  | cont x' => exact ih (measure x') hr.2 x' rfl hr.1

theorem loop.spec_decr_nat {α : Type u} {β : Type v}
  (measure : α → Nat)
  (inv : α → Prop)
  (post : β → Prop)
  (body : α → RustM (ControlFlow α β)) (x : α)
  (hBody :
    ∀ x, inv x → body x ⦃ r =>
      match r with
      | .done y => post y
      | .cont x' => inv x' ∧ measure x' < measure x ⦄)
  (hInv : inv x) :
  loop body x ⦃ post ⦄ := by
  have := loop.spec measure inv post body x hBody hInv
  apply this

end Aeneas.Std

namespace Aeneas.Std.WP

/-- Note that `forall_const` is too general: it can eliminate unused outputs that we actually
want to introduce in the context -/
theorem forall_unit {p : Prop} : (Unit → p) ↔ p := by simp

end Aeneas.Std.WP

/-!
# `mvcgen` specs

Accessors for the postconditions of `RustM` programs, `@[spec]` lemmas for `mvcgen`, and lemmas
relating triples to `RustM.ok`.
-/

namespace Aeneas.Std

open Std.Do WP RustM
open Aeneas.Data.Coinductive

/-- The post-shape of `RustM` in `mvcgen`: a failure (`Error`), any other effect, divergence. -/
abbrev RustM.postShape : PostShape :=
  .except (ULift Error) (.except PUnit (.except PUnit .pure))

abbrev PostCond.okAssertion {α : Type u} (Q : PostCond α RustM.postShape) (r : α) :
    Assertion RustM.postShape :=
  Q.1 r

abbrev PostCond.ok {α : Type u} (Q : PostCond α RustM.postShape) (r : α) : Prop :=
  (Q.1 r).down

abbrev PostCond.failAssertion {α : Type u} (Q : PostCond α RustM.postShape) (e : ULift Error) :
    Assertion RustM.postShape :=
  Q.2.1 e

abbrev PostCond.fail {α : Type u} (Q : PostCond α RustM.postShape) (e : Error) : Prop :=
  (Q.2.1 (.up e)).down

/-- The postcondition for effects other than failure (`RustM` has none at the moment). -/
abbrev PostCond.otherAssertion {α : Type u} (Q : PostCond α RustM.postShape) :
    PUnit → Assertion RustM.postShape :=
  Q.2.2.1

abbrev PostCond.divAssertion {α : Type u} (Q : PostCond α RustM.postShape) :
    PUnit → Assertion RustM.postShape :=
  Q.2.2.2.1

abbrev PostCond.div {α : Type u} (Q : PostCond α RustM.postShape) : Prop :=
  (Q.2.2.2.1 .unit).down

@[spec]
theorem RustM.ok_spec {α : Type} {a : α} {Q : PostCond α RustM.postShape}
    (hQ : PostCond.ok Q a) :
    ⦃ ⌜ True ⌝ ⦄ RustM.ok a ⦃ Q ⦄ := by
  simpa [Triple, WP.wp, PredTrans.apply]

@[spec]
theorem RustM.fail_spec {α : Type} {e : Error} {Q : PostCond α RustM.postShape}
    (hQ : PostCond.fail Q e) :
    ⦃ ⌜ True ⌝ ⦄ (RustM.fail e : RustM α) ⦃ Q ⦄ := by
  simpa [Triple, WP.wp, PredTrans.apply]

attribute [spec] uncurry

/-- A triple with postcondition `r = v` is equivalent to the program being `.ok v`. -/
theorem triple_post_eq_iff_eq {α : Type} {x : RustM α} {v : α} :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ r = v ⌝ ⦄ ↔ x = .ok v := by
  cases x with
  | ret a => simp [Triple, WP.wp, PredTrans.apply]
  | vis i k => cases i; simp [Triple, WP.wp, PredTrans.apply]
  | div => simp [Triple, WP.wp, PredTrans.apply]

/-- If the program equals `.ok v`, then a triple is equivalent to its postcondition on `.ok v`. -/
theorem triple_iff_post_of_eq_ok {α : Type} {x : RustM α} {v : α} {P : α → Prop}
    (hx : x = .ok v) : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ ↔ P v := by
  subst hx
  simp [Triple, WP.wp, PredTrans.apply]

/-- A triple is equivalent to the existence of a value `a` such that the program is `.ok a`
and the postcondition holds on `a`. -/
theorem triple_iff_exists_ok {α : Type} {x : RustM α} {P : α → Prop} :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ ↔ ∃ a, x = .ok a ∧ P a := by
  cases x with
  | ret a => simp [Triple, WP.wp, PredTrans.apply]
  | vis i k => cases i; simp [Triple, WP.wp, PredTrans.apply]
  | div => simp [Triple, WP.wp, PredTrans.apply]

/-- Enrich triple's postcondition to contain a triple stating which program produced the value. -/
theorem triple_with_self {α : Type} {x : RustM α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ∧ ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r' => ⌜ r' = r ⌝ ⦄ ⌝ ⦄ := by
  obtain ⟨a, hx, hPa⟩ := triple_iff_exists_ok.1 h
  exact (triple_iff_post_of_eq_ok hx).2 ⟨hPa, triple_post_eq_iff_eq.2 hx⟩

/- Modus-ponens-like reasoning on a `noThrow` and a `mayThrow` triple -/
theorem triple_in_hypothesis {α : Type} {f : RustM α} {Q : α → Assertion RustM.postShape}
    (p : Prop)
    (h : ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓ r => Q r ⦄)
    (hp : ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓? r => Q r → ⌜ p ⌝ ⦄) :
    p := by
  cases f with
  | ret a => simp_all [Triple, WP.wp, PredTrans.apply]
  | vis i k => cases i; simp_all [Triple, WP.wp, PredTrans.apply]
  | div => simp_all [Triple, WP.wp, PredTrans.apply]

/-!
## Loops
-/

section
unseal RustM

/-- When divergence is allowed, `mvcgen`'s WP of a `RustM` program is admissible: the head of
a chain's supremum (a result or a failure) already occurs in the chain. -/
theorem wp_admissible_of_div {β : Type} (P : PostCond β RustM.postShape)
    (hdiv : PostCond.div P) :
    Lean.Order.admissible (fun r : RustM β => (wp⟦r⟧ P).down) := by
  intro c hc hAll
  generalize hEq : Lean.Order.CCPO.csup hc = t
  cases t with
  | ret v =>
    have h := hAll _ (ITree.csup_ret_mem hc hEq)
    rw [show (ITree.ret v : RustM β) = RustM.ok v from rfl] at h
    simpa [WP.wp, PredTrans.apply] using h
  | vis i k =>
    obtain ⟨k₀, hMem⟩ := ITree.csup_vis_mem hc hEq
    have h := hAll _ hMem
    rw [show (ITree.vis i k₀ : RustM β) = RustM.vis i k₀ from rfl] at h
    cases i
    simpa [WP.wp, PredTrans.apply] using h
  | div => simpa [WP.wp, PredTrans.apply] using hdiv

/-- `mvcgen` spec for the `loop` combinator.

Given a loop invariant `inv`, a well-founded relation `rel` and a termination measure, discharges
`loop body init` provided each iteration of `body` either finishes (`.done`) satisfying the
postcondition or continues (`.cont`) preserving the invariant while decreasing the measure. The
measure does not need to decrease if the postcondition allows divergence. -/
@[spec]
theorem loop_spec
  {α β γ : Type}
  {P : PostCond β RustM.postShape}
  {body : α → RustM (ControlFlow α β)} {init : α}
  (inv : α → Prop)
  (rel : γ → γ → Prop)
  (termination : α → γ)
  (hwf : WellFounded rel)
  (h_inv_init : inv init)
  (h_body : ∀ x, inv x → ⦃ ⌜ True ⌝ ⦄ body x ⦃ post⟨
    fun cf => match cf with
      | .cont r => ⌜ inv r ∧ (rel (termination r) (termination x) ∨ PostCond.div P) ⌝
      | .done r => PostCond.okAssertion P r,
    PostCond.failAssertion P, PostCond.otherAssertion P, PostCond.divAssertion P⟩ ⦄) :
  ⦃ ⌜ True ⌝ ⦄ loop body init ⦃ P ⦄ := by
  suffices h : ∀ x, inv x → (wp⟦loop body x⟧ P).down by
    unfold Triple
    intro _
    exact h init h_inv_init
  -- One iteration: the property holds for the unfolding of the loop if it holds for the
  -- continuations allowed by `h_body`.
  have step : ∀ (g : α → RustM β) x, inv x →
      (∀ r, inv r → (rel (termination r) (termination x) ∨ PostCond.div P) →
        (wp⟦g r⟧ P).down) →
      (wp⟦Std.bind (body x) (fun r => match r with
        | ControlFlow.cont x => g x
        | ControlFlow.done x => RustM.ok x)⟧ P).down := by
    intro g x hinv hg
    have hb := h_body x hinv trivial
    revert hb
    generalize body x = b
    cases b with
    | ret cf =>
      cases cf with
      | cont r =>
        simp only [WP.wp, PredTrans.apply, RustM.match.ok, bind_ok]
        exact fun ⟨hi, hr⟩ => hg r hi hr
      | done r => simp [WP.wp, PredTrans.apply]
    | vis i k => cases i; simp [WP.wp, PredTrans.apply]
    | div => simp [WP.wp, PredTrans.apply]
  by_cases hdiv : PostCond.div P
  case pos => -- Divergence permitted: fixpoint induction.
    have hadm : Lean.Order.admissible
        (fun g : α → RustM β => ∀ x, inv x → (wp⟦g x⟧ P).down) := by
      apply Lean.Order.admissible_pi
      intro x
      apply Lean.Order.admissible_pi
      intro _
      exact Lean.Order.admissible_apply (β := fun _ => RustM β)
        (fun _ (r : RustM β) => (wp⟦r⟧ P).down) x (wp_admissible_of_div P hdiv)
    exact loop.fixpoint_induct body _ hadm
      (fun g ih x hinv => step g x hinv (fun r hr _ => ih r hr))
  case neg => -- Divergence forbidden: well-founded induction on the termination measure.
    intro x hinv
    induction hg : termination x using hwf.induction generalizing x
    rename_i t IH
    rw [loop.eq_1]
    refine step _ x hinv (fun r hr hrel => ?_)
    rcases hrel with hrel | hd
    · subst hg
      exact IH (termination r) hrel r hr rfl
    · exact absurd hd hdiv

end

end Aeneas.Std

/-!
# Partial-correctness specifications
-/

namespace Aeneas.Std.WP

open Std RustM
open Std.Do

/-- Partial-correctness variant of `spec`.

`partialSpec x p_ok p_fail p_div` reads as: "if `x` reduces to `ok a` then `p_ok a` holds; if it
reduces to `fail e` then `p_fail e` holds; if it diverges then `p_div` holds". Unlike `spec`, it
does not assume the program terminates without exception. -/
@[expose]
def partialSpec {α} (x : RustM α)
    (p_ok : α → Prop) (p_fail : Error → Prop) (p_div : Prop) : Prop :=
  match x.match with
  | .ok a => p_ok a
  | .vis (.fail e) _ => p_fail e
  | .div => p_div

@[simp, grind =, agrind =]
theorem partialSpec_ok (a : α) (p_ok : α → Prop) p_fail p_div :
    partialSpec (ok a) p_ok p_fail p_div ↔ p_ok a := by
  simp [partialSpec]

@[simp, grind =, agrind =]
theorem partialSpec_fail (e : Error) p_ok p_fail p_div :
    partialSpec (α := α) (fail e) p_ok p_fail p_div ↔ p_fail e := by
  simp [partialSpec]

@[simp, grind =, agrind =]
theorem partialSpec_div (p_ok : α → Prop) p_fail p_div :
    partialSpec div p_ok p_fail p_div ↔ p_div := by
  simp [partialSpec]

/-- Derive a total-correctness `spec` from `partialSpec` by ruling out the failure and divergence
cases. Used by `@[step]` to generate a step-tactic lemma from a `partialSpec` theorem. -/
theorem spec_of_partialSpec
    {α} {x : RustM α} {p_ok : α → Prop} {p_fail : Error → Prop} {p_div : Prop}
    (h : partialSpec x p_ok p_fail p_div)
    (h_fail : ∀ e, ¬ p_fail e) (h_div : ¬ p_div) :
    spec x p_ok := by
  cases x with
  | ret a => simpa [partialSpec] using h
  | vis i k => cases i; simp [partialSpec] at h; exact absurd h (h_fail _)
  | div => simp [partialSpec] at h; exact absurd h h_div

/-- Lift an Aeneas partial-correctness spec to an mvcgen-compatible `Triple`. -/
theorem partialSpec_to_mvcgen {α : Type u} {x : RustM α}
    {p_ok : α → Prop} {p_fail : Error → Prop} {p_div : Prop}
    (h : partialSpec x p_ok p_fail p_div)
    {Q : PostCond α RustM.postShape}
    (h_ok   : ∀ r, p_ok r → PostCond.ok Q r)
    (h_fail : ∀ e, p_fail e → PostCond.fail Q e)
    (h_div  : p_div → PostCond.div Q) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ Q ⦄ := by
  cases x with
  | ret a => simp_all [partialSpec, Triple, WP.wp, PredTrans.apply]
  | vis i k => cases i; simp_all [partialSpec, Triple, WP.wp, PredTrans.apply]
  | div => simp_all [partialSpec, Triple, WP.wp, PredTrans.apply]

end Aeneas.Std.WP
