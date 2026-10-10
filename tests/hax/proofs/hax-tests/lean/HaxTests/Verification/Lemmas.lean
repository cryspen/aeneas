-- Lemmas for the proofs of `ProofObligations.lean`, and `@[spec]`
-- registrations of core-models definitions.
import Aeneas
import CoreModels
import HaxTests.Verification.MissingCore
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option mvcgen.warning false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

/- You can remove the following line by using the CLI option `-all-computable`: -/
noncomputable section


/-- Inversion of a precondition that starts with a monadic call: if
`(m >>= f).holds`, then `m` returns some `a` (no panic/divergence) and `(f a).holds`. -/
theorem Aeneas.Std.RustM.holds_bind {α : Type} {m : RustM α} {f : α → RustM Prop}
    (h : (m >>= f).holds) : ∃ a, m = ok a ∧ (f a).holds := by
  cases m
  · simp [Bind.bind, Std.bind, Triple, WP.wp, PredTrans.apply] at h ⊢
    exact h
  · simp [Bind.bind, Std.bind, Triple, WP.wp, PredTrans.apply] at h
  · simp [Bind.bind, Std.bind, Triple, WP.wp, PredTrans.apply] at h

/-- `holds_bind` as an equivalence, for `simp`: a precondition starting with a
monadic call (e.g. a trait method, which has no `@[spec]`) becomes a plain
hypothesis about the call's result. -/
theorem Aeneas.Std.RustM.holds_bind_iff {α : Type} {m : RustM α} {f : α → RustM Prop} :
    (m >>= f).holds ↔ ∃ a, m = ok a ∧ (f a).holds := by
  constructor
  · exact RustM.holds_bind
  · rintro ⟨_, rfl, _⟩
    simpa

open Lean Elab Command in
/-- `register_closure_specs ns` marks `@[spec]` the `call`/`call_mut`/`call_once`
methods of every closure extracted under the namespace `ns`, so that `hax_mvcgen`
can go through closures (e.g. those of `hax_lib::forall`/`exists` in conditions).
Their names are numbered by aeneas (`__18.requires.closure.Insts.….call`) and change
when items are added, hence the registration by shape rather than by name.
Fails if there is no such method, so that a change of naming is noticed. -/
elab "register_closure_specs " ns:ident : command => do
  let methods := [`call, `call_mut, `call_once]
  let closures := (← getEnv).constants.fold (init := #[]) fun acc n _ =>
    if ns.getId.isPrefixOf n && methods.contains (.mkSimple n.getString!) &&
        n.components.contains `closure && n.components.contains `Insts then
      acc.push n
    else acc
  if closures.isEmpty then
    throwError "register_closure_specs: no closure method found under `{ns.getId}`"
  for n in closures do
    elabCommand (← `(attribute [spec] $(mkIdent n)))
