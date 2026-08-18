module
public import Aeneas.Std.Primitives
public meta import Aeneas.Tactic.Step.Init
public meta import Aeneas.Tactic.Conv.Bvify.Init
public section

namespace Aeneas.Std

open RustM WP

@[step]
theorem massert_spec (b : Prop) [Decidable b] :
    partialSpec (massert b)
      (fun _ => b)
      (fun | .assertionFailure => ¬ b | _ => False)
      False := by
  unfold massert
  split <;> simp_all [partialSpec]

@[simp, step_pre_simps, bvify]
theorem massert_ok (b : Prop) [Decidable b] : massert b = ok () ↔ b := by
  grind [massert, fail_not_ok]

@[simp, step_pre_simps, bvify]
theorem spec_massert (b : Prop) [Decidable b] : Std.WP.spec (massert b) P ↔ (b ∧ P ()) := by
  simp [massert]
  split <;> simp <;> grind

@[simp, global_simps] theorem massert_True : massert True = ok () := by simp [massert]
@[simp, global_simps] theorem massert_False : massert False = fail .assertionFailure := by simp [massert]

end Aeneas.Std
