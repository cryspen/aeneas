import AeneasSoundness.Soundness.StepEventSound

/-!
G5 gate fixture: prints the axiom set every M10 soundness-side theorem
depends on. CI diffs the output against `tests/axioms.golden.txt`; a
divergence is a regression.

The expected axiom list shrinks as phases close:
* Phase A (now): `LLBCState`, `concretise`, `Valid`, `LStep`, the
  per-event lemma axioms, and `stepEvent_sound` itself.
* Phase A end (M10.0k): the four paper-side axioms get replaced with
  real types; per-event lemmas become `sorry`'d theorems (`sorryAx`).
* Phase C end: per-event lemmas are real; `stepEvent_sound` still
  `sorry`'d (Phase D closes it).
* Phase D end (M10.3a, *now*): `stepEvent_sound` is a theorem; the
  trusted base is Lean core + the `CertGen_faithful` per-event
  family.
* Phase F (M10 done): `replayCrate_implies_borrow_checks` carries
  `CertGen_faithful` + the four `paper_thm_*` placeholders.
* Phase G (optional, post-M10): the four `paper_thm_*` axioms are
  replaced with real proofs; trusted base reduces to `CertGen_faithful`
  plus Lean core.

Plan §10.2 has the per-phase expected output.
-/

#print axioms AeneasSoundness.Soundness.stepEvent_sound

-- Phase E adds: `#print axioms AeneasSoundness.Soundness.replayFun_sound`
-- Phase F adds: `#print axioms AeneasSoundness.Soundness.replayCrate_implies_borrow_checks`
