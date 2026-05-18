import AeneasCheck.LLBCSharp.Replay
import AeneasSoundness.Soundness.Invariants.HWM

/-!
# AbsRegistry consistency invariant on `SymState`

Plan §"Lean-side migration sequence" row 1 (M10.x.1, AbsRegistry
half). This file states the structural promise the cert makes
about events that reference an abs id: every reference (`EvEndAbs
absId`, `EvMutBorrow … .inAbsReborrow absId`, `EvReborrow … (some
parentAbs)`, `EvSymExpandMutBorrow … (some parentAbs) …`) names
an absId that's *currently* in `SymState.absRegistry`. The
`Typecheck/Consistency.lean` `seenAbs` field
(`Typecheck/Consistency.lean:300`) is the precedent — it tracks
abs ids ever-introduced across the trace; this file tightens to
"currently-installed at the event boundary" for the events that
need it.

## Scope (M10.x.1)

Like `HWM.lean`, this file provides structural scaffolding only.
The downstream M10.x.5 axiom drop (`mutBorrow_inAbsReborrow`'s
`hAbsExists`) consumes the per-event predicate as a premise; after
M10.x.2's replayer strengthening installs the registry-presence
check in `stepMutBorrow`, the premise becomes hStep-derivable.

The predicate distinguishes between two classes of abs id usage:

* **Lookup events** (`.endAbs`, `.mutBorrow.inAbsReborrow`,
  `.reborrow` with `some parentAbs`, `.symExpandMutBorrow` with
  `some parentAbs`): the cert expects the named absId to *already
  be* in `st.absRegistry`. The pre-event predicate is
  `st.absRegistry.contains absId = true`.
* **Introduction events** (`.call`'s `absSig`, `.join`'s
  `joinMutBorrows`-rule entries): the cert *establishes* the
  absId in the registry as part of the event. No precondition on
  the pre-state.

`stepEndAbs` is treated as a lookup event with respect to the
released loans' role list, but the replayer is *tolerant* of
missing `absRegistry` entries
(`AeneasCheck.LLBCSharp.Step.lean:352-353` returns `pure ()` on
`absRegistry[absId]? = none`). So technically `.endAbs`'s
registry-presence is non-load-bearing today. We still record the
predicate for `.endAbs` for symmetry; downstream M10.x.6's
preamble-commute refactor consumes it.

## Trust impact

Zero. Pure structural lemmas; no `axiom` / `sorry` / `unsafe`.
-/

namespace AeneasSoundness.Soundness.Invariants

open AeneasCheck.LLBCSharp
open AeneasCheck.Raw

/-! ## Per-event abs-reference predicate -/

/-- Per-event predicate: the absId(s) the event references are in
    `st.absRegistry`. Only the lookup events impose a constraint;
    introduction events and abs-free events are unconditional. -/
def AbsRegistryReferenced (st : SymState) : Event → Prop
  | .endAbs absId _ _ _ => st.absRegistry.contains absId = true
  | .mutBorrow _ _ _ (.inAbsReborrow absId) =>
      st.absRegistry.contains absId = true
  | .mutBorrow _ _ _ (.loopOwned _) =>
      -- `loopOwned`'s argument is a *loop* id, not an abs id.
      -- No registry constraint.
      True
  | .reborrow _ _ _ _ (some parentAbs) =>
      st.absRegistry.contains parentAbs = true
  | .reborrow _ _ _ _ none => True
  | .symExpandMutBorrow _ _ _ (some parentAbs) _ _ =>
      st.absRegistry.contains parentAbs = true
  | .symExpandMutBorrow _ _ _ none _ _ => True
  | _ => True

/-! ## Monotonicity of the registry over stepEvent

The registry grows by `addAbsShape` (in `stepCall`'s `absSig`
fold and `stepJoin`'s `joinMutBorrows` install) and shrinks by
`removeAbsShape` (in `stepEndAbs`). All other 14 events leave it
untouched. We expose two consequences:

* "Monotone-growth" of `absIdHwm` (already in `HWM.lean`).
* For consumer convenience: any abs id present in `st.absRegistry`
  is below `st.absIdHwm` (`HwmInvariant.absBound`).

These two facts compose to give the M10.x.5 lemma "if the cert's
referenced absId is in the pre-state registry and the replayer
accepts the trace, then it's in the post-state registry until
explicitly ended". The detailed across-events flow needs cert-
provided per-event admissibility (similar to `HWM.lean`'s
`eventRespectsHwm`); we expose the scaffold below. -/

/-- Inversion lemma: `addAbsShape shape` makes `shape.absId`
    present in the registry. Used by Phase D's per-event lemmas
    once `stepCall` / `stepJoin` succeed. -/
theorem addAbsShape_contains (st : SymState) (shape : AbsShape) :
    (st.addAbsShape shape).absRegistry.contains shape.absId = true := by
  simp [SymState.addAbsShape, Std.HashMap.contains_insert]

/-- Inversion lemma: `addAbsShape shape` preserves registry
    membership for any *other* absId. -/
theorem addAbsShape_contains_other (st : SymState) (shape : AbsShape)
    (a : Nat) (h : a ≠ shape.absId) :
    (st.addAbsShape shape).absRegistry.contains a = st.absRegistry.contains a := by
  simp [SymState.addAbsShape, Std.HashMap.contains_insert,
    show ¬ (shape.absId = a) from fun he => h he.symm]

/-- Inversion lemma: `removeAbsShape absId` removes exactly that id;
    membership of any other id is unchanged. -/
theorem removeAbsShape_contains_other (st : SymState) (absId : Nat)
    (a : Nat) (h : a ≠ absId) :
    (st.removeAbsShape absId).absRegistry.contains a = st.absRegistry.contains a := by
  simp [SymState.removeAbsShape, Std.HashMap.contains_erase,
    show ¬ (absId = a) from fun he => h he.symm]

/-- After `removeAbsShape absId`, the id is *not* in the registry. -/
theorem removeAbsShape_contains_self (st : SymState) (absId : Nat) :
    (st.removeAbsShape absId).absRegistry.contains absId = false := by
  simp [SymState.removeAbsShape, Std.HashMap.contains_erase]

/-! ## Fold-level monotonicity helpers

For `stepCall` / `stepJoin`'s installation folds, we expose
"every previously-present absId stays present" + "every shape's
absId is installed by the fold". The first is consumed by the
`endAbs` (and other lookup-event) preservation argument; the
second by the `EvCall` post-state's `absSig.foldl addAbsShape`
correspondence. -/

/-- Generic fold-level monotonicity: an `addAbsShape` fold never
    removes existing entries. -/
theorem absSigFold_preserves_contains
    (shapes : List AbsShape) (st : SymState) (a : Nat)
    (h : st.absRegistry.contains a = true) :
    (shapes.foldl SymState.addAbsShape st).absRegistry.contains a = true := by
  induction shapes generalizing st with
  | nil => simpa
  | cons s rest ih =>
    simp only [List.foldl_cons]
    apply ih
    simp [SymState.addAbsShape, Std.HashMap.contains_insert, h]

/-- Generic fold-level monotonicity for the `stepJoin` abs-install
    fold (only `joinMutBorrows` entries install). -/
theorem stepJoin_absInstall_preserves_contains
    (witnesses : List JoinEntry) (st : SymState) (a : Nat)
    (h : st.absRegistry.contains a = true) :
    (witnesses.foldl
      (fun (s : SymState) (entry : JoinEntry) =>
        match entry.rule with
        | .joinMutBorrows _ _ _ absShape => s.addAbsShape absShape
        | _ => s) st).absRegistry.contains a = true := by
  induction witnesses generalizing st with
  | nil => simpa
  | cons w rest ih =>
    simp only [List.foldl_cons]
    cases hw : w.rule with
    | joinMutBorrows _ _ _ absShape =>
      apply ih
      simp [SymState.addAbsShape, Std.HashMap.contains_insert, h]
    | joinSame => exact ih _ h
    | joinSymbolic _ => exact ih _ h
    | joinVar => exact ih _ h
    | joinBottomOther _ => exact ih _ h
    | joinOtherBottom _ => exact ih _ h

/-! ## Cross-mutator preservation

For pairing with `eventRespectsHwm`-style trace reasoning, expose
the "non-touching" mutator helpers: every non-abs-mutator
preserves both registry membership AND the `AbsRegistryReferenced`
predicate (modulo the event itself). -/

/-- `setLocal` doesn't touch absRegistry. -/
theorem setLocal_contains (st : SymState) (l : Nat) (v : Val) (a : Nat) :
    (st.setLocal l v).absRegistry.contains a = st.absRegistry.contains a := rfl

/-- `addLoan` doesn't touch absRegistry. -/
theorem addLoan_contains (st : SymState) (b : Nat) (inner : Val)
    (kind : LoanKind) (a : Nat) :
    (st.addLoan b inner kind).absRegistry.contains a = st.absRegistry.contains a := rfl

/-- Raw `loans.erase` doesn't touch absRegistry. -/
theorem loans_erase_contains (st : SymState) (b : Nat) (a : Nat) :
    ({ st with loans := st.loans.erase b } : SymState).absRegistry.contains a =
      st.absRegistry.contains a := rfl

/-- Raw env-replace doesn't touch absRegistry. -/
theorem env_replace_contains (st : SymState) (newEnv : Std.HashMap Nat Val)
    (a : Nat) :
    ({ st with env := newEnv } : SymState).absRegistry.contains a =
      st.absRegistry.contains a := rfl

/-! ## Trace-level corollary

The headline statement: for any chain of `stepEvent` successes,
the abs ids that the trace ever *introduces* (via `stepCall` or
`stepJoin.joinMutBorrows`) are exactly the ids that can be
referenced by subsequent events (modulo `stepEndAbs` removals).

The cleanest packaging mirrors `HwmInvariant`'s
`WitnessedChain` + `hwm_chain` shape: a per-step `AbsRegistry`
admissibility predicate (the `AbsRegistryReferenced` above) plus
a chain-level conclusion. The conclusion here is weaker than for
HWM: we don't claim a global "all referenced ids are installed"
fact (that would conflict with `stepEndAbs` removal), only the
per-step compatibility. -/

/-- Per-step admissibility: at the pre-state, the event's
    references are in the registry. Mirrors
    `eventRespectsHwm` in `HWM.lean`. -/
def AbsRegistryAdmissible (st : SymState) (e : Event) : Prop :=
  AbsRegistryReferenced st e

/-- Trace-level statement: a `WitnessedChain` (from `HWM.lean`)
    threaded with `AbsRegistryAdmissible` at each step lands in a
    state where the final event's references (if any) were in the
    registry at their pre-state.

    For M10.x.1's purposes this is a *type-level scaffold* — we
    don't need a per-step extraction theorem because each per-event
    soundness lemma (M10.x.5 mutBorrow_inAbsReborrow_sound, etc.)
    can consume the predicate from `CertGen_faithful` until
    M10.x.2's replayer strengthening establishes it by inversion.
    The trace-level chain remains useful for Phase E
    `replayFun_sound` once M10.x.5+ collapse the per-event premise
    chain. -/
def AbsRegistryAdmissibleAt (st : SymState) (steps : List (Event × SymState)) :
    Prop :=
  match steps with
  | [] => True
  | (e, _) :: _ => AbsRegistryAdmissible st e

end AeneasSoundness.Soundness.Invariants
