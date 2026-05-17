import AeneasCheck.LLBCSharp.Replay
import AeneasSoundness.LLBCSharpPaper.Program
import AeneasSoundness.Soundness.Concretise.Defn

/-!
# `Final` — function-exit predicate (paper Fig. 10 bridge)

Plan §5.1 E1 (M10.4a). The companion to `LLBCSharpPaper.Initial` /
`LLBCSharpPaper.BorrowChecks` that live in `Program.lean`. `Final`
sits in `Soundness/` rather than `LLBCSharpPaper/` because its
signature carries `AeneasCheck.LLBCSharp.SymState` — the replayer's
running state — and we keep the LLBCSharpPaper/ layer free of any
checker dependency beyond `AeneasCheck.Raw.*`. The bridging happens
here, via `Soundness.Concretise.concretise`.

The cert-format-and-soundness.md §4.3 statement of
`replayFun_sound` shapes `Final`'s role:

```
Final(Ω#_out, f.signature, trace.finalState)
```

i.e. `Final` pairs the paper-Ω at function exit with the replayer's
`SymState` (returned from `Replay.replayFun`). The pairing is

* a `concretise`-bridge: `concretise st = Ω` so per-event Phase E2
  / E3 lemmas can chain `stepEvent_sound` (which uses the same
  bridge predicate);
* the cert's exit-check post-condition (`leakedDirect.isEmpty` —
  `Replay.replayFun:99-102`) lifted into the paper's no-`.direct`-loan
  invariant; and
* a placeholder slot for the paper's "return local bound" condition
  (Phase E3 sharpens this once the cert convention for the return
  local is pinned).

## What Phase E3 will sharpen

Cert-format §4.5 calls out three permitted exit-leak kinds:
`.reborrow`, `.lazyExpand`, and `.shared`. Each must be tied to a
caller-visible region abstraction at function exit — Phase E3's
`replayFun_post` lemma proves this from the `CertGen_faithful`
promise (the OCaml interpreter wouldn't have emitted a leaked
non-direct loan whose abs isn't in `Ω.abs`).

`Final` at M10.4a only declares the predicate shape; the connection
to leaked-loan-abs membership is a Phase-E3 strengthening that adds
a fourth `Final` field. Per plan §3.4 (Phase-C-driven Phase-A
strengthening) the same one-field-at-a-time discipline applies here.

## Pairing with `Initial`

The two predicates compose for the eventual `replayFun_sound`:

```
∃ Ω_in Ω_out,
  Initial Ω_in lfd.signature cc.llbcProgram ∧
  Ω_in ⟶_#* Ω_out ∧
  Final Ω_out lfd.signature trace.finalState ∧
  BorrowChecks lfd.signature
```

Phase E2 builds the `⟶_#*` derivation; Phase E3 discharges
`Final`; Phase E4 (M10.4d) assembles.
-/

namespace AeneasSoundness.Soundness

open AeneasCheck.Raw (LlbcSignature LlbcProgram)
open AeneasCheck.LLBCSharp (SymState LoanInfo LoanKind)
open AeneasSoundness.LLBCSharpPaper (LLBCState)
open AeneasSoundness.Soundness.Concretise (concretise)

/-! ## `Final` -/

/-- Paper Fig. 10's `Final(Ω, sig, st)` — Ω is a final state for
    `sig`, paired with the replayer's `finalState` `st`.

    Four shape conditions, named explicitly so Phase E3
    (`replayFun_post`) can discharge them one at a time:

* `concretise_matches` — the bridging equality `concretise st = Ω`.
  Phase E2's induction maintains this invariant; E3 reads it off at
  exit.
* `no_direct_leak` — the cert's exit check
  (`Replay.replayFun:99-102`) lifted: no `.direct` loan is live at
  exit. The replayer's `leakedDirect.isEmpty = true` is exactly this
  fact at the `SymState` level.
* `return_populated` — the paper's "the return slot holds a value at
  function exit". Locked at `Ω.ctx 0 = some _` (Charon's convention:
  local 0 is the return slot; locals 1..sig.inputs.size are the
  inputs; the rest are body locals). Phase E3 sharpens the witness;
  at M10.4a we record only the existential.
* `non_direct_leaks_in_abs` — placeholder for the cert-format-and-
  soundness.md §4.5 "non-direct leaks are caller-visible" condition.
  Phase E3 connects each live `.reborrow` / `.shared` / `.lazyExpand`
  loan to its parent abstraction's `Ω.abs` entry; at M10.4a we
  leave the body as `True` so Phase E2 can ignore it while building
  the induction.
-/
structure Final
    (Ω : LLBCState) (sig : LlbcSignature) (st : SymState) : Prop where
  concretise_matches : concretise st = Ω
  no_direct_leak :
    ∀ (b : Nat) (li : LoanInfo),
      st.loans[b]? = some li → li.kind ≠ LoanKind.direct
  return_populated : ∃ v, Ω.ctx 0 = some v
  non_direct_leaks_in_abs : True
  -- Note: `sig` is currently unused in the body — the field
  -- placeholder is a hook for Phase E3's strengthenings (e.g.
  -- "the abs ids of permitted non-direct leaks lie in
  -- `signatureToInitialAbs sig`-derived caller abstractions").
  -- We thread it through the signature so the predicate's call
  -- sites match cert-format §4.3 verbatim and Phase E3 doesn't
  -- need to renumber arguments.
  _sig_placeholder : sig = sig := rfl

end AeneasSoundness.Soundness
