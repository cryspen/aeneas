# Certificate-based Pipeline

The Aeneas Lean checker takes a *certificate* — a JSON trace produced by
the OCaml symbolic interpreter — and replays it against an executable
mirror of the LLBC# operational semantics. A successful replay yields a
paper-side multi-step derivation matching the cert's events. The
proof is mechanised in Lean 4 against the operational semantics of
the LLBC# paper (Ho, Fromherz, Protzenko 2024 — see §3).

The pipeline produces a clean Lean term as a side-effect. The cert
is structurally fragile by construction (any inconsistency aborts the
replay), so the cert checker shoulders the trust that an unverified
LLBC-to-Lean translator would otherwise hold.

---

## 1. Architecture

```
   ┌──────────┐  Charon  ┌──────────────┐  cert.json  ┌──────────────────────┐
   │  Rust.rs │ ──────▶  │ aeneas       │ ──────────▶ │ aeneas-lean-checker  │
   └──────────┘          │ -emit-cert   │             │ parse → tc → replay  │
                         │ (OCaml)      │             │   → translate → emit │
                         └──────────────┘             └──────────────────────┘
                                                               │
                                                               ▼
                                                       Pure Lean .lean
```

Two Lean packages plus the OCaml emitter:

| Component | Path | Role |
|---|---|---|
| Cert emitter | `src/cert/` (OCaml) | Records the LLBC# symbolic interpreter's trace as JSON. |
| Checker | `aeneas-lean-checker/` | Parses + typechecks the cert, replays it against `SymState`, translates to pure Lean, emits a `.lean` file. Lean-core only (no Mathlib). |
| Soundness | `aeneas-lean-soundness/` | The mechanised correspondence theorem; depends on Mathlib. |

The checker has five sub-libraries:

* `AeneasCheck.Raw` — cert AST (events, places, types). Schema lives in `AeneasCheck/Raw/CertEvent.lean`.
* `AeneasCheck.Typecheck` — structural well-formedness over the cert.
* `AeneasCheck.LLBCSharp` — `SymState` + `stepEvent` (the executable mirror of LLBC#).
* `AeneasCheck.Translate` / `AeneasCheck.Pure` — cert → pure Lean function lift.
* `AeneasCheck.Backends` — Lean / Rust pretty-printers.

The soundness package mirrors the checker on the paper side
(`AeneasSoundness.LLBCSharpPaper`) and proves the per-event,
per-function, and per-crate correspondence theorems
(`AeneasSoundness.Soundness`).

---

## 2. What's proven

Three theorems, all proven from `[propext, Classical.choice, Quot.sound]`
(verifiable with `#print axioms`):

### `stepEvent_sound` — per event

```lean
theorem stepEvent_sound :
    ∀ (ev : Event) (st st' : SymState) (Ω : LLBCState),
      concretise st = Ω →
      LoanHwmInvariant st →
      stepEvent st ev = .ok st' →
      ∃ Ω', Valid ev Ω ∧ LStep Ω ev Ω' ∧ concretise st' = Ω'
```

Every event the checker accepts corresponds to one paper-side `LStep`
derivation. `concretise` is the lift from `SymState` to the paper's
`LLBCState`; `Valid` flattens the rule premises; `LStep` is the
27-constructor operational semantics from paper Fig. 3 / 7 / 8 / 11 /
§5.2.

### `replayFun_correspondence` — per function

```lean
theorem replayFun_correspondence
    (n : Nat) (f : FunCert) (strictJoin : Bool) (trace : CheckedTrace)
    (hReplay : replayFun n f strictJoin = .ok trace) :
    LStepStar (concretise (SymState.empty n)) trace.events.toList
              (concretise trace.finalState) ∧
    (∀ b li, trace.finalState.loans[b]? = some li → li.kind ≠ .direct)
```

A trace-level multi-step derivation visiting each cert event in order,
plus the exit invariant: no `.direct` loan is live at function exit.

### `replayCrate_correspondence` — per crate

```lean
theorem replayCrate_correspondence
    (cc : CrateCert) (strictJoin : Bool) (results : Array CheckedTrace)
    (hReplay : replayCrate cc strictJoin = .ok results) :
    results.size = cc.functions.size ∧
    ∀ i (hi : i < cc.functions.size), ∃ (hir : i < results.size),
      LStepStar
        (concretise (SymState.empty (inferNumLocals cc.functions[i].events)))
        results[i].events.toList
        (concretise results[i].finalState) ∧
      (∀ b li, results[i].finalState.loans[b]? = some li → li.kind ≠ .direct)
```

Per-index correspondence across the crate.

### What this does *not* claim

* **Cert ⇔ source Rust faithfulness.** The OCaml emitter is the trust
  point: if it drops events, the cert is an incomplete picture, and the
  derivation matches the incomplete cert rather than the actual
  execution. Catching emitter bugs is the job of the differential
  harness (see `differential-testing-plan.md`).
* **PL-level borrow safety.** That is the paper's safety theorem
  (Theorem 4.x); we do not axiomatise it here. A downstream consumer
  who wants the safety claim composes our correspondence with the
  paper theorem by hand.

---

## 3. Paper

Aymeric Fromherz, Son Ho, Jonathan Protzenko. *Sound Borrow-Checking
for Rust via Symbolic Semantics (Long Version)*.
[arXiv:2404.02680v2](https://arxiv.org/abs/2404.02680), 2024.

Section numbers in `AeneasSoundness.LLBCSharpPaper/Step.lean`
docstrings refer to this version. The paper's LLBC# ⇒ LLBC ⇒ PL
hierarchy of Fig. 1 corresponds to the Lean module layout:

| Paper | Lean module |
|---|---|
| LLBC# operational semantics (Fig. 3 / 7 / 8 / 11 / §5.2) | `AeneasSoundness.LLBCSharpPaper.Step` (`LStep`) |
| `Ω#` state (Fig. 2) | `AeneasSoundness.LLBCSharpPaper.State` (`LLBCState`) |
| Function-entry / exit invariants (Fig. 10) | `AeneasSoundness.LLBCSharpPaper.Program` (`Initial`, `BorrowChecks`) + `Soundness.InitialFinal` (`Final`) |
| Theorems 3.1, 3.3, 4.1, 4.2 (Appendix A/B) | *Not mechanised.* The Lean library stops at the LLBC# correspondence. |

---

## 4. Running the toolchain

### Build

```bash
# OCaml side (Aeneas + Charon, see root README.md for prerequisites)
make bin/aeneas

# Lean checker (Lean-core only, ~1s warm)
cd aeneas-lean-checker && lake build

# Soundness proof (Mathlib, ~1s warm)
cd aeneas-lean-soundness && lake build
```

### Vertical-slice gate (G1)

End-to-end Rust → cert → Lean → Rust model → cargo test:

```bash
bash scripts/check-vertical-slice.sh
```

### Other gates

* **G2** — Direct (hand-written) Lean checker tests:
  `cd aeneas-lean-checker && for f in tests/Direct/*.lean; do lake env lean "$f"; done`
* **G3** — Generated-Lean smoke tests:
  `cd aeneas-lean-checker && lake build GeneratedTests`
* **G4** — 89-fixture sweep:
  ```bash
  for f in tests/llbc/*.cert.json; do
    aeneas-lean-checker/.lake/build/bin/aeneas-check "$f" > /dev/null || echo "FAIL: $f"
  done
  ```
* **G5** — Axiom-hygiene check (TCB must remain `[propext, Classical.choice, Quot.sound]`):
  ```bash
  cd aeneas-lean-soundness
  lake env lean tests/AxiomCheck.lean | diff - tests/axioms.golden.txt
  ```
* **G6** — No-sorry under `Soundness/`:
  `grep -rn "^\s*sorry\b" aeneas-lean-soundness/AeneasSoundness/Soundness/`
* **G7** — Warm `lake build` budget: <2s for either package.

### Generating a cert for a new Rust source

```bash
# 1. Rust → LLBC
charon rustc --preset=aeneas --dest-file=my.llbc -- src/my.rs --crate-type=lib

# 2. LLBC → cert.json (current cert format is v6)
bin/aeneas -emit-cert my.llbc

# 3. cert.json → Lean (replay + emit)
aeneas-lean-checker/.lake/build/bin/aeneas-check my.cert.json --out My.lean
```

---

## 5. Trust base

What's trusted to use the correspondence theorem:

1. **Lean kernel** — `propext`, `Classical.choice`, `Quot.sound`.
2. **The OCaml cert emitter** (`src/cert/`) — emits a faithful trace
   of the LLBC# symbolic interpreter. Cross-checked by the
   differential harness, not formally proven.
3. **Charon** — Rust → LLBC translation.

What is *not* trusted: the cert content (replay validates it), the
Lean checker logic (its outputs are witnessed by the proof), or any
paper-level meta-theorem (none are axiomatised in this library).
