# Aeneas Verified Pipeline — Long-term Architecture

This document records the architectural vision for the Aeneas verified
pipeline: a Rust program is translated through a sequence of stages,
each of which we'd like to either (a) check the output of in Lean
rather than trust the implementation, or (b) prove correct in Lean.
The destination is a pure functional spec (Lean, Rocq, or F\*) whose
correspondence to the source Rust is guaranteed end-to-end by a chain
of Lean theorems plus a small, named trust base.

It is paired with `cert-format-and-soundness.md` (the cert format
reference) and `plans/llbc-sharp-soundness-plan.md` (the M10 campaign).

**Project scope (current):** the only step we are verifying in Lean
is **step 4 (the cert checker, M10)**. All other steps stay as
trusted OCaml or trusted Lean — we accept the existing implementation
and rely on testing for their correctness. The future-milestone
discussion below (§3, §6) is a *speculative roadmap* of where the
trust base *could* shrink if subsequent campaigns were undertaken,
not a committed plan. The reason for documenting it now is so that
M10's design decisions (where the soundness theorem lives, what its
quantifiers are, what state it speaks of) compose cleanly with any
later step we may want to verify, without re-architecture.

---

## 1. Pipeline overview

```
                                                  ┌── verified by ──┐
                          ┌──────────────────┐    ▼                 │
   Rust source            │  pre-pass        │   trusted (today)    │
       │                  │  LLBC → LLBC'    │   verified (M12)     │
       ▼                  └──────────────────┘                      │
   ┌────────┐   LLBC          ▲                                     │
   │ Charon │ ───────────► step 2                                   │
   └────────┘   (trusted)     │                                     │
   step 1                     ▼                                     │
                          ┌──────────────────┐   untrusted output:  │
                          │  symbolic interp │   cert.json          │
                          │  LLBC' → cert    │   (no proof needed   │
                          └──────────────────┘    on this step      │
                              step 3              because cert is   │
                                  │               checked next)     │
                                  ▼                                 │
                          ┌──────────────────┐                      │
                          │  cert checker    │   verified (M10) ────┘
                          │  cert → "valid   │
                          │   LLBC# trace"   │
                          └──────────────────┘
                              step 4
                                  │
                                  ▼
                          ┌──────────────────┐
                          │  translate to    │   verified (M11)
                          │  Pure IR         │
                          │  cert → PExpr    │
                          └──────────────────┘
                              step 5
                                  │
                                  ▼
                          ┌──────────────────┐
                          │  backend emit    │   verified per
                          │  PExpr → Lean    │   target (M13+)
                          │       /Rocq/F\*  │
                          └──────────────────┘
                              step 6
                                  │
                                  ▼
                          ┌──────────────────┐
                          │  external spec   │
                          │  in Lean/Rocq/F\*│
                          └──────────────────┘
```

Each step is implemented today and works end-to-end (the existing
89-fixture sweep is the integration test). The verified-pipeline
work doesn't change *what* the pipeline does — it migrates each
step's correctness from "tested" to "Lean-proved" and shrinks the
trust base accordingly.

---

## 2. Per-step status and target

### Step 1 — Charon (`Rust → LLBC`)

* **Today:** trusted. Charon is the Rust-to-LLBC frontend; ~tens of
  kLOC of Rust + `rustc` internals. Verifying it would require
  modelling enough of Rust's surface semantics to prove a translation
  relation — a research project on its own scale.
* **Long-term:** stays trusted. Charon is the trust root for the
  "Rust as written ↔ LLBC as analysed" correspondence. Realistic
  alternatives (Rust language standard ports, miri-derived semantics,
  etc.) are out of Aeneas's scope.

### Step 2 — Pre-passes (`LLBC → LLBC'`)

* **Today:** trusted. `src/PrePasses.ml` is 2,201 lines of OCaml
  applied unconditionally at `Main.ml:741-742`. Transformations include
  loop normalization, dead-code elimination, panic-site simplification,
  type-alias inlining, marker-trait filtering, and global-access
  rewriting. The output `llbc.json` is documented as "post-pre-pass"
  (`Main.ml:102`, `CertGen.ml:7`); the cert events refer to the
  post-pre-pass LLBC, not Charon's LLBC.
* **Speculative future (label: M12):** port `PrePasses.ml` to Lean
  and prove each pass is semantics-preserving for borrow-checking
  and forward-translation purposes. The size of this campaign is
  comparable to M10 (maybe larger — pre-passes operate on richer
  state than the symbolic interpreter does and there are 30+
  distinct passes). **Not on the current roadmap.** Documented
  here only to clarify what the M10 theorem does *not* cover.
* **Intermediate option (cheap):** ship an external CI check that
  re-runs `aeneas -emit-llbc-json` on Charon's LLBC and asserts the
  output is byte-equal across runs. Doesn't reduce the trust base;
  rules out *regressions* in `PrePasses.ml` between releases.

### Step 3 — Symbolic interpreter (`LLBC' → cert`)

* **Today:** OCaml symbolic interpreter (`src/interp/`) emits cert
  events via the M9.5 / M9.6 hooks. The interpreter is non-trivial
  (~10kLOC); however its output is **untrusted** — every claim the
  cert makes is verified by step 4.
* **Long-term:** this step is the natural place to *not* prove,
  because we don't have to. The cert-checker architecture means a
  buggy interpreter either produces a cert the checker rejects (no
  soundness violation) or a cert the checker accepts (then ∃ valid
  LLBC# derivation matching it, by the M10 soundness theorem —
  perhaps not the one OCaml meant, but a real one). The engineering
  cost of porting the interpreter to Lean would be high and the
  formal-guarantee dividend zero. Keep it in OCaml.
* **Caveat:** the engineering invariant that "the OCaml interpreter
  accepts approximately the same programs Rust does" is what makes
  the cert useful. That's caught by the differential test
  (`tests/lean-checker/differential/`), not by a theorem.

### How is the cert tied to *this* LLBC?

Before describing step 4, a sub-question: when the Lean checker
accepts a cert, the soundness theorem promises a valid LLBC#
derivation exists — but for *which* LLBC? Cert v3 (M9.7) made the
answer simple: **the cert *contains* the LLBC.**

1. **The cert embeds the post-pre-pass LLBC program** under
   `CrateCert.llbcProgram` (an `LlbcProgram` carrying type decls, fun
   decls with signatures + locals + body statements, and trait
   decls/impls). The OCaml side serializes the *post-`PrePasses.ml`*
   crate state — i.e. the same in-memory `crate` value the symbolic
   interpreter walked — into the cert at `-emit-cert` time. The Lean
   checker reads `llbcProgram` directly; there is no separate
   `<input>.llbc.json` file to consult.

2. **The (LLBC, cert) pair binding is structural, not hash-based.**
   In cert v1/v2 the binding was a hash digest (`cc_crate_hash`) over
   a separately-emitted `<input>.llbc.json` file; the Lean side was
   meant to MD5 the file and compare. That arrangement created two
   trust hazards: (a) the binding was honor-system because the Lean
   CLI silently dropped the `_llbcJson` argument (a known gap), and
   (b) the LLBC the cert was bound to was the post-pre-pass crate,
   which had to be dumped through a custom Aeneas serializer anyway.
   Cert v3 collapses both: the cert *is* the post-pre-pass LLBC plus
   the per-function execution trace. No second file, no hash to
   enforce.

3. **`cc.crateHash` is retained as an informational digest** of the
   source crate but no longer participates in the soundness binding.
   The Lean checker can use it for cache invalidation; the soundness
   theorem speaks of the LLBC implied by `llbcProgram`.

With the cert self-contained, the trust chain at step 4 reads:

* The OCaml pipeline (Charon + `PrePasses.ml` + interpreter + emitter)
  produces a single cert file whose `llbcProgram` is the post-pre-pass
  LLBC and whose `functions[i].events` is the execution trace for that
  LLBC. **Trusted** that the OCaml side faithfully embeds its own
  in-memory crate state into the JSON; the OCaml-side LLBC→JSON
  serializer lives in `src/cert/LlbcJson.ml` (689 LOC, mirrors the
  charon-ml `OfJson` deserializer's shape in reverse).
* The Lean checker reads `llbcProgram` and `functions` from the same
  cert file. There is no second file the user can fail to provide.
* The soundness theorem says: *for the LLBC encoded in
  `cc.llbcProgram`*, ∃ valid LLBC# derivation for each `FunCert.events`.

The binding chain becomes:

```
Charon's LLBC  ──[PrePasses.ml]──►  LLBC'  ──[Aeneas embeds in cert]──┐
   (trusted)                          ▲                                ▼
                                      │                  CrateCert {
                                      │                    llbcProgram = …LLBC'…,
                                      │                    functions   = …trace…
                                      │                  }
                                      └──── [trusted that PrePasses is
                                             semantics-preserving]
```

The user-facing trust is "PrePasses is semantics-preserving" plus
"Charon is correct"; everything from `-emit-cert` onward is a single
file the Lean checker reads atomically. The pre-v3 hash-check gap is
moot.

#### Historical note (pre-M9.7)

Before cert v3, `aeneas-check` took two paths: an LLBC file and a cert
file. The CLI silently ignored the LLBC bytes (`_llbcJson` with
underscore prefix in `Cli.lean`), so any binding was honor-system. The
intended fix was to MD5 the LLBC file and compare to a digest stored
in the cert. M9.7 (commits M9.7a → M9.7q) made the question moot by
moving the LLBC bytes *into* the cert.

### Step 4 — Cert checker (`cert → "valid LLBC# trace"`)

* **Today:** Lean checker (`aeneas-lean-checker/`). Replays each
  cert event against an executable mirror of the LLBC# symbolic
  state, fails fast on any inconsistency. M9.6 made every rule choice
  the OCaml interpreter implicitly made explicit in the cert
  (per-event hints), so the replayer's per-event check matches a
  single paper rule rather than guessing among several.
* **Long-term (M10 — this campaign):** prove in Lean that a
  successful `replayCrate` implies the existence of a valid LLBC#
  derivation for each function in the cert. Done condition: the
  theorem `replayCrate cc = .ok _ → ∃ valid LLBC# derivation per
  function` is stated and proved with no domain `axiom`s — only
  Lean core (`propext`, `Classical.choice`, `Quot.sound`).
* **Done condition reduces the trust base from "Lean checker code
  is correct" to "the paper-side `LStep` / `Valid` faithfully
  transcribe the paper's rules" — a modeling assumption, not an
  executable trust.**

### Step 5 — Translate (`cert → Pure IR`)

* **Today:** Lean implementation in
  `aeneas-lean-checker/AeneasCheck/Translate/`. Walks the cert's
  events and produces a `PExpr` (Pure IR) for each function:
  a value-flow lifting that strips borrows and lifetimes, leaving a
  pure functional expression that computes the same observable
  outputs as the original LLBC.
* **Speculative future (label: M11):** prove that the emitted
  `PExpr` is functionally equivalent to the LLBC source — the
  "forward simulation" theorem; paper's Theorem 3.4 covers this.
  **Not on the current roadmap.** Today this step is trusted Lean.

### Step 6 — Backend emit (`Pure IR → Lean / Rocq / F\*`)

* **Today:** Pretty-printers in `AeneasCheck/Backends/`. The Lean
  emitter targets `Aeneas.Std` (a runtime in `backends/lean/`); the
  Rust-model emitter exists as a differential-test artifact.
  Rocq and F\* are paper-level targets, not yet implemented in the
  Lean-checker tree.
* **Speculative future (label: M13+):** prove each emitter preserves
  observable semantics. The Lean target is the easiest because both
  source and target are Lean. Rocq and F\* are harder because they
  require modelling the target language's semantics. **Not on the
  current roadmap.**

---

## 3. Trust base evolution

Each row is the formal trust base after the named milestone lands
(plus Lean core; that row is universal and never goes away).

| After milestone | Formal TCB additions vs. previous | Engineering TCB |
|---|---|---|
| Lean core (always) | `propext`, `Classical.choice`, `Quot.sound` | Lean compiler + Mathlib version |
| **(today, pre-M10)** | + the Lean checker's code is correct (no proof yet) | + Charon, + `PrePasses.ml`, + symbolic interpreter, + Translate, + emit |
| **After M10 (this campaign)** | + Phase A's transcription faithfully captures paper rules (modeling assumption) | + Charon, + `PrePasses.ml`, + Translate, + emit. **Symbolic interpreter drops out** (its output is verified, so it itself isn't trusted.) |
| **After M11 (Translate soundness)** | + Phase A as before; nothing new | + Charon, + `PrePasses.ml`, + emit |
| **After M12 (PrePasses verified)** | + (none if pre-passes prove against Phase A's LLBC# semantics directly) | + Charon, + emit |
| **After M13 (per-backend emit)** | + the target language's semantic model | + Charon |
| **End state** | only Lean core + Phase A transcription + each backend's target semantics | only Charon |

The crucial observation: every milestone *replaces* an engineering
TCB entry with a formal one (and possibly a modeling assumption).
The total trust does not strictly shrink — porting `PrePasses.ml`
to Lean adds a modeling assumption that the Lean port matches the
intended semantics — but it moves trust from "this 2.2 kLOC of
OCaml is correct" (operational) to "we transcribed each pass's
intent faithfully" (auditable against the paper / against the
source). That's a meaningful reduction in surface area even when
the axiom count is similar.

---

## 4. Why the cert-checker architecture is load-bearing

The Aeneas design decision that step 3 emits an *untrusted certificate*
and step 4 *checks the certificate* is what makes the pipeline
tractable to verify. Two consequences:

1. **The symbolic interpreter is free.** We never have to prove
   anything about `src/interp/`. It's a generator of evidence; the
   evidence is verified. A buggy interpreter is caught by the checker
   or by the differential test, not by a theorem.

2. **The checker is small enough to verify.** A 4kLOC Lean replayer
   is portable to a soundness proof in roughly a year. A 10kLOC OCaml
   symbolic interpreter (which would have to be ported and proved if
   the cert architecture didn't exist) would be a multi-year campaign.

This is the standard *de Bruijn criterion*: trust only a small
checker, not a large producer. M10 makes the criterion formal for
step 4; M11 extends it to step 5; M12 puts step 2 inside the
verified perimeter.

---

## 5. M10 in this context

The M10 campaign (`plans/llbc-sharp-soundness-plan.md`) is precisely the
step-4 verification:

* **Input** to step 4: the cert (untrusted) + the LLBC' (post-pre-pass,
  also untrusted at this layer because step 4 verifies the cert
  against the LLBC').
* **Output** of step 4: a Lean theorem
  `replayCrate cc = .ok _ → ∃ valid LLBC# derivation for cc`.
* **Lean trust base after M10:** Lean core. *Domain axioms: none.*

What M10 explicitly does *not* cover:
* The LLBC' ↔ Charon's LLBC correspondence (step 2 — M12).
* The cert ↔ Pure IR translation (step 5 — M11).
* PL safety as an end-to-end claim. (Step 4's theorem can be
  *composed* with the paper's Thms 3.3 / 4.1 / 4.2 to derive PL
  safety; this composition is informal — we cite the paper rather
  than port its theorems.)

This is the "tight scope" the user requested: prove the soundness of
the cert-checker architecture, not redo the paper's metatheorems.

---

## 6. Open questions

* **Granularity of M12.** PrePasses.ml has ~30 distinct passes. Some
  are trivial (filter type aliases, refresh statement ids) and some
  are heavy (decompose global accesses, simplify panics). The campaign
  granularity should match: each pass gets its own
  semantics-preservation proof, and the order of porting is by
  pass-simplicity.
* **What to do with PL-safety claims.** Currently the user takes PL
  safety informally via paper citation. If a downstream auditor needs
  a Lean theorem for PL safety, we'd port Thms 3.3 / 4.1 / 4.2 (the
  "Phase G" of the original soundness plan, cut for M10). This is
  always available as a follow-on.
* **Charon trust.** The Charon project has its own roadmap; verifying
  it is not Aeneas's problem. But if Charon ships a separate trust
  reduction (e.g., a translation-validation pass that checks each
  LLBC against the Rust AST), we'd inherit it.
* **Pure IR semantics.** Step 5's correctness theorem requires a
  semantics for `PExpr` (the Pure IR). The current Lean checker
  defines `PExpr` syntactically; an executable interpreter / denotation
  is needed for M11. The natural choice is a deep embedding in Lean
  proper (Lean's expr datatype is already pure functional), but the
  details are a separate design question.

---

## 7. Document anchors

* M10 campaign plan: `documentation/plans/llbc-sharp-soundness-plan.md`
* Cert format reference: `documentation/cert-format-and-soundness.md`
* The current pre-pass code (engineering TCB entry): `src/PrePasses.ml`
* The current symbolic interpreter (no longer trusted post-M10):
  `src/interp/`
* The current cert checker (M10 target): `aeneas-lean-checker/`
* The translation step (M11 target):
  `aeneas-lean-checker/AeneasCheck/Translate/`
* Backend emitters (M13+ targets):
  `aeneas-lean-checker/AeneasCheck/Backends/`
