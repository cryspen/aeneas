# LLBC# Soundness Campaign — Implementation Plan

> **Cert v3 revision (2026-05-17).** This plan was written pre-M9.7 (cert v2). It has been revised to reflect the cert v3 (M9.7) self-contained-cert redesign: cert files now embed the post-pre-pass LLBC under `cc.llbcProgram` and no longer reference an external `<input>.llbc.json` file. The campaign's top-level theorem quantifies over a single `cc : CrateCert`, signatures come from the matched `LlbcFunDecl` via a new `LLBCSharpPaper/Program.lean` helper module, and the broadened `CertGen_faithful` axiom (§0.3) covers both the trace and the embedded LLBC subtree. Key cross-references: §0.3 (quantifier-domain note), §0.4 (cert-v3 boundaries), §1.1 (new `Program.lean`), §5 (Phase E theorem signature), §6 (Phase F theorem + `lookupFunDecl_total` preamble).

## Executive Summary

This plan stages the soundness proof of the Aeneas Lean checker — closing the four `axiom`s in `aeneas-lean-checker/AeneasCheck/Theorems/StepEventSound.lean` into a fully Lean-mechanized statement that *`replayCrate` accepting a cert implies the existence of a valid LLBC# derivation*, and by composition with the paper's theorems, PL-level safety. It is the natural follow-on to the M9.6 (Option C) cert-format redesign and the M9.7 (cert v3) self-contained-cert redesign (together: 41 commits, branch `aeneas-lean-certificate`): M9.6 made every replayer-side rule choice deterministic; M9.7 made the cert a single self-contained file that carries the post-pre-pass LLBC inside it; this campaign supplies the paper-side surface (`LLBCState`, `concretise`, `LStep`, `Valid`) those hints will be matched against.

The campaign is split into **eight phases (M10.0 — M10.7)**, in dependency order, with one Lean module landing per phase. Each phase has a vertical-slice gate (a representative event becomes fully proved end-to-end) before the campaign advances to the next paper rule. Total estimated effort: **~70–110 working days** single-developer focus (i.e., a multi-month campaign), heavily front-loaded on Phase A (paper-side surface; ~20 d) and Phase C (per-event lemmas; ~25–35 d). The bulk of work parallelises along per-event boundaries (Phase C), with Phases A, D, E, F, G largely serial.

The campaign is **trusted-base-bounded**: we assume the OCaml `CertGen.ml` faithfully shadows the LLBC# interpreter (i.e., a `CrateCert` is only ever produced from a real interpreter trace), and we trust the paper's Appendix A/B proofs of Theorems 3.1, 3.3, 4.1, 4.2 when porting them. Everything else is proved.

**Scope boundary (firm):** This campaign covers the *direct-borrow subset* + the M9.6 hint surface. `EvProj` is excluded (rejected by the replayer; M11+ work, requires sub-borrow structure in `Val`). The value-grammar coarse abstractions (`M9.5d`, `M9.5f`, `M9.5p` — variant/tuple/record collapse to `.sym`) remain — the proof keeps them as part of `concretise`'s lossy projection and *does not* prove value-equality through them, only borrow-graph well-formedness.

**Build-time strategy:** `aeneas-lean-checker` stays mathlib-free; all Mathlib-dependent code lives in a new sister package `aeneas-lean-soundness/` (Lake workspace member) so checker CI keeps its ~1s build. Soundness CI is a separate, slower lane (~30 min cold) gated on its own.

---

## 0. Scope decisions (call-outs)

### 0.1 Mathlib dependency — Yes, sandboxed

The current `aeneas-lean-checker` is deliberately mathlib-free (lakefile.lean comment §M4-M6: "this lib only depends on Lean core (for Lean.Json)"). The soundness proof, by contrast, needs:

- `Mathlib.Tactic.Lemma`, `Mathlib.Tactic.Cases`, etc., for inductive-relation pattern matching;
- `Mathlib.Data.Finset.*` and `Mathlib.Data.Multiset.*` for borrow-graph well-formedness predicates;
- `Mathlib.Tactic.FinCases` for case-analysis on small enumerations (`MutBorrowKind`, `JoinRule`);
- Quantifier-instantiation tooling (`grind`, `aesop`) for the per-rule lemma proofs.

**Recommended structure:**

```
aeneas-lean-checker/             # Stays mathlib-free. The replayer + translator.
aeneas-lean-soundness/           # NEW. The paper-side surface + soundness proof.
  AeneasSoundness/
    LLBCSharpPaper/              # Phase A — the formal LLBC# semantics
      Syntax.lean                # value grammar, region abstractions
      State.lean                 # Ω# states
      Step.lean                  # ⟶_# reduction rules (Figs 3/7/8/9/11)
      WellFormed.lean            # borrow-graph predicates
    Concretise/                  # Phase B
      Defn.lean                  # ⟦·⟧ : SymState → LLBCState
      WellFormed.lean
    Soundness/                   # Phases C, D, E, F
      StepEventSound.lean        # the four-axiom file lands here, fully proved
      ReplayFunSound.lean        # induction over events
      ReplayCrateSound.lean      # crate-level corollary
      Theorems/                  # Phase G — paper-theorem ports
        Thm31_Confluence.lean
        Thm33_LLBCSharpRefines.lean
        Thm41_BorrowChecksSafe.lean
        Thm42_PLSafety.lean
      CertImpliesSafety.lean     # end-to-end corollary
```

`aeneas-lean-soundness` becomes a Lake workspace dependency on `aeneas-lean-checker` (the soundness side *re-imports* `AeneasCheck.LLBCSharp.{State,Step,Replay}` and `AeneasCheck.Raw.CertEvent` to reason about them). It does **not** affect the checker's build; CI runs the two lanes independently.

The Theorems/ directory at `aeneas-lean-checker/AeneasCheck/Theorems/StepEventSound.lean` is *moved* in Phase A's first commit into `aeneas-lean-soundness/AeneasSoundness/Soundness/StepEventSound.lean`. The original file is replaced by a one-line `import` of the soundness-side file plus a re-export so existing fixtures don't break.

### 0.2 LLBC vs. LLBC# — Port LLBC# first, LLBC as needed

The paper has two languages: **LLBC** (concrete PL semantics, Fig. 1's middle layer) and **LLBC#** (symbolic, the actual borrow checker — Fig. 4's top layer). M9.6 cited only LLBC# rules.

**Recommendation:** port **LLBC# only** in Phase A. LLBC enters the picture only at Phase G when we port Theorem 4.1 ("LLBC# borrow-checking implies LLBC safe execution") and Theorem 3.3 ("LLBC ↔ PL forward simulation"). Those theorems are *internal* to the paper-side surface — we can axiomatize them in Phase A and discharge in Phase G after the soundness backbone (Phases C, D, E) is done. Concretely:

- Phase A introduces `LLBCSafe : LLBCState → Prop` and `LLBCSharp_to_LLBC : Theorem`-stubs as `axiom`s.
- Phase G replaces them with real ports.

This is the same shape as the M9.6 plan (which axiomatized `LLBCState` and replaced it incrementally). It lets us measure progress in terms of "axioms remaining in `Soundness/`," parallel to M9.6's "M9.5* shortcuts remaining."

### 0.3 Trusted base — explicit

The campaign's done condition is **all `axiom` declarations removed from `AeneasSoundness.Soundness.*`** *except* the four listed below. These four are the trusted base; they remain `axiom` (or `Lean.Mathlib`-derived) forever.

| Trusted-base axiom | Why trusted | Mitigations |
|---|---|---|
| **`CertGen_faithful`** (Aeneas's OCaml interpreter emits certs that are real traces *of the LLBC the same cert embeds*) | We have no Lean port of `src/cert/CertGen.ml` or `src/cert/LlbcJson.ml` to typecheck against. The Lean side has no view into the OCaml side. | Mitigated by `--differential` testing in `tests/lean-checker/differential/` and by the existing G1–G4 sweep (89/89). A bug in `CertGen` is an OCaml bug, not a Lean theorem violation. |
| **`paper_thm_3_1_confluence`** (LLBC# reduction is confluent up to ≤) | This is Theorem 3.1 of the paper. We port it in Phase G, but the port is a *re-derivation*, not a re-proof from first principles. We trust the paper's Appendix B. | If a port reveals a paper gap, the user pings the paper authors; outside the campaign's scope. |
| **`paper_thm_4_1_safe`** (LLBC# borrow-checking implies LLBC safety) | Theorem 4.1; same caveat as above. | Same mitigation. |
| **`paper_thm_3_3_pl_refines`** (LLBC ↔ PL forward simulation under step-indexing) | Theorem 3.3; ditto. | Same mitigation. |

What is *not* trusted: the join-algebra correspondence, `concretise`'s well-formedness, every per-event step lemma, the induction over events, the crate-level corollary. All of those are *proved* (replacing axioms in `StepEventSound.lean` with real definitions/theorems).

A `#print axioms cert_implies_pl_safety` in Phase G's final commit must list only the four above plus Lean's core (`propext`, `Classical.choice`, `Quot.sound`).

**Quantifier domain (post-cert-v3).** The M10 top-level theorem now reads, schematically,

```
∀ cc : CrateCert,
  replayCrate cc = .ok _ →
  ∀ f ∈ cc.functions,
    ∃ d : LStep⋆,  d is a valid LLBC# derivation for f.events
                   under the LLBC program cc.llbcProgram
```

Pre-M9.7, the theorem also had to quantify over a separate `llbc : LlbcProgram` argument and carry a `cc.crateHash = md5(llbc)` premise, then *re-thread* the same `llbc` through every per-event lemma. Cert v3 (M9.7) collapses this: `cc.llbcProgram` *is* the LLBC the derivation refers to. The `CertGen_faithful` axiom carries the OCaml-side promise that the embedded program is the post-pre-pass crate state the symbolic interpreter actually walked; the Lean side never compares against a separate file. This removes one quantifier from the top-level statement, one premise from every per-event lemma, and the entire engineering hazard around (LLBC, cert) mismatch.

### 0.4 Cert v3 boundaries (carried into every phase)

M9.7 reshaped what the campaign's per-event lemmas see and what the trusted base covers. The downstream phases (A–F) inherit these boundaries; flagging them once here:

- **Static program lookup**: function signatures, locals' LLBC types, ADT field shapes, trait method tables — all live in `cc.llbcProgram.{funDecls,typeDecls,traitDecls,traitImpls}`. The pre-v3 flat `cc.typeDecls` / `cc.traitDecls` / `cc.traitImpls` mirrors and the per-function opaque-string `FunCert.signature` are gone (M9.7o-E5a/E5b). Whenever a Phase-C/D/E/F lemma needs a callee signature or a struct's field types, it goes through `cc.llbcProgram` — *not* through `FunCert`.
- **Function-cert ↔ funDecl pairing**: each `FunCert` is paired to its `LlbcFunDecl` by name (`f.fnName ≡ lfd.itemMeta.name`). A helper `lookupFunDecl (cc : CrateCert) (f : FunCert) : Option LlbcFunDecl` (to be introduced in Phase A) is the canonical glue; every lemma that needs `f`'s signature takes a hypothesis `lookupFunDecl cc f = some lfd` and works from `lfd.signature` / `lfd.localsTypes`.
- **`CertGen_faithful` coverage**: the axiom (§0.3) is broader post-M9.7 — it now covers *both* "the events are a real interpreter trace" *and* "the embedded `llbcProgram` is the post-pre-pass crate state that trace was produced from." A single OCaml-side honesty assumption underpins both.
- **No external LLBC argument**: top-level theorems, per-function theorems, per-event lemmas all quantify over `cc : CrateCert` alone. The `(llbc, cert)` pair with hash premise is retired throughout — the per-event lemma signatures in Phase C and the function-level signature in Phase E both lose one `llbc : LlbcProgram` argument and the `crateHash`-equals-MD5 premise. Wherever this plan still reads "the LLBC", it means `cc.llbcProgram` of the ambient `cc`.

---

## 1. Phase A — Paper-side surface (LLBC# port)

**Deliverable:** A Lean port of paper Figs. 3, 7, 8, 9, 11, replacing the four `axiom`s `LLBCState`, `concretise`, `Valid`, `LStep` in `StepEventSound.lean` with real declarations *signatures only* (the proofs in `Step.lean` come in Phase C). After Phase A, the soundness skeleton typechecks against real types but every soundness lemma is still `sorry`.

**Estimated LOC:** ~2.5–3 kLOC across `LLBCSharpPaper/`. **Estimated duration:** 15–22 days, 5–10 commits.

### 1.1 Sub-deliverables

| Module | What it contains | Paper anchor | Est. LOC |
|---|---|---|---|
| `LLBCSharpPaper/Syntax.lean` | `Val#` (value grammar: `borrow^m`, `loan^m`, `borrow^s`, `loan^s`, `⊥`, ADTs, literals); `Place#`; `RegionAbs` (a `Multiset` of role entries). | Fig. 2 + §4.1 | ~600 |
| `LLBCSharpPaper/State.lean` | `LLBCState` as `{ ctx : Map Local Val#, abs : Map AbsId RegionAbs, freshness : NonceCounters }`; reads/writes; place-resolution `Ω(p) ⇒ v`. | Fig. 2 + §4.1 | ~400 |
| `LLBCSharpPaper/Program.lean` | **(M9.7-introduced.)** Helpers over `cc.llbcProgram`: `lookupFunDecl : CrateCert → FunCert → Option LlbcFunDecl`; `lookupTypeDecl`, `lookupTraitDecl`, `lookupTraitImpl` (by id and by qualified name); `signatureOf : CrateCert → FunCert → Option LlbcSignature` (composes `lookupFunDecl` with `.signature`); `localsTypesOf : CrateCert → FunCert → Option (Array LlbcTy)`. The phase's per-event and per-function lemmas thread `cc` and use these helpers wherever the pre-v3 plan reached into `f.signature`. | — | ~250 |
| `LLBCSharpPaper/WellFormed.lean` | `WellFormed Ω#` — borrow-id uniqueness, loan-side ↔ borrow-side pairing, no dangling refs, abs-membership disjointness. Plus `WellFormedProgram : LlbcProgram → Prop` (well-formedness of the embedded LLBC subtree: typeDecl ids are dense and unique; trait-impls reference declared traits; funDecls reference declared types). | implicit in Fig. 3 side conditions | ~400 |
| `LLBCSharpPaper/Step.lean` | `inductive LStep : LLBCState → Event → LLBCState → Prop` with one constructor per paper rule. | Figs. 3, 7, 8, 9, 11 | ~1.5k |
| `LLBCSharpPaper/Valid.lean` | `Valid : Event → LLBCState → Prop` — per-event side-condition predicate. | Figs. 3, 7, 8, 9, 11 (premises) | ~300 |

### 1.2 Per-paper-rule plan for `LStep` constructors

Each row produces one `LStep` constructor and one `Valid` clause. Order matches the cert ↔ rule table at `documentation/cert-format-and-soundness.md:113-132`.

| Constructor | Paper rule (Fig:line) | Premises (the `Valid` body) | Conclusion shape |
|---|---|---|---|
| `LStep.mutBorrow_direct` | E-MutBorrow / Fig. 3 | `Ω#(p) = some v`, `⊥, loan^{s,m} ∉ v`, `ℓ ∉ dom(loans)` | `Ω# ⟶_# Ω#[p ↦ loan^m ℓ; ℓ ↦ borrow^m ℓ v]` |
| `LStep.mutBorrow_inAbsReborrow` | Le-Reborrow-MutBorrow-Abs / Fig. 8 | parent loan live in named abs; ℓ fresh; place projects through parent | `Ω# ⟶_# Ω# ∪ abs[ℓ ↦ borrow^m ℓ _]` |
| `LStep.mutBorrow_loopOwned` | loop-fixpoint borrow / §5.2 (no named rule) | loop's region abs is open; ℓ fresh | abs-extended state |
| `LStep.sharedBorrow` | E-SharedBorrow / Fig. 3 | `Ω#(p) = some v`, `⊥ ∉ v`, ℓ_s fresh | dual of `mutBorrow_direct` |
| `LStep.endBorrow_direct` | Reorg-End-MutBorrow / Fig. 3 | `Ω#[loan^m ℓ, .]` hole not under a borrow; `loan^{s,m} ∉ v` | `Ω#[loan^m ℓ, borrow^m ℓ v] ↪ Ω#[v, ⊥]` |
| `LStep.endBorrow_reborrow` | (no separate rule — end of reborrow is implicit when parent abs closes) | parent abs in scope | `Ω#` unchanged on ctx; only frees ℓ |
| `LStep.endBorrow_shared` | (paper omits; same shape as mut for the symbolic side) | shared loan tracked | dual |
| `LStep.move` | E-Move / Fig. 3 | `Ω#(src) = some v` | `Ω#[src ↦ ⊥; dst ↦ v]` |
| `LStep.copy` | (paper omits; trivial — only valid for `Copy`-bounded types, but symbolic state doesn't track Copy bounds; the cert's emission is the witness) | `Ω#(src) = some v` | `Ω#[dst ↦ v]` (src untouched) |
| `LStep.assign` | E-Assign / Fig. 3 | rhs reduces to `v` in Ω# | `Ω#[dst ↦ v]` |
| `LStep.assert_true` | E-Assert (sugar) | `cond ⇓ true` | `Ω#` unchanged |
| `LStep.assert_false_panic` | E-Assert (sugar) | `cond ⇓ false ∧ expected = true` | `panic` (next event must be `EvPanic`) |
| `LStep.binop` | E-BinaryOp / Fig. 3 (rvalue) | operands well-formed | `Ω#[dst ↦ sym n]` (fresh sym; we don't model arith results) |
| `LStep.panic` | E-Panic / Fig. 3 | (none) | `Ω#` unchanged; trace must terminate |
| `LStep.retn` | E-Step-Return / Fig. 7 | retval bound | terminal state |
| `LStep.reborrow` | Le-Reborrow-MutBorrow-Abs / Fig. 8 (mut form, on entry) | parent loan live; parent abs declared (`parentAbs` hint) | abs-extended state with new mut sub-borrow |
| `LStep.call` | E-Call-Symbolic / Fig. 9 | for each role in `absSig`, an `A_in(ρ)` shape with the right loan/borrow roles | `Ω# ∪ ⋃abs ∪ [dst ↦ σ_fresh]` |
| `LStep.endAbs` | Reorg-End-Abs / §4.1, Fig. 8 | abs contains no live loans other than those in `releasedLoans`; final values typed-compatible | drop abs; release loans |
| `LStep.symExpandMutBorrow` | lazy mut-borrow expansion / §4.1 (rewriting; no named rule) | `parentAbs` owns the sym; substitution scope is `substLocals ∪ substLoans` | `Ω#` with σ rewritten to borrow tag |
| `LStep.join_same` | Join-Same / Fig. 11 | `Ω#_left(l) = Ω#_right(l)` | result inherits |
| `LStep.join_symbolic` | Join-Symbolic / Fig. 11 | both branches differ; values borrow-free; fresh σ | result has fresh σ |
| `LStep.join_mutBorrows` | Join-MutBorrows + Collapse-Dup-MutBorrow / Fig. 11 | both sides hold mut borrow; new abs allocated | result has fresh borrow inside new abs |
| `LStep.join_var` | Join-Var / Fig. 11 | abs absorbs whole var | result fold |
| `LStep.join_bottom_other` / `LStep.join_other_bottom` | Join-Bottom-Other / Join-Other-Bottom / Fig. 11 | one side `⊥`; other gets abs-wrapped | dual |
| `LStep.loopInv` | loop fixpoint snapshot / §5.2 | invariant is a fixpoint of the body under ≤ | abs-extended state with loop's region abs declared |
| `LStep.loopEnd` | end-of-body / §5.2 (no rule) | depth bookkeeping | unchanged |
| `LStep.matchArm` | (translator marker; no rule fires) | trivial | unchanged |

**Total constructors: 27.** This is the inductive `LStep` from `Step.lean`. `Valid` is a separate function-like predicate (a `match` on `Event` returning the same premise conjunction). Pair `LStep` and `Valid` so `Valid e Ω` iff `∃ Ω', LStep Ω e Ω'`.

### 1.3 Sub-phase commits (Phase A)

| # | Commit (M10.0a–j) | What lands | Gates |
|---|---|---|---|
| A1 | `M10.0a Soundness: scaffold aeneas-lean-soundness Lake package + Mathlib pin` | `aeneas-lean-soundness/` skeleton, lakefile, CI lane stub. Move `StepEventSound.lean` from checker to soundness. | G1–G4 + new G7 (soundness build < 30 min cold) |
| A2 | `M10.0b Soundness: port LLBCSharpPaper.Syntax (Val#, Place#, RegionAbs)` | `Syntax.lean`. No proofs; just type definitions. | G7 |
| A3 | `M10.0c Soundness: port LLBCSharpPaper.State (LLBCState, ctx, abs maps)` | `State.lean`. | G7 |
| A4 | `M10.0d Soundness: define LLBCSharpPaper.Program helpers (lookupFunDecl / signatureOf / localsTypesOf over cc.llbcProgram)` | `Program.lean` (M9.7-introduced). | G7 |
| A5 | `M10.0e Soundness: port LLBCSharpPaper.WellFormed (borrow-graph predicate + WellFormedProgram)` | `WellFormed.lean`. | G7 |
| A6 | `M10.0f Soundness: port LStep — Fig. 3 rules (mutBorrow, sharedBorrow, endBorrow, move, copy, assign, assert, binop, panic, retn)` | First half of `Step.lean`. Mutable-borrow + ownership rules. | G7 |
| A7 | `M10.0g Soundness: port LStep — Fig. 7+8 rules (reborrow, call, endAbs, symExpandMutBorrow)` | Second half. Abstraction rules. | G7 |
| A8 | `M10.0h Soundness: port LStep — Fig. 11 rules (the 6 join constructors)` | Third batch. | G7 |
| A9 | `M10.0i Soundness: port LStep — §5.2 loop rules (loopInv, loopEnd, matchArm)` | Final batch. | G7 |
| A10 | `M10.0j Soundness: port Valid predicate (per-event premise extractor)` | `Valid.lean`. Defined by `match` on `Event`. Includes `Valid_iff_LStep_exists` smoke lemma (sorry). | G7 |
| A11 | `M10.0k Soundness: replace 4 axioms in StepEventSound.lean with real types` | The skeleton stops being all-axiom; its statements still all-sorry. | G7 |

**Phase-A gate (vertical slice):** at A11, the file `StepEventSound.lean` typechecks against real types. Every theorem in it is `sorry`'d. Run `#print axioms stepEvent_sound` and see only `sorryAx` plus the Lean core (no domain `axiom`s).

### 1.4 Risks (Phase A)

- **Region-abstraction representation choice.** Two natural shapes: (a) `Multiset (Role × LoanId)` (intrinsic finite multiset; Mathlib-flavoured) or (b) `Std.HashMap AbsId AbsContent` mirroring the M9.6 `absRegistry`. Recommendation: **start with (a)** for proof ergonomics; the `concretise` map ((b) → (a)) is straightforward. (a) plays well with `simp` and `decide` on small cases; (b) doesn't.
- **The Fig. 9 `inst_sig` algebra.** `E-Call-Symbolic` freshens lifetimes via `inst_sig`. We will likely *not* model this in full and instead trust the M9.6 `absSig` hint as the contract — `Valid.call` takes `absSig` literally rather than re-deriving it.
- **Fig. 11 `Collapse-Merge-Abs` / `Collapse-Dup-MutBorrow`.** Two rules fold abstractions. Modelling fold as a separate step vs. folding it into `LStep.join_*` is a design call; recommendation: keep `Collapse-*` as separate `LStep` constructors (extra ~150 LOC), invoked transitively in the `join_*` rules' premises. Cleaner than baking them into the join lemma.
- **Build time.** Mathlib pull-in is ~25–35 min cold. Mitigation: pin a Mathlib version, cache CI, and accept that soundness CI runs in its own slow lane. The checker's CI stays fast.

---

## 2. Phase B — `concretise` and its well-formedness

**Deliverable:** A defined function `concretise : SymState → LLBCState` plus well-formedness lemmas `concretise_wellFormed : ∀ st, Replay-valid st → WellFormed (concretise st)` and `concretise_inversion` (round-trip-like properties tying replayer-side updates to LLBC#-side updates).

**Estimated LOC:** ~700–1000. **Estimated duration:** 6–10 days, 3–5 commits.

### 2.0 Static vs. dynamic split (post-cert-v3)

`concretise` lifts only the *dynamic* state — replayer's `SymState` (env, loans, numLocals, absRegistry) up to paper's `LLBCState` (ctx, abs, freshness). The *static* program (`LlbcProgram`: type/fun/trait decls) does not need a Lean-side lift — it is read directly from `cc.llbcProgram`. The pre-v3 framing folded both into a single (LLBC, cert) pair and required a `concretise_program` companion; cert v3 removes the second half entirely. The Phase-B lemmas in §2.2 below are unchanged in shape from the pre-v3 plan; they no longer have to mention an external `LlbcProgram` argument.

### 2.1 What `concretise` does

For each `SymState` component (`env`, `loans`, `numLocals`, `absRegistry`):

| `SymState` field | `LLBCState` analogue | Concretisation |
|---|---|---|
| `env : Std.HashMap Nat Val` | `ctx : Map Local Val#` | lift each `Val` to `Val#`. `Val.sym n → Val#.sym n` etc.; `Val.bottom → Val#.⊥`. ADTs / tuples / records (the M9.5d/f/p collapse) lift to `Val#.opaque` (a deliberate lossy projection). |
| `loans : Std.HashMap Nat LoanInfo` | implicit (loans live inside `ctx` values and `abs` entries) | for each `LoanInfo` with `kind = .direct`: the loan lives directly in `ctx` (an `Ω#(local) = loan^m ℓ`). For `.reborrow` / `.lazyExpand`: the loan lives in a region abstraction; lift to a fresh `abs` entry. |
| `numLocals` | `ctx.dom`'s cardinality | no semantic lift; just an invariant. |
| `absRegistry : Std.HashMap Nat AbsShape` | `abs : Map AbsId RegionAbs` | for each `(absId, shape)`: build a `RegionAbs` from `shape.roles` (mutBorrow/mutLoan/sharedBorrow entries → `borrow^m`/`loan^m`/`borrow^s` role markers). `shape.parentAbs` becomes the abs's ancestor link. |

The lossy parts of `concretise` are exactly the `M9.5d/f/p` collapse points: an ADT/tuple/record in `env` projects to `Val#.opaque`. This is *fine* for the soundness theorem — we only claim "*structural* LLBC# well-formedness preserved," not value-equivalence through ADTs.

### 2.2 Sub-phase commits (Phase B)

| # | Commit (M10.1a–e) | What lands |
|---|---|---|
| B1 | `M10.1a Soundness: define concretise — env + numLocals` | `Concretise/Defn.lean` (partial). |
| B2 | `M10.1b Soundness: define concretise — loans + absRegistry` | finish `Defn.lean`. |
| B3 | `M10.1c Soundness: prove concretise preserves WellFormed (smoke lemma)` | one-liner: `theorem concretise_wellFormed_smoke : WellFormed (concretise (SymState.empty 0))`. Easy; flushes the type contract. |
| B4 | `M10.1d Soundness: prove concretise inversion lemmas (env, loans, abs)` | `concretise_env_get : (concretise st).ctx l = liftVal (st.env[l]?)` etc. ~6 lemmas. Each is provable by `simp` on the definitions. |
| B5 | `M10.1e Soundness: prove concretise_set_local / addLoan / removeLoan commute lemmas` | for each `SymState` mutator (`setLocal`, `addLoan`, `takeLoan`), prove `concretise (mutator st …) = mutator# (concretise st) …`. These are the bedrock of Phase C's per-event proofs. |

### 2.3 Risks (Phase B)

- **Hidden coupling between `loans` and `env`.** The replayer's invariant is that a `.direct` loan has a `.mutLoan b` token somewhere in `env`. The paper's invariant is the same but stronger (the loan's value flows back to a *specific* hole). Recommendation: prove a `LoanTokenInvariant : SymState → Prop` once, propagate everywhere.
- **`absRegistry` is populated only on `EvCall`.** For loans created by `EvMutBorrow` with `.inAbsReborrow absId` *before* the relevant `EvCall`, there's no abs in the registry to lift into. The current replayer tolerates this (commit M9.6's docstring §3.2.1 acknowledges abs ids stay opaque). **The concretise has to invent a placeholder `RegionAbs.unknown` for these cases.** This is the cleanest fix: extend `LLBCState.abs` codomain to `RegionAbs ⊕ Unknown`. Add to Phase A risks; reflect in Phase B's commit message.

---

## 3. Phase C — Per-event sub-soundness lemmas

**Deliverable:** All 27 per-rule sub-soundness lemmas from `StepEventSound.lean` (and the per-`MutBorrowKind` / per-`JoinRule` splits) proved. After Phase C, the file's *event-case* lemmas (`stepMutBorrow_direct_sound`, `stepMutBorrow_inAbsReborrow_sound`, …, `stepJoin_witnessed_sound`) are `theorem`, not `axiom`.

**Estimated LOC:** ~3.5–5 kLOC of proofs. **Estimated duration:** 25–35 days, 20–30 commits. **This is the campaign's bulk.**

### 3.1 Per-lemma plan

Each lemma has the shape (cf. `StepEventSound.lean:73-113`):

```lean
theorem stepXxx_yyy_sound
  (st st' : SymState) (Ω : LLBCState) (hRep : concretise st = Ω)
  (hWF  : WellFormed Ω)
  (hStep : Replay.stepXxx st … = .ok st')
  : ∃ Ω', Valid (Event.xxx … ) Ω ∧ LStep Ω (Event.xxx …) Ω' ∧ concretise st' = Ω'
```

Proof pattern (uniform across all lemmas; differs only in which `LStep` constructor and which `concretise` commute-lemma is used):

```
1. Unfold `Replay.stepXxx` to see what `SymState.fields` it touched.
2. Apply Phase-B commute lemmas to push `concretise` through the touched fields.
3. Witness Ω' = (whatever the LStep rule says). Use `exact ⟨Ω', _, _, _⟩`.
4. Discharge `Valid` from the replayer's side-condition checks (the bounds checks
   and freshness checks in `stepXxx`).
5. Discharge `LStep` by applying the corresponding `LStep.xxx_yyy` constructor.
6. Discharge `concretise st' = Ω'` from Phase-B's commute lemmas (often pure rfl).
```

### 3.2 Per-event ordering (in commit order)

Lemmas ordered to bootstrap: trivial passthroughs first, in-replayer-state-touching next, then hint-bearing, with the join lemma last (the hardest).

| # | Commit (M10.2a–z…) | Lemma proved | Risk | Est. LOC | Agent |
|---|---|---|---|---|---|
| C1 | `M10.2a Soundness: stepPanic / stepRetn soundness (trivial passthroughs)` | `panic`, `retn` | Trivial | ~50 | `lean4:prove` |
| C2 | `M10.2b Soundness: stepMatchArm / stepLoopEnd soundness (no-op markers)` | `matchArm`, `loopEnd` | Trivial | ~80 | `lean4:prove` |
| C3 | `M10.2c Soundness: stepMove / stepCopy soundness` | `move`, `copy` | Low (single-field mutation) | ~120 | `lean4:prove` |
| C4 | `M10.2d Soundness: stepAssign soundness` | `assign` | Low | ~80 | `lean4:prove` |
| C5 | `M10.2e Soundness: stepAssert soundness (true/false branches)` | `assert` | Low (case on `cond`) | ~120 | `lean4:prove` |
| C6 | `M10.2f Soundness: stepBinop soundness` | `binop` | Low (binop result is symbolic placeholder) | ~80 | `lean4:prove` |
| C7 | `M10.2g Soundness: stepSharedBorrow soundness` | `sharedBorrow` | Low | ~150 | `lean4:prove` |
| C8 | `M10.2h Soundness: stepMutBorrow_direct soundness (.direct hint case)` | `mutBorrow_direct` | Medium | ~250 | `lean4:formalize` (lemma + first prove) |
| C9 | `M10.2i Soundness: stepMutBorrow_inAbsReborrow soundness` | `mutBorrow_inAbsReborrow` | Medium-high (abs registry interaction) | ~300 | `lean4:formalize` |
| C10 | `M10.2j Soundness: stepMutBorrow_loopOwned soundness` | `mutBorrow_loopOwned` | Medium | ~250 | `lean4:prove` |
| C11 | `M10.2k Soundness: stepEndBorrow_direct soundness` | `endBorrow_direct` (kind = direct) | High (token restoration; env scan) | ~400 | `lean4:formalize`, escalate to `lean4:autoprove` |
| C12 | `M10.2l Soundness: stepEndBorrow_reborrow / .shared / .lazyExpand soundness` | three sub-cases | Medium | ~350 | `lean4:prove` |
| C13 | `M10.2m Soundness: stepReborrow soundness` | `reborrow` (with `parentLive` / `parentAbs` hint) | Medium-high | ~300 | `lean4:formalize` |
| C14 | `M10.2n Soundness: stepCall soundness (absSig hint case)` | `call` (uses `absSig`) | High (absRegistry insertion + abs creation) | ~500 | `lean4:formalize` |
| C15 | `M10.2o Soundness: stepEndAbs soundness (releasedLoans + tokenClearLocals)` | `endAbs` | High (abs validation, multi-loan release) | ~500 | `lean4:formalize` |
| C16 | `M10.2p Soundness: stepSymExpandMutBorrow soundness` | `symExpandMutBorrow` (`parentAbs` + `substLocals` + `substLoans`) | High (substitution scope) | ~450 | `lean4:formalize` |
| C17 | `M10.2q Soundness: stepLoopInv soundness (loanRegistry hint)` | `loopInv` | Medium | ~300 | `lean4:prove` |
| C18 | `M10.2r Soundness: stepJoin — JoinSame entry soundness` | per-entry `JoinSame` | Medium | ~250 | `lean4:formalize` |
| C19 | `M10.2s Soundness: stepJoin — JoinSymbolic entry soundness` | per-entry `JoinSymbolic` | Medium | ~250 | `lean4:formalize` |
| C20 | `M10.2t Soundness: stepJoin — JoinMutBorrows entry soundness (fresh abs)` | per-entry `JoinMutBorrows` + `Collapse-Dup-MutBorrow` | **Highest** (paper's join algebra; the cert-format doc §5 step 4 explicitly flags this) | ~600 | `lean4:formalize`, very likely escalation to `lean4:sorry-filler-deep` |
| C21 | `M10.2u Soundness: stepJoin — JoinVar entry soundness` | per-entry `JoinVar` | Medium-high (region abs absorption) | ~350 | `lean4:formalize` |
| C22 | `M10.2v Soundness: stepJoin — JoinBottomOther / JoinOtherBottom entry soundness` | the two ⊥-propagation rules | Medium | ~300 | `lean4:prove` |
| C23 | `M10.2w Soundness: stepJoin_witnessed_sound (assemble from per-entry lemmas)` | the top-level join lemma (induction over `witnesses`) | Medium (the inductive step) | ~250 | `lean4:prove` |

**Phase-C gate (vertical slice 1):** at C8 (`stepMutBorrow_direct_sound`), run `#print axioms stepMutBorrow_direct_sound`: must list `sorryAx` only for sibling-lemmas, not for the target. This is the first non-trivial proof and is the model for all 27.

**Phase-C gate (vertical slice 2):** at C23, the join lemma. The single highest-risk lemma; if this can be proved cleanly, the campaign is past the hardest technical hump.

### 3.3 Parallelism in Phase C

The lemmas in Phase C are *logically* independent (each is about one event), but they touch shared infrastructure (`Concretise/Defn.lean`'s commute lemmas, `LLBCSharpPaper/WellFormed.lean`'s invariants). Real parallelism:

| Batch | Lemmas | Shared files | Parallel? |
|---|---|---|---|
| C1–C7 (trivial / single-mutator events) | panic, retn, matchArm, loopEnd, move, copy, assign, assert, binop, sharedBorrow | All touch `StepEventSound.lean` (write); read `Concretise/Defn.lean` | **Sequential within `StepEventSound.lean`.** Each commit adds a `theorem` block. |
| C8–C10 (mutBorrow split) | direct, inAbsReborrow, loopOwned | All touch `StepEventSound.lean`; read `LLBCSharpPaper/Step.lean` | Sequential. |
| C11–C12 (endBorrow split) | by `LoanKind` | Same | Sequential. |
| C13–C17 (independent hinted events) | reborrow, call, endAbs, symExpandMutBorrow, loopInv | Same | Sequential. |
| C18–C23 (join split) | per-`JoinRule` entry lemmas | Same | Sequential, but **per-entry lemmas can be drafted in parallel worktrees**, then merged. The worktree's commit-message prefix names which entry. |

The honest answer is the same as the Option C plan: little real parallelism, since the file `StepEventSound.lean` (and likely a new `LemmasShared.lean`) is the shared write. Worktree isolation is for *clean discard* of bad agent attempts, not for speed. Use parallel worktrees only when a single agent has been spinning on a hard lemma for >2 hours and you want a second perspective.

### 3.4 Risks (Phase C)

- **Join algebra (C20).** Paper Fig. 11's `Collapse-Dup-MutBorrow` introduces a *fresh* region abstraction. The replayer's `stepJoin` does **not** add an entry to `absRegistry` — the cert's `JoinMutBorrows` constructor carries `abs : Nat` but the replayer's join doesn't allocate. **This is a gap.** Either (a) extend M9.6 to emit a follow-up `EvCall`-like event in joins, or (b) prove the soundness with a side condition `∃ shape, st.absRegistry[abs]? = some shape ∨ True` (i.e., abs may be opaque). Recommendation: (b) for the campaign; flag as a follow-up to M9.6 (see Open Questions §11).
- **`stepEndBorrow_direct` env scan (C11).** `stepEndBorrow` walks `st.env.toList` looking for `mutLoan b`. The corresponding `LStep.endBorrow_direct` premise says "the place that holds `loan^m ℓ` is unique." For uniqueness, we need a `WellFormed` invariant: each `.mutLoan b` appears at most once in `env`. The invariant needs to be established at every replayer-side mutator that might insert a `.mutLoan` — likely 3 places (`stepMutBorrow.loopOwned`, `stepMutBorrow.direct`, `stepSymExpandMutBorrow`). Establish the invariant in Phase B (`LoanTokenInvariant`).
- **`stepSymExpandMutBorrow` (C16).** The substitution rewrites `env` entries holding `.sym svId`. The `LStep` rule says the rewrite is *global* (the entire `Ω#`); the replayer's hint says it's *exactly* `substLocals ∪ substLoans`. Proving the two coincide requires: cert promise = the OCaml side enumerated every binding. We trust the broadened `CertGen_faithful` here (§0.3) — the same axiom that promises the embedded `cc.llbcProgram` is the post-pre-pass crate state; the lemma is *conditional* on a `SubstScope_Complete` premise that the axiom discharges. Recommendation: add `SubstScope_Complete` to `Valid.symExpandMutBorrow`'s premise list and discharge it from `CertGen_faithful`; do not add a *new* axiom.

---

## 4. Phase D — Top-level `stepEvent_sound`

**Deliverable:** `stepEvent_sound` (currently axiom at `StepEventSound.lean:124-128`) becomes a theorem proved by case-analysis on `ev`, delegating to the Phase-C per-event lemmas.

**Estimated LOC:** ~150 (mostly mechanical). **Estimated duration:** 1–2 days, 1–2 commits.

Proof shape (already sketched at `option-c-implementation-plan.md:526-545`):

```lean
theorem stepEvent_sound : … := by
  intro ev st st' Ω hRep hStep
  cases ev with
  | mutBorrow loan place sv kindHint =>
    cases kindHint with
    | direct          => exact stepMutBorrow_direct_sound …
    | inAbsReborrow a => exact stepMutBorrow_inAbsReborrow_sound a …
    | loopOwned l     => exact stepMutBorrow_loopOwned_sound l …
  | sharedBorrow … => exact stepSharedBorrow_sound …
  -- … 22 more cases, each a one-line delegate …
  | join l r res witnesses => exact stepJoin_witnessed_sound l r res witnesses …
```

**Phase-D gate:** `#print axioms stepEvent_sound` lists only Lean core + `paper_thm_*` (which haven't been touched yet, still axiom from Phase A) + `CertGen_faithful`. No `sorryAx`. No domain `axiom` from `LLBCSharpPaper/`.

### 4.1 Risks (Phase D)

- Mechanical phase; the only risk is *the cases not lining up* — i.e., one of the Phase-C lemmas has a slightly different signature than the cases-block expects. Mitigation: have Phase C agents always write the lemma signature first as a `sorry`'d theorem matching the case structure exactly; only after the signature is locked do they fill in the proof.

---

## 5. Phase E — `replayFun_sound`

**Deliverable:** Per-function soundness (cert-format doc §4.3):

```lean
theorem replayFun_sound :
  ∀ (cc : CrateCert) (f : FunCert) (lfd : LlbcFunDecl)
    (numLocals : Nat) (trace : CheckedTrace),
    f ∈ cc.functions →
    lookupFunDecl cc f = some lfd →
    Replay.replayFun numLocals f = .ok trace →
    ∃ Ω_in Ω_out,
      Initial(Ω_in, lfd.signature, cc.llbcProgram) ∧
      Ω_in ⟶_#* Ω_out ∧
      Final(Ω_out, lfd.signature, trace.finalState) ∧
      borrow_checks# (lfd.signature)
```

Proved by induction on `f.events`, threading `stepEvent_sound` through. The exit check (no `.direct` loan live) maps to the paper's `borrow_checks#` predicate.

The post-cert-v3 signature differs from the pre-v3 form in two ways: (i) it takes the ambient `cc : CrateCert` so per-event lemmas inside the induction can resolve callee signatures via `cc.llbcProgram.funDecls`; (ii) it carries the matched `LlbcFunDecl` explicitly so `Initial` / `Final` / `borrow_checks#` operate on the *structured* `LlbcSignature`, not on a stringified `FnSignature` (the latter no longer exists). `lookupFunDecl cc f = some lfd` is the campaign-wide glue introduced in Phase A's `Program.lean`.

**Estimated LOC:** ~600 (with helper lemmas). **Estimated duration:** 5–8 days, 3–5 commits.

### 5.1 Sub-phase commits

| # | Commit (M10.3a–d) | What lands |
|---|---|---|
| E1 | `M10.3a Soundness: define Initial, Final, borrow_checks# (paper Fig. 10 port; consumes LlbcSignature)` | the paper-side function-signature predicates |
| E2 | `M10.3b Soundness: prove replayFun_event_induct (induction over events array, cc threaded)` | the heavy-lifting lemma; iterates over `f.events`, threading `stepEvent_sound` |
| E3 | `M10.3c Soundness: prove replayFun_post (exit check = paper post-condition)` | the leak-check correspondence — "no `.direct` loan at exit ⇔ paper's `Final` shape" |
| E4 | `M10.3d Soundness: assemble replayFun_sound` | compose E1 + E2 + E3 |

**Phase-E gate:** the lemma's `#print axioms` is the same as Phase D's plus E1's new defs.

### 5.2 Risks (Phase E)

- **`Initial`/`Final` over `LlbcSignature` (post-cert-v3).** The paper's `borrow_checks#` (Fig. 10) reads off signature-derived region abstractions; M9.6's `EvCall.absSig` ports those abs shapes per-call, but the *function-entry* abs shapes (for the function's own input borrows) are not in the cert proper. They have to be reconstructed from the structured `LlbcSignature` (via the `lookupFunDecl cc f = some lfd` pairing). Mitigation: add a small `signatureToInitialAbs : LlbcSignature → Array AbsShape` in `LLBCSharpPaper/Program.lean` (Phase A) and use it in `Initial`. Pre-v3 this helper took the opaque-string `FnSignature` and had to parse RawTy substrings; the structured form makes it a clean pattern-match on `LlbcTy`.
- **The "function-exit loan leak" check (Phase E vs. M9.6).** `Replay.replayFun` at `replayFun:97-101` checks `leakedDirect.isEmpty`. The corresponding paper post-condition is on `Final`. Phase E3's proof has to handle the `.reborrow` / `.lazyExpand` / `.shared` *leaks-allowed* cases. The cert-format doc §4.5 says this requires invoking the loop's / caller's region abstraction. The paper-side `Final` definition has to permit those kinds of leaks; Phase A's `Final` must encode this exception explicitly.
- **`lookupFunDecl` totality** (post-cert-v3). Every `FunCert` in `cc.functions` has a matching `LlbcFunDecl` in `cc.llbcProgram.funDecls` — this is part of what `CertGen_faithful` promises. Phase E threads `lookupFunDecl cc f = some lfd` as a hypothesis; the *totality* lemma `∀ f ∈ cc.functions, ∃ lfd, lookupFunDecl cc f = some lfd` is a Phase-F preamble (it falls out of `replayCrate cc = .ok` because the checker side already pairs them up — see M9.7h's `checkLlbcVsCert`). Don't re-axiomatise it.

---

## 6. Phase F — `replayCrate_implies_borrow_checks`

**Deliverable:** Crate-level corollary (cert-format doc §4.4):

```lean
theorem replayCrate_implies_borrow_checks :
  ∀ (cc : CrateCert),
    Replay.replayCrate cc = .ok _ →
    ∀ f, f ∈ cc.functions →
      ∃ lfd, lookupFunDecl cc f = some lfd ∧ borrow_checks# (lfd.signature)
```

Direct corollary of `replayFun_sound`, quantified over `cc.functions`. The `lookupFunDecl cc f = some lfd` clause is supplied by the *function-pairing totality* lemma (a Phase-F preamble; cf. §5.2): every replayed function has a matching `LlbcFunDecl` because `Replay.replayCrate` only succeeds when the M9.7h consistency-pair check (`Consistency.checkLlbcVsCert`) is also green, and that check already requires the pairing. Plus a typecheck-side lemma showing that `Typecheck.checkCrateCert` is a sound under-approximation of the structural well-formedness needed by `replayFun_sound`.

**Estimated LOC:** ~350 (slightly higher than pre-v3 because of the pairing totality preamble). **Estimated duration:** 2–4 days, 3 commits.

| # | Commit (M10.4a–c) | What lands |
|---|---|---|
| F1 | `M10.4a Soundness: prove typecheck_implies_wellFormedInit` | the typechecker's post-condition implies `WellFormed (concretise (initial SymState))` |
| F2 | `M10.4b Soundness: prove lookupFunDecl_total_of_replayCrate_ok` | every `f ∈ cc.functions` has a matching `LlbcFunDecl`; falls out of the M9.7h pair check |
| F3 | `M10.4c Soundness: assemble replayCrate_implies_borrow_checks` | the crate corollary |

**Phase-F gate:** `#print axioms replayCrate_implies_borrow_checks` lists Lean core + `paper_thm_*` + `CertGen_faithful` + the typecheck-side lemma (which is provable, not trusted).

---

## 7. Phase G — Paper theorem ports

**Deliverable:** Lean ports of paper Theorems 3.1, 3.3, 4.1, 4.2, replacing the four trusted-base placeholder `axiom`s introduced in Phase A. After Phase G, the trusted base shrinks to just `CertGen_faithful` plus Lean core.

**Estimated LOC:** ~4–6 kLOC (paper-derived; the paper's Appendix A/B is ~50 pages of proof). **Estimated duration:** 30–50 days, 10–15 commits. **This is the campaign's optional phase — the project could ship after Phase F with the four paper theorems as trusted-base axioms.**

### 7.1 Recommendation

**Defer Phase G.** Ship Phases A–F as M10.0–M10.4. Treat Phase G as an open M11 milestone, scheduled as time permits. The end-to-end safety guarantee (the `cert_implies_pl_safety` corollary) is *still derivable* as long as the four paper theorems remain as trusted-base axioms; the user gets all the engineering benefit (every cert that passes is a witness of safe execution) without paying the Theorem-3.1 port cost. The paper's authors have signed the proofs; the rationality of trusting them is well-established.

If Phase G is undertaken (M11+):

| # | Commit (M10.5a–o) | What lands |
|---|---|---|
| G1 | `M10.5a Soundness: port LLBC concrete syntax (Fig. 2 — concrete value grammar)` | the LLBC language; ~600 LOC |
| G2 | `M10.5b Soundness: port LLBC reduction relation ⟶_LLBC (Fig. 2 lower half)` | ~500 LOC |
| G3 | `M10.5c Soundness: port LLBC# → LLBC stripping function` | ~300 LOC |
| G4 | `M10.5d Soundness: port Thm 3.1 — Confluence of ⟶_#` | the largest port; ~1500 LOC |
| G5 | `M10.5e Soundness: port Thm 3.3 — LLBC ↔ PL forward simulation` | ~1200 LOC |
| G6 | `M10.5f Soundness: port Thm 4.1 — borrow_checks# implies LLBC-safe` | ~800 LOC |
| G7 | `M10.5g Soundness: port Thm 4.2 — well-formed initial state premise discharger` | ~400 LOC |
| G8–G15 | per-lemma cleanup, regression budget | misc |

### 7.2 End-to-end corollary

After Phase G (or in parallel, conditioned on the trusted-base axioms):

```lean
corollary cert_implies_pl_safety :
  ∀ (cc : CrateCert) (f : FunCert) (lfd : LlbcFunDecl),
    Replay.replayCrate cc = .ok _ →
    f ∈ cc.functions →
    lookupFunDecl cc f = some lfd →
    ∀ (Ω_pl : PLState) (n : ℕ),
      Initial_pl(Ω_pl, lfd.signature) →
      ¬ (Ω_pl ⊢ lfd.body ⟶_pl^n stuck)
```

Lands as a final commit (M10.6a). 80 LOC. Composes `replayCrate_implies_borrow_checks` + `paper_thm_4_1_safe` + `paper_thm_3_3_pl_refines`. The function *body* operated on by ⟶_pl is `lfd.body` (the structured LLBC statement tree the cert embeds) — not a separate compiled artifact the caller has to also produce. This is the user-visible payoff of cert v3: one file, one theorem.

---

## 8. Multi-agent orchestration

### 8.1 Agent ↔ phase mapping

| Phase | Primary agent | Secondary agent (escalation) | Why |
|---|---|---|---|
| A1 (Lake scaffold) | `general-purpose` | — | Infra: lakefile, CI config, file moves. Not proof work. |
| A2–A4 (Syntax/State/WellFormed) | `lean4:draft` (skeletons) → `general-purpose` (def fillers) | `lean4:refactor` (mathlib lookups) | Type definitions; lots of `inductive` declarations. |
| A5–A8 (LStep constructors) | `lean4:draft` (constructors as `sorry` premise lists) → `lean4:formalize` (fill premises) | — | Each constructor is a focused, well-scoped task. |
| A9 (Valid predicate) | `lean4:draft` | — | Match-on-Event boilerplate. |
| A10 (axiom replacement) | `general-purpose` | — | File restructuring. |
| B1–B5 (concretise + lemmas) | `lean4:formalize` | `lean4:prove` for individual lemmas | Definition + simp lemmas. |
| C1–C7 (trivial events) | `lean4:prove` (1 lemma per dispatch) | `lean4:autoprove` if a wave gets stuck | High-volume, low-difficulty. |
| C8–C17 (medium events) | `lean4:formalize` (statement + first attempt) | `lean4:autoprove` then `lean4:sorry-filler-deep` | Higher difficulty; lemma statements may need shaping. |
| C18–C22 (per-`JoinRule` entry lemmas) | `lean4:formalize` | `lean4:sorry-filler-deep` for stubborn ones; `lean4:proof-repair` after any shared-lemma refactor | The hardest lemma family. |
| C23 (join assembly) | `lean4:prove` | — | Induction over `witnesses`; mechanical given C18–C22. |
| D1 (stepEvent_sound) | `lean4:prove` | — | Mechanical case-analysis. |
| E1–E4 (replayFun_sound) | `lean4:formalize` | `lean4:autoprove` for E2's induction | E2 is the only non-trivial proof. |
| F1–F2 (crate corollary) | `lean4:prove` | — | Mechanical. |
| G1–G15 (paper theorem ports) | `lean4:formalize` | `lean4:axiom-eliminator` to remove the Phase-A placeholder axioms one at a time; `lean4:sorry-filler-deep` heavily | A separate sub-campaign; effectively re-living Phases A+C for the LLBC layer. |
| Cleanup / golfing | `lean4:proof-golfer` (post-Phase E) | `lean4:review` (between phases) | After Phase E ships, golf the bulky lemmas. |
| Cross-phase audits | `lean4:doctor` (after each phase boundary) + `Explore` for read-only searches | — | Catches axiom-set regressions, naming inconsistencies. |

### 8.2 Parallelism vs. serialisation

| Plan commits | Files touched | Parallel? |
|---|---|---|
| A1 alone | lakefile + file moves | n/a |
| A2–A4 (Syntax, State, WellFormed) | three different files | **Yes** — pure type definitions, no cross-dependencies *as long as* `Syntax.lean` lands first. |
| A5–A8 (LStep constructor batches) | all touch `Step.lean` | **No.** Same file. Sequential. |
| A9 (Valid) | `Valid.lean` only | Could run in parallel with A5–A8 *if* it doesn't reference `LStep`. Recommend sequential (A9 after A8) for simplicity. |
| A10 (axiom replacement) | `StepEventSound.lean` | n/a |
| B1–B2 (concretise def) | `Defn.lean` | Sequential. |
| B3–B5 (concretise lemmas) | `Defn.lean` (B5 may touch) + `WellFormed.lean` | Sequential. |
| C1–C7 (trivial events) | all touch `StepEventSound.lean` | **No.** Same file. Sequential. |
| C8–C10 (mutBorrow split) | `StepEventSound.lean` | Sequential. |
| C11–C12 (endBorrow split) | `StepEventSound.lean` | Sequential. |
| C13–C17 (hinted events) | `StepEventSound.lean` | Sequential. |
| C18–C22 (per-`JoinRule` entry lemmas) | One module `Soundness/JoinLemmas/JoinXxx.lean` per entry rule, then a `Soundness/JoinLemmas.lean` aggregator | **Yes** — if the per-entry lemmas are factored into a sub-namespace each in its own file. Recommend this factoring (~5 sibling files), then dispatch C18–C22 as a 5-wide parallel batch (worktree isolation). |
| C23 (join assembly) | `StepEventSound.lean` + aggregator | Sequential after C18–C22. |
| D1 | `StepEventSound.lean` | n/a |
| E1–E4 | new `Soundness/ReplayFunSound.lean` | E1 first; E2–E3 could run in parallel *if* E2 lemmas don't depend on E3. Recommend sequential for tractability. |
| F1–F2 | new `Soundness/ReplayCrateSound.lean` | Sequential. |
| G1–G15 | per-theorem files; can be very parallel | Yes (G1–G7 are largely independent paper theorems). |

The genuine parallelism in this campaign:
- A2–A4 (three sibling type files): 3-wide.
- C18–C22 (per-`JoinRule` entry lemmas, if factored): 5-wide.
- G1–G7 (per-paper-theorem ports): 4–7-wide.

Everywhere else is serial.

### 8.3 Checkpoints between phases (review gates)

After each phase boundary, run the following sequence before declaring the phase "done":

1. **Axiom inventory.** `#print axioms <phase-final-theorem>`. Compare to the expected list (recorded in the progress file). Any unexpected `sorryAx` or `axiom`-named entry blocks.
2. **`lean4:doctor` run.** Catches missing imports, stale `@[simp]` annotations, kernel inconsistencies.
3. **`lean4:review` (read-only audit) on the phase's new files.** A separate agent reads everything Phase-X produced and reports anomalies. No-edit, ~1-hour budget.
4. **Sweep parity.** `aeneas-lean-checker` G1–G4 (the M9.6 gates) must still be green — soundness work shouldn't perturb the checker. The two packages are isolated by Lake but it's possible a shared import was accidentally touched.
5. **Update the campaign progress file.** Like `.option-c-progress.md`, but `.m10-soundness-progress.md`.

### 8.4 Recovery from stuck agents

The `lean4:autoprove` hard-stop pattern (established for M9.6; the boot prompt that documented it was retired post-campaign) ports here. Specific stuck-paths:

- **`lean4:autoprove` hits 10 cycles with no progress on a Phase-C lemma.** Escalate to `lean4:sorry-filler-deep` with a tightened scope (`--deep-scope=target`, `--deep-max-lines=300`).
- **`lean4:sorry-filler-deep` returns "no progress" twice in a row.** Stop and escalate to the user: the lemma's *statement* may be wrong (Phase-A definition mismatch). Often the fix is a small `WellFormed` strengthening that ripples back into Phase B.
- **A whole `JoinRule` entry lemma is intractable (C20 specifically).** The cert-format doc §6.4 risk 2 names this as the most likely "schema needs `fmt_version=3`" trigger. If after one `lean4:sorry-filler-deep` attempt the lemma still doesn't go through, stop and surface the gap (see Open Questions §11).
- **Phase G port stuck on a paper-side detail.** This is acceptable — `axiom`-out the specific theorem inside Phase G's file, log it as "trusted base extension," and proceed. Phase G is the *bonus* phase; the campaign's M10 done condition does not require all of Phase G.

### 8.5 Agent prompt template

Every Phase-C agent receives the same template:

```
You are working on the LLBC# soundness campaign for Aeneas at
/Users/karthik/aeneas. Your assigned lemma is:

  <theorem signature, exact copy from StepEventSound.lean>

The lemma lives in:
  /Users/karthik/aeneas/aeneas-lean-soundness/AeneasSoundness/Soundness/StepEventSound.lean

The proof should:
1. Apply `Replay.stepXxx` (look up at LLBCSharp/Step.lean:<line>).
2. Use `concretise` commute lemmas from Concretise/Defn.lean (file outline
   via `lean_file_outline`).
3. Discharge `Valid` from the replayer's side checks.
4. Discharge `LStep` by `apply LStep.<the_right_constructor>`.

Before writing tactics, invoke these skills:
  - aeneas-lean-core
  - aeneas-tactics-quickref
  - lean-lsp-mcp

Your only allowed edits are:
  - StepEventSound.lean (this lemma's body)
  - Concretise/Defn.lean (only to add a missing commute lemma; flag with a TODO)
  - LLBCSharpPaper/WellFormed.lean (only to strengthen an invariant; flag)

If the lemma cannot be proved in 90 minutes:
  - Reduce to a sub-`sorry` that names what's missing.
  - Report back. The orchestrator will decide whether to escalate or to
    revise Phase A / B.

NEVER:
  - Use `omega`, `simp_all`, `partial_fixpoint_induct` (see aeneas-tactics-quickref).
  - Commit. The orchestrator merges your worktree.
```

---

## 9. Per-commit breakdown (aggregate table)

The campaign is **~77 commits across 8 phases** (post-cert-v3: +1 Phase-A commit for `Program.lean`, +1 Phase-F commit for `lookupFunDecl_total`). Phases A–F (M10.0 – M10.4) are the M10 done condition; Phase G (M10.5) is M11+.

### 9.1 Phase A (M10.0a–k) — 11 commits

| # | Commit title | Risk |
|---|---|---|
| 1 | M10.0a Soundness: scaffold aeneas-lean-soundness Lake package + Mathlib pin | Medium (CI lane setup) |
| 2 | M10.0b Soundness: port LLBCSharpPaper.Syntax (Val#, Place#, RegionAbs) | Low |
| 3 | M10.0c Soundness: port LLBCSharpPaper.State (LLBCState, ctx, abs maps) | Low |
| 4 | M10.0d Soundness: define LLBCSharpPaper.Program (lookupFunDecl etc.) | Low |
| 5 | M10.0e Soundness: port LLBCSharpPaper.WellFormed (+ WellFormedProgram) | Medium |
| 6 | M10.0f Soundness: port LStep — Fig. 3 rules | Medium |
| 7 | M10.0g Soundness: port LStep — Fig. 7+8 rules | Medium |
| 8 | M10.0h Soundness: port LStep — Fig. 11 join rules | High |
| 9 | M10.0i Soundness: port LStep — §5.2 loop rules | Medium |
| 10 | M10.0j Soundness: port Valid predicate | Low |
| 11 | M10.0k Soundness: replace 4 axioms in StepEventSound.lean | Low |

### 9.2 Phase B (M10.1a–e) — 5 commits

| # | Commit title | Risk |
|---|---|---|
| 12 | M10.1a Soundness: define concretise — env + numLocals | Medium |
| 13 | M10.1b Soundness: define concretise — loans + absRegistry | Medium |
| 14 | M10.1c Soundness: smoke lemma concretise_wellFormed_smoke | Low |
| 15 | M10.1d Soundness: concretise inversion lemmas | Medium |
| 16 | M10.1e Soundness: concretise commute lemmas (setLocal/addLoan/takeLoan) | Medium-high |

### 9.3 Phase C (M10.2a–w) — 23 commits

| # | Commit title | Risk |
|---|---|---|
| 17 | M10.2a Soundness: stepPanic / stepRetn soundness | Trivial |
| 18 | M10.2b Soundness: stepMatchArm / stepLoopEnd soundness | Trivial |
| 19 | M10.2c Soundness: stepMove / stepCopy soundness | Low |
| 20 | M10.2d Soundness: stepAssign soundness | Low |
| 21 | M10.2e Soundness: stepAssert soundness | Low |
| 22 | M10.2f Soundness: stepBinop soundness | Low |
| 23 | M10.2g Soundness: stepSharedBorrow soundness | Low |
| 24 | M10.2h Soundness: stepMutBorrow_direct soundness | Medium |
| 25 | M10.2i Soundness: stepMutBorrow_inAbsReborrow soundness | Medium-high |
| 26 | M10.2j Soundness: stepMutBorrow_loopOwned soundness | Medium |
| 27 | M10.2k Soundness: stepEndBorrow_direct soundness | High |
| 28 | M10.2l Soundness: stepEndBorrow_reborrow / shared / lazyExpand soundness | Medium |
| 29 | M10.2m Soundness: stepReborrow soundness | Medium-high |
| 30 | M10.2n Soundness: stepCall soundness (absSig + lookupFunDecl) | High |
| 31 | M10.2o Soundness: stepEndAbs soundness | High |
| 32 | M10.2p Soundness: stepSymExpandMutBorrow soundness | High |
| 33 | M10.2q Soundness: stepLoopInv soundness | Medium |
| 34 | M10.2r Soundness: stepJoin — JoinSame entry soundness | Medium |
| 35 | M10.2s Soundness: stepJoin — JoinSymbolic entry soundness | Medium |
| 36 | M10.2t Soundness: stepJoin — JoinMutBorrows entry soundness | **Highest** |
| 37 | M10.2u Soundness: stepJoin — JoinVar entry soundness | Medium-high |
| 38 | M10.2v Soundness: stepJoin — JoinBottomOther / JoinOtherBottom soundness | Medium |
| 39 | M10.2w Soundness: stepJoin_witnessed_sound (assemble) | Medium |

### 9.4 Phase D (M10.3a) — 1 commit

| # | Commit title | Risk |
|---|---|---|
| 40 | M10.3a Soundness: prove stepEvent_sound by case-analysis on Event | Low |

### 9.5 Phase E (M10.4a–d) — 4 commits

| # | Commit title | Risk |
|---|---|---|
| 41 | M10.4a Soundness: define Initial / Final / borrow_checks# (over LlbcSignature) | Medium |
| 42 | M10.4b Soundness: prove replayFun_event_induct (cc threaded) | High |
| 43 | M10.4c Soundness: prove replayFun_post (exit ↔ paper Final) | Medium-high |
| 44 | M10.4d Soundness: assemble replayFun_sound | Low |

### 9.6 Phase F (M10.5a–c) — 3 commits

| # | Commit title | Risk |
|---|---|---|
| 45 | M10.5a Soundness: prove typecheck_implies_wellFormedInit | Medium |
| 46 | M10.5b Soundness: prove lookupFunDecl_total_of_replayCrate_ok | Low |
| 47 | M10.5c Soundness: prove replayCrate_implies_borrow_checks | Low |

**M10 done at #47.** Remaining = optional Phase G.

### 9.7 Phase G (M10.6a–p) — up to 15 commits, optional

| # | Commit title | Risk |
|---|---|---|
| 48 | M10.6a Soundness: port LLBC concrete syntax (Fig. 2) | Medium |
| 49 | M10.6b Soundness: port ⟶_LLBC reduction | Medium |
| 50 | M10.6c Soundness: port LLBC# → LLBC stripping | Medium |
| 51 | M10.6d Soundness: port Thm 3.1 Confluence | Very high |
| 52 | M10.6e Soundness: port Thm 3.3 LLBC ↔ PL forward sim | Very high |
| 53 | M10.6f Soundness: port Thm 4.1 borrow_checks# ⇒ LLBC-safe | High |
| 54 | M10.6g Soundness: port Thm 4.2 well-formed initial state | Medium |
| 55–61 | M10.6h–n: per-lemma cleanup / golfing | Misc |
| 62 | M10.6o Soundness: assemble cert_implies_pl_safety | Low |
| 63 | M10.6p Soundness: docs refresh (cert-format-and-soundness.md §4–§5 → "proved") | Trivial |

### 9.8 PR-sized bundling

Following the M9.6 plan's §7.4 framing, group commits into PR-sized chunks:

| PR | Commits | Focus | Reviewer load |
|---|---|---|---|
| PR-A1 | #1 (M10.0a) | Lake scaffold | Infra review |
| PR-A2 | #2–#11 | All of Phase A (includes new Program.lean for cert-v3 lookup helpers) | Domain review (paper port) |
| PR-B | #12–#16 | Phase B | Smaller, focused |
| PR-C1 | #17–#23 | Phase C trivial events (7 lemmas) | Pattern lock-in |
| PR-C2 | #24–#28 | mutBorrow + endBorrow splits | Focused |
| PR-C3 | #29–#33 | reborrow / call / endAbs / symExpand / loopInv | The hint-heavy events |
| PR-C4 | #34–#39 | The join lemmas | The hardest PR |
| PR-D-E-F | #40–#47 | Phases D + E + F bundled (includes lookupFunDecl_total) | Crate-level assembly |
| PR-G* | #48–#63 | Phase G (multiple PRs as time permits) | Out of M10 scope |

**Total: 8 PRs for M10** (Phases A–F). Phase G adds another 2–4 PRs.

---

## 10. Gates

The M9.6 campaign's four gates (G1: vertical slice, G2: Direct tests, G3: GeneratedTests, G4: sweep) all stay in force for the **checker** side. The soundness campaign adds three new gates that apply to the **soundness** side.

### 10.1 Gate definitions

| Gate | What it checks | When it runs | Owner |
|---|---|---|---|
| G1–G4 | (M9.6 gates) — checker still green | Every commit | Checker CI |
| **G5: Axiom hygiene** | `#print axioms <key-theorem>` returns *only* the intended trusted base | After every Phase boundary | Soundness CI + orchestrator script |
| **G6: No `sorry`** | `grep -rn 'sorry' aeneas-lean-soundness/AeneasSoundness/Soundness/` returns only docstring history | After every Phase-C/D/E/F/G commit (i.e., commits #17 onward) | Soundness CI |
| **G7: Cycle-time budget** | Soundness `lake build` ≤ 30 min cold, ≤ 5 min warm | Every soundness-side commit | Soundness CI |

### 10.2 G5: Axiom hygiene — exact expected output per phase

The orchestrator script runs `lake env lean --run AxiomCheck.lean` where `AxiomCheck.lean` is:

```lean
import AeneasSoundness.Soundness.StepEventSound
import AeneasSoundness.Soundness.ReplayFunSound
import AeneasSoundness.Soundness.ReplayCrateSound
#print axioms AeneasSoundness.Soundness.stepEvent_sound
#print axioms AeneasSoundness.Soundness.replayFun_sound        -- post-v3: signature carries `cc`+`lookupFunDecl`
#print axioms AeneasSoundness.Soundness.replayCrate_implies_borrow_checks
```

| After phase | Expected axioms for `stepEvent_sound` | Expected axioms for `replayCrate_implies_borrow_checks` |
|---|---|---|
| Phase A | Lean core + `sorryAx` (theorem is `sorry`'d) | (theorem not yet declared) |
| Phase B | Lean core + `sorryAx` | (still not declared) |
| Phase C | Lean core only (no sorry, no `sorryAx`) | Lean core + `sorryAx` (Phase E hasn't run) |
| Phase D | Lean core only | Lean core + `sorryAx` |
| Phase E | Lean core only | Lean core + `sorryAx` (Phase F hasn't run) |
| Phase F (M10 done) | Lean core only | Lean core + **`CertGen_faithful`** + `paper_thm_3_1`, `paper_thm_3_3`, `paper_thm_4_1`, `paper_thm_4_2` (Phase G stubs) |
| Phase G | Lean core only | Lean core + `CertGen_faithful` (Phase G replaced the paper theorems with real proofs) |

The orchestrator commits the expected output as a test fixture (`aeneas-lean-soundness/tests/axioms.golden.txt`); CI diffs against it. A diff is a regression.

### 10.3 G6: No `sorry`

```bash
! grep -rn '\bsorry\b' aeneas-lean-soundness/AeneasSoundness/Soundness/ | grep -v -- '--'
```

Allow `sorry` in:
- Docstrings (preceded by `--` or in a `/-...-/` block).
- Files under `aeneas-lean-soundness/AeneasSoundness/Drafts/` (a scratchpad for in-flight work; never imported by the public modules).

### 10.4 G7: Cycle-time budget

```bash
( cd aeneas-lean-soundness && time lake build )
```

Cold: < 30 min (CI fresh checkout; includes Mathlib download + compile).
Warm: < 5 min (CI with `.lake/` cached; this is what regression-tests run against).

Concrete soft-limits per file:
- `LLBCSharpPaper/Step.lean` (the Fig.3+11 rules): ≤ 60 s warm.
- `Soundness/StepEventSound.lean`: ≤ 120 s warm.
- `Soundness/JoinLemmas/*.lean` (per-`JoinRule` lemmas): ≤ 30 s each.

If a file exceeds its budget by 50%, escalate to `lean4:proof-golfer` for that file. (M9.6's plan §7.4 had a `lake build GeneratedTests` budget; same idea, soundness-side.)

### 10.5 Gate-invocation summary (orchestrator's per-commit checklist)

```bash
# Checker side (M9.6 gates) — unchanged
bash scripts/check-vertical-slice.sh                     # G1
(cd aeneas-lean-checker && for t in tests/Direct/*.lean; do lake env lean --run "$t"; done)  # G2
(cd aeneas-lean-checker && lake build GeneratedTests)    # G3
# (G4 sweep as in M9.6 plan §7.1)

# Soundness side — new
(cd aeneas-lean-soundness && lake build)                 # G7
(cd aeneas-lean-soundness && lake env lean tests/AxiomCheck.lean)  # G5
( ! grep -rn '\bsorry\b' aeneas-lean-soundness/AeneasSoundness/Soundness/ | grep -v '/Drafts/' | grep -v -- '--' )  # G6
```

---

## 11. Risk inventory

### 11.1 Cross-cutting risks

1. **Paper proofs may not transcribe directly to Lean.** Specifically the *join algebra* (cert-format doc §5 step 4 explicitly names this as the hardest case). The paper's join is non-deterministic — Fig. 11 rules can be applied in different orders. The Lean port has to settle on a deterministic application order; the cert's `JoinEntry` constructor + per-rule lemma is the natural choice, but the paper's confluence theorem (Thm 3.1) is what *makes* the choice not matter. Phase G's Thm 3.1 port is what discharges this — until then, the per-`JoinRule` lemma is conditional on a `JoinDeterminisation` axiom. **Mitigation:** treat `JoinDeterminisation` as a Phase-A axiom (in `LLBCSharpPaper/Step.lean`); replace it in Phase G. Phase C lemmas can use it freely.

2. **Mathlib version drift.** The campaign will span months; Mathlib bumps happen weekly. Bumping mid-campaign breaks proofs.
   - **Mitigation:** pin a Mathlib version in `aeneas-lean-soundness/lakefile.lean` at Phase-A commit. Pin file in repo (`.mathlib-pin`). Bumping happens only at phase boundaries, scheduled in a separate PR ("M10.Xa Soundness: bump Mathlib to <commit>; regen proofs"). Between bumps, the pin is frozen.

3. **Soundness theorem reveals an M9.6 or M9.7 hint gap.**
   - Specific anticipated cases: (a) `EvJoin.JoinMutBorrows` does not name the *new* abs's role list (cf. C20 risk above). (b) `EvLoopInv.loanRegistry` gives `(borrowId, parentAbsId)` but not the fixpoint witness needed for paper §5.2 `Ω ≤ Ω'`. (c) `EvCall.absSig` covers `A_in(ρ)` but not `inst_sig`'s region-variable instantiation.
   - **Status post-M9.7**: cert v3 (the M9.7 schema bump) addressed the *(LLBC, cert) binding* gap but did not address (a)/(b)/(c). The open questions §14.1-14.3 (below) still list them; they are now candidates for an `M9.8` micro-bump rather than rolled into M9.7. The schema is already at `fmt_version = 3`; bumping to `4` for any of these is a small, focused commit.
   - **Mitigation:** if (a)/(b)/(c) surfaces in Phase A, fix it as an `M9.8` micro-bump before Phase B starts. If in Phase B, fix before Phase C. If in Phase C, the cost is one revisit of OCaml + cert regen — a 4-day diversion. **Hard rule:** if a gap surfaces in Phase D or later, the gap is *taken to a follow-up M10.X campaign*; the current campaign axiomatises the missing premise and continues. Don't re-open the cert format in mid-Phase D.

4. **LLBC# state representation: extrinsic vs. intrinsic.**
   - Extrinsic: `LLBCState := { ctx, abs, … } ; WellFormed Ω : Prop`. Every theorem carries `WellFormed Ω` as a hypothesis. Easy to define; clutters every signature.
   - Intrinsic: `LLBCState := { ω : RawState // wellFormed_raw ω }`. Well-formedness is an invariant of the type. Cleaner signatures; harder to construct values (every constructor needs a proof).
   - **Recommendation: extrinsic.** It composes better with Aeneas's existing definition style (the replayer's `SymState` is extrinsic). The proof clutter is a fixed cost; not having to plumb proofs through every `LStep` constructor is a much bigger win. Phase A commits this choice.

5. **Build time explodes mid-campaign.**
   - With ~5 kLOC of Phase C proofs, the soundness build can hit Mathlib's per-file timeout (default 60s). Files like `JoinLemmas/JoinMutBorrows.lean` will likely need `set_option maxHeartbeats N`.
   - **Mitigation:** factor every Phase-C lemma into a sibling file (`StepEventSound/MutBorrow.lean`, `StepEventSound/Join/*.lean`, etc.). Per-file build budget of ≤ 90 s warm. Re-run `lean4:proof-golfer` whenever a file blows the budget. (G7 enforces this.)

6. **Loss of `aeneas-lean-checker` CI speed.**
   - If a contributor accidentally adds an `import Mathlib.*` to the checker side, the checker's ~1s build becomes ~30 min.
   - **Mitigation:** `aeneas-lean-checker/lakefile.lean` already documents this. Add a CI check (a simple `grep -r 'import Mathlib' aeneas-lean-checker/`) that fails if anyone tries.

7. **Trusted base creeps.**
   - Without discipline, every stuck proof becomes an axiom.
   - **Mitigation:** G5 enforces an *expected* axiom list. New axioms require explicit user sign-off (a row in `documentation/llbc-sharp-soundness-plan.md`'s trusted-base table). The orchestrator's blocker policy (§13.5 below) makes adding a non-trusted-base axiom a hard blocker.

8. **Concretise's lossy collapse on ADTs (`Val#.opaque`) doesn't compose with the paper's value rules.**
   - Paper's `Val#` is structured (variants/tuples/records as nested `Val#`); we map to `opaque`.
   - **Symptom:** a `LStep` rule that needs to *unpack* a tuple value (e.g., a hypothetical "field-access" rule) has no premise to discharge.
   - **Mitigation:** the events we actually prove sound (no `.proj`, no `.field`) don't unpack values structurally. The `concretise → Val#.opaque` is sound *for the events in scope*. Document the boundary in `LLBCSharpPaper/Syntax.lean` ("for the direct-borrow subset, ADT/tuple/record concretise to `opaque`; rules that introspect those go through `M11`").

### 11.2 Phase-specific risks (recap)

- **Phase A:** region abs representation (extrinsic vs. intrinsic); paper's `inst_sig` (recommend trust via `absSig` hint).
- **Phase B:** `LoanTokenInvariant`'s placement; `absRegistry` may be empty for early loans.
- **Phase C:** join algebra (C20); env-scan invariant in `endBorrow` (C11); `substLocals/Loans` completeness (C16).
- **Phase D:** mechanical — only risk is signature mismatch with Phase C.
- **Phase E:** `Initial`/`Final` correspondence with M9.6 hints; leak-tolerance for `.reborrow`/`.lazyExpand` at function exit.
- **Phase F:** typecheck-side lemma may need strengthening of `Typecheck/Stmts.lean` checks (a checker-side commit, in the M9.6 lane). Defer to a sibling commit if needed.
- **Phase G:** paper port volume — accept that this is a separate sub-campaign; M10 ships without it.

---

## 12. Done conditions

The M10 campaign is done when **all** of the following hold:

1. **No `axiom` in `aeneas-lean-soundness/AeneasSoundness/Soundness/`** other than `CertGen_faithful` (post-M9.7 broadened form — see §0.3) and (until Phase G) the four `paper_thm_*` placeholders. Confirmed by G5 against the golden axiom list.
2. **No `sorry`** in `aeneas-lean-soundness/AeneasSoundness/Soundness/` (G6).
3. **`cert_implies_pl_safety`** is declared (Phase F at minimum; Phase G to fully discharge the paper theorems).
4. **`#print axioms cert_implies_pl_safety`** lists only Lean core + `CertGen_faithful` (post-Phase G) or + `CertGen_faithful` + 4 paper theorems (post-Phase F, pre-Phase G).
5. **All gates green:** G1–G7 on the campaign's final commit.
6. **Soundness CI build ≤ 30 min cold, ≤ 5 min warm** (G7).
7. **Checker CI build still ≤ 1 s** (no Mathlib leak into `aeneas-lean-checker`).
8. **Documentation refreshed:**
   - `documentation/cert-format-and-soundness.md` §4 ("Soundness theorem (sketch)") becomes "Soundness theorem (proved)". §4.5's caveats list shrinks to just the `EvProj` exclusion + M11 future-work.
   - `documentation/llbc-sharp-soundness-plan.md` (this file) gets a `## Status: COMPLETE` banner with a link to the campaign's final commit.
   - A new `documentation/m10-soundness-results.md` (~200 lines) writes up: what's proved, what's trusted, how to read `#print axioms`, what M11+ work remains.
9. **The campaign's progress file** `.m10-soundness-progress.md` shows all commits checked off; no pending blockers; final fixture sweep is 89/89 (or whatever the post-M9.6 baseline is at campaign start).
10. **A release-note commit** `M10 Soundness: end-to-end PL-safety guarantee for replayed certs` tagged on `aeneas-lean-soundness` for `v0.1`.

If Phase G is deferred (recommended), the campaign ships at #45 with the four paper theorems as trusted-base axioms. The donsness banner reads "M10 COMPLETE (Phases A–F; Phase G deferred to M11+)."

---

## 13. Aggregate effort estimate

| Phase | Days | Notes |
|---|---|---|
| Phase 0 (this document) | 1 | Done. |
| Phase A (paper-side surface) | 15–22 | 10 commits; ~3kLOC of definitions. |
| Phase B (concretise + commute lemmas) | 6–10 | 5 commits; ~1kLOC. |
| Phase C (per-event lemmas) | 25–35 | 23 commits; the bulk. |
| Phase D (stepEvent_sound) | 1–2 | 1 commit; mechanical. |
| Phase E (replayFun_sound) | 5–8 | 4 commits; the induction. |
| Phase F (crate corollary) | 2–4 | 2 commits. |
| **M10 total (Phases A–F)** | **55–80 days** | 45 commits. |
| Phase G (paper theorems) | 30–50 | Optional sub-campaign; +15 commits. |
| **Full total** | **85–130 days** | 60 commits. |

**Parallelisation:**
- A2–A4 (3-wide, ~5 d savings)
- C18–C22 (5-wide, ~10 d savings)
- G1–G7 (4-wide, ~15 d savings if Phase G)
- Total speedup with 2–3 parallel agent threads: **~25–35%**. Two-developer M10: ~40–55 days. Three-developer M10: ~30–45 days.

**Calendar:** at ~1 working day per agent-hour (with review overhead, gate runs, escalation cycles), M10 is **3–6 calendar months** of focused work. Phase G doubles that.

---

## 14. Open questions for the user before campaign starts

These are gaps or design choices the M9.6 work didn't anticipate and that this plan flags for explicit user sign-off before the campaign begins. None are blockers if the user picks a default; they are surfaced for transparency.

### 14.1 `EvJoin.JoinMutBorrows` and the missing fresh abs role list

The M9.6 hint `JoinRule.joinMutBorrows (l_left l_right l_fresh : Nat) (abs : Nat)` names the fresh region abstraction id (`abs`) but **does not give the abs's role list**. The paper's `Collapse-Dup-MutBorrow` rule introduces a *fresh* abs with three roles: `borrow^m l_left`, `borrow^m l_right`, `loan^m l_fresh` (cf. cert-format doc:264). The replayer's `stepJoin` currently doesn't allocate the abs in `absRegistry`.

**Status (post-M9.7):** M9.7 was the cert-v3 self-contained-cert redesign and bumped to `fmt_version = 3`. It did not address this gap. The schema is now stable at `3`; closing the gap is an `M9.8` micro-bump.

**Choice for the user:**
- **(A)** Patch as M9.8: add `EvJoin.JoinMutBorrows.absRoles : Array AbsRoleEntry`, bump to `cert_fmt_version=4`. ~6-commit follow-up before Phase C20 lands. **Recommended.**
- **(B)** Trust the cert: `Valid.join_mutBorrows`'s premise stipulates the abs exists in `LLBCState.abs` (i.e., `Ω#.abs[abs]? = some shape ∧ shape.roles = [borrow^m l_left, borrow^m l_right, loan^m l_fresh]`); the cert is taken at its word that the OCaml side created it. Adds an *implicit* trusted-base extension via the broadened `CertGen_faithful` (§0.3).

Both are defensible. (A) is cleaner and the M9.6 surface gets one more piece of metadata; (B) keeps the schema frozen at v3 and shifts the work to a Phase-C trust argument. The plan above assumes (B) (matches "no schema changes mid-campaign"); call out (A) as a recommended M9.8 micro-bump.

### 14.2 `EvLoopInv.fixpointWitness`

Cert-format doc §6.2 already flagged this as a Phase-6 follow-up: `EvLoopInv.loanRegistry` gives loan ids but not the `Ω ≤ Ω'` fixpoint witness from paper §5.2. The campaign assumes the witness can be reconstructed from the rest of the loop body events (loanRegistry + subsequent EvLoopEnd). If reconstruction fails for some cert, Phase C17 (`stepLoopInv_sound`) gets stuck.

**Status (post-M9.7):** Same as 14.1 — not addressed by cert v3; a candidate M9.8 micro-bump.

**Choice for the user:**
- **(A)** Add `EvLoopInv.fixpointWitness : Array (Nat × Nat)` as part of M9.8 (would bump to `cert_fmt_version=4`). Map: invariant-local-id → body-final-local-id. ~3-commit follow-up.
- **(B)** Trust reconstruction and prove it as a Phase-C2 lemma (`reconstruct_fixpoint_witness`); if reconstruction fails for a specific cert, the cert is rejected by the replayer (a new check). This shifts cost from cert format to replayer.

Recommend (A) bundled with 14.1 into a single M9.8 schema bump.

### 14.3 `EvCall.inst_sig`

Cert-format doc §6.2 flag: `EvCall.absSig` covers `A_in(ρ)` but not the `inst_sig`'s instantiation of region variables. Phase C14 (`stepCall_sound`) needs to know how callee lifetimes were instantiated.

**Status (post-M9.7):** Cert v3 makes the callee's structured signature available via `cc.llbcProgram.funDecls` + `lookupFunDecl`, which makes option (B) below much cheaper than it was pre-M9.7 — the callee signature is no longer an opaque RawTy string but a structured `LlbcSignature` with explicit `generics.regions`. The Phase-A lemma to compute `inst_sig` lazily is now pure pattern-matching on structured data.

**Choice for the user:**
- **(A)** Add `EvCall.instSig : Array (Nat × Nat)` (callee region var index → caller abs id). Small schema bump (M9.8).
- **(B)** Compute `inst_sig` lazily from `regionAbs` + `lookupFunDecl cc f`'s signature. Keeps the schema frozen; pays in a Phase-A lemma. **Recommended** (cheaper post-cert-v3 than it was pre-v3).

(B) is what the plan above assumes.

### 14.4 Mathlib pin location

The plan creates `aeneas-lean-soundness/lakefile.lean` with a Mathlib dependency. Two natural placement options:

- **(A)** In-tree: `aeneas-lean-soundness/.mathlib-pin` (a file with the Mathlib commit). Pinned at the same time as `charon-pin`. Bumps go through user review.
- **(B)** Out-of-tree: rely on a global Mathlib cache (`~/.cache/mathlib/<commit>`). Less reproducible across contributors.

Recommend (A). Trivial choice; flag for the user.

### 14.5 Phase G ship-or-skip

This plan recommends **skipping Phase G** for the M10 done condition (the four paper theorems remain trusted-base axioms). Phase G is then a separate M11 sub-campaign. The user should confirm this scoping; if Phase G is required for M10, add ~30–50 days to the estimate.

### 14.6 LLBC# vs. LLBC scope

Phase A above ports LLBC# only; LLBC enters in Phase G. If Phase G is deferred, the campaign never touches LLBC. The user should confirm: it is acceptable for the M10 deliverable to leave the LLBC ↔ PL bridge as an axiom (Thm 3.3), as long as we have:
- a fully Lean-mechanized proof that replayer-accepts → LLBC# borrow-checks (Phase F), and
- a Lean-stated, paper-trusted corollary that LLBC# borrow-checks → PL safe (Phase F's final theorem).

This matches the trust boundary documented at cert-format-and-soundness.md:591-602 ("Established by the Lean proof" vs. "Trusted base"). The proposed M10 done condition is consistent with what the cert-format doc says we'd ship; flag for explicit confirmation.

### 14.7 Audit of the `.shared` borrow case across phases

`SymState.LoanInfo.kind = .shared` is the M9.2 path the M9.6 plan didn't tighten (M9.6 §0.1 explicitly excluded shared-borrow strengthening). The soundness proof has to handle the case anyway — Phase C's `stepSharedBorrow_sound` and `stepEndBorrow_shared_sound` lemmas (commits 22 and 27).

Choice: either we **prove** these in the campaign (likely; they're easy) or we **axiomatize** them as a Phase-A trusted extension. Recommend the former; flagged here only because the M9.6 hint inventory says nothing about shared borrows, and the plan above assumes shared-borrow LStep rules are simple enough to land in Phase A without further M9.6 hints.

### 14.8 `EvProj` revival

The plan firmly excludes `EvProj` (per cert-format doc:431-432: "the replayer rejects it"). If the user wants `EvProj` *inside* M10, this triggers:
- A Phase A extension (new `LStep.proj` constructor; new `Val#.mut_subborrow` / `Val#.shared_subborrow` constructors); ~500 LOC.
- A Phase C lemma; ~300 LOC.
- A new hint family on the OCaml side; a `cert_fmt_version=3` bump.

Total extra: ~1.5–2 weeks. Recommend deferring to M11+. Flagged for user choice.

---

## 15. Document anchors (for orchestrator agents)

The orchestrator and per-phase agents will need exact file:line citations throughout. Anchors:

- M9.6 plan: `/Users/karthik/aeneas/documentation/plans/option-c-implementation-plan.md`
- M9.7 plan (cert v3): `/Users/karthik/aeneas/documentation/plans/cert-v3-implementation-plan.md`
- M9.7 progress (post-campaign state): `/Users/karthik/aeneas/.cert-v3-progress.md`
- Cert format spec: `/Users/karthik/aeneas/documentation/cert-format-and-soundness.md` (§2.1–2.2 rewritten for cert v3)
- Verified-pipeline architecture (cert-self-contains-LLBC narrative): `/Users/karthik/aeneas/documentation/verified-pipeline-architecture.md` (§2 Step 4)
- Skeleton (current state, all axioms): `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Theorems/StepEventSound.lean`
- Cert event vocabulary: `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Raw/CertEvent.lean` (post-M9.7o-E5a: only the dynamic event/hint types; no flat TypeDecl/TraitDecl/FnSignature)
- LLBC program subtree (cert v3 source of static info): `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Raw/LLBCProgram.lean` — `LlbcProgram`, `LlbcFunDecl`, `LlbcTypeDecl`, `LlbcTraitDecl`, `LlbcTraitImpl`, `LlbcSignature`, `LlbcTy`; `CrateCert` lives here too.
- Hint inventory (per-constructor docstrings on `Event`): `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Raw/CertEvent.lean`
- Replayer side: `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/LLBCSharp/Step.lean`, `.../LLBCSharp/Replay.lean`
- State: `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/LLBCSharp/State.lean`
- Values: `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/LLBCSharp/Values.lean`
- Consistency (cert v3 pair check, M9.7h–j): `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Typecheck/Consistency.lean` — `checkLlbcVsCert` is the Phase-F `lookupFunDecl_total` preamble's source of truth.
- Typecheck (for Phase F): `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Typecheck/Stmts.lean`
- Translator (informational; not part of the trust base): `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Translate/Forward.lean` (post-M9.7o-E5b: consumes `LlbcSignature` directly; `rawTyToPTy` and helpers retired)
- OCaml-side LLBC→JSON serializer (the bridge that populates `cc.llbcProgram`; covered by the broadened `CertGen_faithful`): `/Users/karthik/aeneas/src/cert/LlbcJson.ml`
- Project conventions: `/Users/karthik/aeneas/CLAUDE.md` + the linked skill files under `/Users/karthik/aeneas/documentation/skills/`
- Lakefile (checker): `/Users/karthik/aeneas/aeneas-lean-checker/lakefile.lean`

Line numbers are deliberately omitted; the post-M9.7 codebase has churned heavily and file:line citations would rot fast. Per-phase agents should rely on `lean_file_outline` / `lean_local_search` (the lean-lsp-mcp skills) to locate symbols.

---

### Critical Files for Implementation

The 5 files most critical for implementing this plan (in dependency order):

- `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Theorems/StepEventSound.lean` — the four axioms to replace; the soundness theorem skeleton.
- `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Raw/CertEvent.lean` + `Raw/LLBCProgram.lean` — the event vocabulary and the structured LLBC subtree the per-event and per-function lemmas case-analyse / pattern-match on.
- `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/LLBCSharp/Step.lean` — the per-event step relation each `stepXxx_sound` lemma is about.
- `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/LLBCSharp/State.lean` — `SymState`, `LoanInfo`, `absRegistry`; the source side of `concretise`.
- `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/LLBCSharp/Replay.lean` — the event-folding loop that Phase E's `replayFun_sound` induction is over.

Secondary (new files this campaign creates): everything under `/Users/karthik/aeneas/aeneas-lean-soundness/AeneasSoundness/{LLBCSharpPaper,Concretise,Soundness}/*.lean`. The new `LLBCSharpPaper/Program.lean` (cert-v3 lookup helpers) is the campaign-wide glue introduced in §1.1.