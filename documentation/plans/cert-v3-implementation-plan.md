# Cert v3 (M9.7) — Implementation Plan

## Executive summary

This plan stages a single "cert v3" redesign that lands the post-M9.6 cert format ready for the M10 soundness campaign. After M9.7, the cert is a clean two-part document — *a post-pre-pass LLBC program* plus *a symbolic-execution trace over that program* — with the Lean checker enforcing that the two halves agree.

The work bundles four logically separate pieces (Phase E onwards is the *rationalisation* — the part that makes this a redesign rather than a sidecar):

* **Embed** Charon's full post-pre-pass LLBC into the cert via a new `cc_llbc_program` field (replaces the 5-line `<input>.llbc.json` stub).
* **Structural consistency (S)**: the cert's existing redundant metadata (`typeDecls`, `traitDecls`, signature-strings) is pairwise-validated against the embedded LLBC.
* **Referential validity (R)**: each event's local / place / call-target references are validated against the embedded LLBC's function bodies.
* **Rationalise**: redirect the translator to read structured types from `cc.llbcProgram`, retire the hand-written opaque-type-string parsers (`rawTyToPTy` et al.), and delete the now-redundant flat metadata fields.

Total effort: **~16–30 working days**, ~13 commits. The campaign is single-developer-friendly but two of its phases (D and E) are independently parallelisable. After M9.7 lands, the M10 soundness theorem's quantifier domain is a clean `CrateCert` whose program-content is `cc.llbcProgram` (no hybrid).

**Out of scope:** Level T (full per-event type-soundness). That overlaps with what M10's per-rule lemmas prove anyway — duplicating it here would be waste. M9.7 stops at structural + referential agreement; M10 picks up type soundness as part of the soundness theorem.

**Compatibility:** the Lean parser accepts both v2 (post-M9.6) and v3 (post-M9.7) certs through Phases A–D so existing committed fixtures stay valid mid-campaign. Phase E retires v2 acceptance only after every in-tree fixture has been regenerated.

---

## Phase 0 — Audit: what's in Charon LLBC that the cert doesn't capture

Mirrors the Explore-agent findings from the design discussion. The delta drives Phase A's schema.

### 0.1 Per-Charon-type field delta

| Charon type | Cert today | Missing from cert |
|---|---|---|
| `fun_decl` (`charon/src/ast/gast.rs:221`) | `fn_id`, `fn_name`, `signature` (opaque strings), `source_span`, `events`, `final_state`, `pretty_name` | `item_meta.attr_info` (attributes, `#[inline]`, visibility, lang_items), `item_meta.source_text`, `src` (TopLevel/TraitDecl/TraitImpl source context), `is_global_initializer`, `generics.const_generics`, per-local types in body |
| `type_decl` (`charon/src/ast/types.rs:506`) | `id`, `name`, `kind`, `type_params`, `is_tuple_struct`, `source_span`, `qualified_name` | `item_meta.attr_info`, `item_meta.source_text`, `item_meta.lang_item`, `layout` (size/align/discriminant-tag per target), `ptr_metadata`, `repr` (`#[repr(C)]` / `#[repr(align)]` / `#[repr(packed)]` / explicit discriminant type), `generics.const_generics`, `src` |
| `variant` (`charon/src/ast/types.rs:563`) | `id`, `name`, `fields` | `attr_info`, `span` (per-variant), `discriminant` (explicit `Foo = 5` values) |
| `field` (`charon/src/ast/types.rs:581`) | `idx`, `name`, `ty` (opaque) | `attr_info`, `span` (per-field) |
| `trait_decl` (`charon/src/ast/gast.rs:341`) | `id`, `name`, `qualified_name`, `methods`, `source_span` | `item_meta.attr_info`, `item_meta.source_text`, `item_meta.lang_item`, `generics`, `implied_clauses` (supertraits), `consts` (associated constants), `types` (associated types), `vtable` (dyn-compatible vtable struct ref), `src` |
| `trait_impl` (`charon/src/ast/gast.rs:426`) | `id`, `pretty_name`, `qualified_name`, `trait_decl_id`, `self_type_decl_id`, `self_type_var`, `type_params`, `trait_clauses`, `methods`, `source_span` | `item_meta.attr_info`, `item_meta.source_text`, `item_meta.lang_item`, `impl_trait.generics` (trait-ref instantiation), `implied_trait_refs` (parent clauses), `consts` (associated const impls), `types` (associated type impls), `vtable` (dyn-compatible vtable instance ref), `src` |
| `statement` (`charon/src/ast/llbc_ast.rs:91`) | (cert has no per-statement representation; events are coarser) | `span` (per-statement source location), `comments_before`, `id` (statement identity) |

### 0.2 Cert size before vs after

Estimate (pessimistic) based on Charon's `CrateData` schema being 2–5× the cert's current event-trace.

| Fixture | cert.json today | cert.json post-M9.7 (estimate) |
|---|---|---|
| `paper` | ~84 KB | ~250–400 KB |
| `incr_cert` | ~5 KB | ~15–25 KB |
| `hashmap` | ~750 KB | ~2–4 MB |
| `adt-borrows` | ~330 KB | ~800 KB–1.5 MB |

File size growth is the campaign's main downside. Mitigation (gzip / postcard) is a separate flag, not in scope for M9.7.

### 0.3 What the rationalisation deletes

After Phase E (`Translate.translateCrate` reads from `cc.llbcProgram` instead of the flat fields):

* Lean type defs that become unused: most of `aeneas-lean-checker/AeneasCheck/Raw/CertEvent.lean` lines 138–250 (`TypeDecl`, `CertVariant`, `CertField`, `TraitDecl`, `TraitImpl`, `TraitMethodDecl`, `TraitImplMethod`, the embedded `qualifiedName`, `isTupleStruct`, etc.).
* OCaml type defs that become unused: `cert_field`, `cert_variant`, `cert_type_decl_kind`, `cert_type_decl`, `cert_trait_decl`, `cert_trait_method`, `cert_trait_impl_method`, `cert_trait_impl` in `src/cert/CertEvent.ml{,i}` (the rebuilt schema is exactly the cert minus these — the `cc_llbc_program` field carries equivalent info structurally).
* Hand-written parsers in `aeneas-lean-checker/AeneasCheck/Translate/Forward.lean`: `rawTyToPTy` and its helpers (`parseTAdtId`, `parseTAdtGenericTypes`, `extractTRefInner`, the M9.5n depth-aware extractors, etc.) — collectively ~600–800 LOC of fragile opaque-string parsing.
* CLI scaffolding: `aeneas-lean-checker/AeneasCheck/Cli.lean` line 29's `_llbcJson` arg (becomes literally unused; can drop). `scripts/check-vertical-slice.sh`'s `-emit-llbc-json` flag and the LLBC arg to `aeneas-check`.

The cert that remains has only: `fmtVersion`, `crateHash`, `llbcProgram`, `functions[].{fnId, fnName, sourceSpan, events, finalState, prettyName}`. Lean side is comparably trimmed.

---

## Phase A — Schema redesign (Lean)

**Deliverable:** `Raw.CertEvent` and `Json.Parser` accept the v3 cert. v2 still parses unchanged (back-compat) until Phase E retires it.

### A.1 New Lean types

In `aeneas-lean-checker/AeneasCheck/Raw/`, a new file `LLBCProgram.lean` containing Lean-side mirrors of the relevant Charon subtree. Define structured types for:

* `LlbcProgram` — top-level (the embedded `CrateData` projection).
* `LlbcFunDecl` — function declarations with structured signature.
* `LlbcTypeDecl` — type declarations with structured field/variant types.
* `LlbcTraitDecl` / `LlbcTraitImpl` — trait surface.
* `LlbcStatement` / `LlbcRvalue` / `LlbcOperand` — function-body grammar.
* `LlbcTy` — structured types (replacing the opaque string `RawTy`).
* `LlbcPlace` / `LlbcProjElem` — structured places.
* `ItemMeta` — attributes, source-text, lang-item, span.

The shape mirrors Charon's `charon-ml` OCaml types (which mirror Rust's `charon::ast::*`). Lean-side parser walks the JSON one node at a time; no dependency injection.

Initial scope: parse enough to satisfy Levels S + R. Things like `repr_options.align`, `ptr_metadata`, `vtable` we parse as opaque values (record but don't introspect). `LlbcStatement` parses fully (needed for R).

LOC estimate: ~800–1200 in `LLBCProgram.lean`.

### A.2 Schema-level changes on `CrateCert`

Add `llbcProgram : LlbcProgram` (no default — required field under v3). Bump `fmtVersion` acceptance to `{1, 2, 3}` with the v3 path requiring `llbc_program`.

The v2 / v1 paths keep the existing fields. The v3 path ALSO keeps the existing fields during Phases A–D — they're redundant but coexist with `llbcProgram` until Phase E retires them.

### A.3 Sub-phase commits

| # | Commit | What lands |
|---|---|---|
| A1 | `M9.7a Lean: add LlbcProgram + subtree types (LlbcFunDecl, LlbcTypeDecl, LlbcTraitDecl, LlbcTraitImpl, LlbcStatement, LlbcTy, LlbcPlace, ItemMeta)` | `Raw/LLBCProgram.lean` — type defs only, no parser yet. ~1000 LOC. |
| A2 | `M9.7b Lean: parse LlbcProgram from JSON (back-compat default = empty)` | `Json/Parser.lean` extended with `parseLlbcProgram` and friends. Default to `LlbcProgram.empty` when the field is absent (v2 certs). ~400 LOC. |
| A3 | `M9.7c Lean: extend CrateCert with llbcProgram field; accept fmt_version 3` | One-line schema change; parseCrateCert now reads the field. |

Gates: all four green throughout. Lean side parses v2 (empty `llbcProgram`) and v3 (populated) identically for downstream callers.

---

## Phase B — OCaml emitter

**Deliverable:** Aeneas's `-emit-cert` emits a v3 cert with `cc_llbc_program` populated from Charon's serializer.

### B.1 Path of least resistance

Call Charon's existing `CrateData::serialize_to_json` (in `/Users/karthik/charon/charon/src/export.rs`) on the post-pre-pass `crate` value in `src/cert/CertGen.ml`'s `emit` function. Embed the resulting JSON value directly as `cc_llbc_program`.

This requires reachability from OCaml to Charon's serializer. Aeneas's OCaml side uses `charon-ml` (an OCaml binding to Charon). Verify with `grep -r CrateData /Users/karthik/charon/charon-ml/` — if `serialize_to_*` isn't re-exported, add an `external` binding (or call the Rust binary as a subprocess; ugly but works as a fallback).

### B.2 OCaml type for `llbc_program`

Keep it as `Yojson.Basic.t` on the OCaml side — no structured OCaml mirror needed. Aeneas writes; the Lean side parses structurally. This avoids duplicating Charon's `CrateData` schema on the OCaml side.

### B.3 Drop the `-emit-llbc-json` stub

The current 5-line stub at `src/cert/CertGen.ml:528-545` (`write_llbc_json`) is redundant. Delete the flag (`src/Config.ml:65-66`, `src/Main.ml:102`) and the write function. Wire `aeneas-check` to no longer require the LLBC arg.

### B.4 Sub-phase commits

| # | Commit | What lands |
|---|---|---|
| B1 | `M9.7d OCaml: bump cert_fmt_version 2→3; populate cc_llbc_program from Charon CrateData` | `src/cert/CertEvent.ml{,i}` adds the field; `CertGen.ml` calls Charon's serializer. ~150 LOC. |
| B2 | `M9.7e OCaml: drop -emit-llbc-json flag and the 5-line stub file` | `src/Config.ml`, `src/Main.ml`, `src/cert/CertGen.ml`. |
| B3 | `M9.7f Lean: drop _llbcJson arg from aeneas-check CLI; usage string update` | `aeneas-lean-checker/AeneasCheck/Cli.lean`. |
| B4 | `M9.7g scripts: update check-vertical-slice.sh and compare-backends.sh` | Drop the `-emit-llbc-json` invocation and the LLBC-arg passing. |

Gates: G1 green (vertical slice regen'd); G2/G3/G4 green (Lean checker accepts v3 with `llbcProgram` populated and ignores it for now).

---

## Phase C — Level S: structural consistency

**Deliverable:** Lean-side check that the cert's flat metadata fields agree with the embedded LLBC. Mismatches produce a precise error and fail the parse.

### C.1 Per-field checks

In a new module `aeneas-lean-checker/AeneasCheck/Typecheck/Consistency.lean`:

* `cc.typeDecls[i]` vs `cc.llbcProgram.type_decls[j]` for some matching `j`: same `id`, same `name`, same kind (struct/enum/opaque), same field count, same field names, same variant names. Type-string equality on each `cf_ty` (re-run `Print.show_ty`-equivalent on the structured LLBC type and compare strings).
* `cc.functions[i].signature.csig_inputs` vs `cc.llbcProgram.fun_decls[i].signature.inputs`: same length, same `show_ty` string per input.
* `cc.functions[i].signature.csig_output`: same `show_ty` string.
* `cc.traitDecls` vs `cc.llbcProgram.trait_decls`: same length, paired by id, same name + method count.
* `cc.traitImpls` vs `cc.llbcProgram.trait_impls`: same length, paired by id, same `trait_decl_id`, same method count.
* `cc.functions[i].fnId` is a valid key into `cc.llbcProgram.fun_decls`.
* Every `EvCall.fn` event references a valid `FunDeclId` in `cc.llbcProgram.fun_decls`.
* Every `EvMatchArm.adtId` references a valid `TypeDeclId` in `cc.llbcProgram.type_decls`.

### C.2 Where it runs

`replayCrate` invokes the consistency check before the typechecker. The check runs once per cert, not per event — it's a setup-time pairing.

If `llbcProgram` is empty (v2 cert), the consistency check is a no-op.

### C.3 Sub-phase commits

| # | Commit | What lands |
|---|---|---|
| C1 | `M9.7h Lean: Consistency.checkLlbcVsCert — structural agreement (Level S)` | New module + driver-side call. ~400 LOC. |

Gates: all four green. Failed consistency checks are a hard parse error — any in-tree fixture that's inconsistent must be regenerated before C1 ships.

---

## Phase D — Level R: referential validity

**Deliverable:** Lean-side check that each event's references (local ids, place projections, function ids in EvCall) are valid in the corresponding `cc.llbcProgram.fun_decls[i].body`.

### D.1 Per-event referential checks

In the same `Consistency.lean` module, extend with per-event walks:

* `EvAssign dst rhs`: `dst.local_` is bound in the function body; the projection path against `dst.ty` is valid against the declared local type.
* `EvMutBorrow loan place sv ..` / `EvSharedBorrow loan sb_id place sv`: place's root local is bound; projection chain valid.
* `EvCall fn callId fnName args dst region_abs abs_sig`: `fn` is a valid `FunDeclId`; `fn_name` agrees with that decl's name; `args.length` matches the callee's `inputs.length`; `region_abs.length` matches the callee's region-abstraction-group count.
* `EvEndAbs abs ...`: abs id is one of the `region_abs` introduced by a preceding `EvCall`.
* `EvSymExpandMutBorrow svId bid innerSv ...`: `svId` was previously introduced by some event in this function.
* `EvMatchArm scrutinee adtId variantId variantName`: `(adtId, variantId)` is a valid (typedecl, variant) pair in `cc.llbcProgram.type_decls`; `variantName` matches.
* Control-flow well-nestedness: `EvLoopInv` / `EvLoopEnd` are properly nested; `EvAssert` / `EvJoin` pairs balance; match arms are contiguous per scrutinee.

### D.2 Sub-phase commits

| # | Commit | What lands |
|---|---|---|
| D1 | `M9.7i Lean: Consistency — per-event referential checks (Level R, EvCall/EvAssign/EvBorrow)` | First half. ~300 LOC. |
| D2 | `M9.7j Lean: Consistency — per-event referential checks (Level R, control-flow well-nestedness + abs lifecycle)` | Second half. ~300 LOC. |

Gates: all four green. Mismatches between an event's references and the LLBC body fail the parse. This is the moment v2-regression risk peaks: any fixture whose cert + LLBC don't fully agree fails to load. Mitigate by regenerating all fixtures during D, not waiting for the final regen pass.

---

## Phase E — Rationalisation

**Deliverable:** the Lean translator reads structured types from `cc.llbcProgram` instead of parsing opaque type strings; the cert's flat metadata fields are deleted.

This is the largest and riskiest phase. The translator is several thousand LOC of Lean code that consumes `cc.typeDecls` / `cc.traitDecls` / opaque-string signatures throughout. We replace those reads with reads from `cc.llbcProgram`, gated by a config flag during the transition so we can A/B-test parity.

### E.1 Stage 1: parallel code path

In `Translate/Driver.lean` and `Translate/Forward.lean`, add a `useLlbcProgram : Bool := false` parameter. When `true`, every read of `cc.typeDecls` / `cc.traitDecls` / `cc.functions[i].signature` redirects to the structured equivalent in `cc.llbcProgram`. When `false`, the original paths run.

* `rawTyToPTy` is replaced by `llbcTyToPTy : LlbcTy → PTy`, which is straight structural recursion (no string parsing).
* `parseTAdtGenericTypes`, `extractTRefInner`, etc. — all retired in the `useLlbcProgram=true` path; `LlbcTy` already carries the structural info.
* ADT-decl / trait-decl lifting: same `StructDecl`/`EnumDecl`/`TraitDecl`/`TraitImpl` outputs, just sourced from `LlbcTypeDecl`/`LlbcTraitDecl`.

### E.2 Stage 2: parity test on 89-fixture sweep

CI runs the sweep twice — once with `useLlbcProgram=false`, once with `=true` — and diffs the emitted Lean output (or the `TranslatedCrate` value, structurally). Both must produce bit-identical results (modulo whitespace / docstring ordering, which may need tightening).

Any divergence is fixed before stage 3 lands.

### E.3 Stage 3: flip default to `useLlbcProgram=true`

The `=false` branch becomes the back-compat path for v2 certs only (where `cc.llbcProgram` is empty). For v3, the flag is fixed at true.

### E.4 Stage 4: retire v2 acceptance + delete flat fields

`parseCrateCert` rejects `fmt_version=2`. The flat fields (`typeDecls`, `traitDecls`, `traitImpls`, opaque-string signatures, `prettyName`-via-trait-impl) are deleted from `CrateCert`. The OCaml side stops emitting them.

The hand-written type-string parsers (`rawTyToPTy` and helpers in `Forward.lean`) are deleted. The `RawTy` type itself stays (the events still embed type strings in `cp_ty`, though we could later structure those too — out of M9.7 scope).

### E.5 Sub-phase commits

| # | Commit | What lands |
|---|---|---|
| E1 | `M9.7k Lean: Translate.Forward — parallel useLlbcProgram=true path (StructDecl/EnumDecl from LlbcTypeDecl)` | Both paths coexist. ~600 LOC of new structured-source code. |
| E2 | `M9.7l Lean: Translate.Forward — parallel useLlbcProgram=true path (trait + signature)` | Trait/impl + function signatures via structured source. ~400 LOC. |
| E3 | `M9.7m Lean: CI parity test — translator output identical with both flag settings on the 89-fixture sweep` | A test script that runs the sweep twice and diffs output. Land any divergence fixes inline. |
| E4 | `M9.7n Lean: flip useLlbcProgram default to true; reject fmt_version=2` | Default flip; parser rejects v2. |
| E5 | `M9.7o Lean+OCaml: delete redundant cert fields (typeDecls / traitDecls / traitImpls / signature-strings); retire rawTyToPTy and helpers` | The big cleanup. Probably the largest commit by LOC delta (deletions). |

Gates: all four green. The parity test in E3 is the critical hold-back — until that passes, E4 must not land.

---

## Phase F — Regen + docs

| # | Commit | What lands |
|---|---|---|
| F1 | `M9.7p Regen 15 tracked tests/llbc/*.cert.json at fmt_version=3 (cert now contains LlbcProgram; flat fields gone)` | Cert files grow ~3–5×. |
| F2 | `M9.7q Docs: cert-format-and-soundness.md, verified-pipeline-architecture.md, llbc-sharp-soundness-plan.md updated for v3` | Reflects the new shape. |

Gates: extended full sweep at 89/0.

---

## Sequencing & dependencies

```
A1 → A2 → A3 ──► B1 → B2 → B3 → B4 ──► C1 ──► D1 → D2 ──► E1 → E2 → E3 → E4 → E5 ──► F1 → F2
```

Aggregate: **13 commits + 2 docs/regen commits = 15 commits**.

**Parallelism opportunities** (when worktree isolation makes it real):

* A2 (parser code) and B1 (OCaml emitter) touch disjoint files; can run in parallel after A1.
* D1 and D2 touch the same file (`Consistency.lean`); must serialise.
* E1 and E2 touch the same file (`Forward.lean`); must serialise.
* Documentation updates (F2) can run in parallel with the final regen (F1) since they touch separate file trees.

Realistic agent parallelism: ~30% speedup over strict serial.

---

## Gates

Same four as the M9.6 campaign:

* **G1** — `bash scripts/check-vertical-slice.sh`
* **G2** — `(cd aeneas-lean-checker && for t in tests/Direct/*.lean; do lake env lean --run "$t"; done)`
* **G3** — `(cd aeneas-lean-checker && lake build GeneratedTests)`
* **G4** — full sweep `for src in tests/src/*.rs; do ./aeneas-lean-checker/.lake/build/bin/aeneas-check /dev/null tests/llbc/$base.cert.json --out /tmp/$base.lean; done`

All four must be green on every commit. Phase D's regression risk peaks because Level R checks can reject previously-valid fixtures — mitigate by regenerating fixtures inline as D commits land, not waiting for F1.

---

## Risks

1. **Charon-ml binding to `CrateData::serialize_to_*` may not exist.** If `charon-ml` doesn't re-export the serializer, we either add a binding upstream (~1 day, requires a Charon-pin bump) or fall back to invoking the Rust `charon` binary as a subprocess and reading its output. The subprocess fallback is uglier but doesn't block. Investigate before committing to the timeline.

2. **Charon schema drift.** `CrateData`'s JSON shape evolves between Charon releases. Pin `charon-pin` once at the start of M9.7 and don't bump until M9.7 is done. Optionally record a `cc_charon_version` field in the cert (one extra string) so future drift is detectable at parse time. *Recommend doing it.*

3. **Cert file size.** Estimated 3–5× growth. The biggest fixture (`hashmap`, currently 750 KB) becomes 2–4 MB. Not blocking; if it becomes a problem later, a gzip / postcard pass is a separate small fix.

4. **Phase E parity test discovers a translator divergence.** The hand-written `rawTyToPTy` and the structured `llbcTyToPTy` may produce subtly different outputs for some corner case (recursive types, deeply nested boxes, etc.). Each divergence is a debug-and-fix; budget 1–2 days slack in E1/E2 for this.

5. **Phase D's referential check rejects a fixture that was passing under M9.6.** This is the M9.5x-style "tolerated invariant violation" risk — a fixture that worked because the cert checker didn't enforce well-nestedness now fails because it does. Mitigate by regenerating each affected fixture inline; the OCaml emitter is the source of truth.

6. **Reviewer fatigue.** 15 commits is a lot for one campaign. Bundle as: PR 1 = A1+A2+A3 (schema-only), PR 2 = B1+B2+B3+B4 (OCaml emit), PR 3 = C1+D1+D2 (consistency), PR 4 = E1..E5 (rationalisation), PR 5 = F1+F2.

---

## Done conditions

* All 15 commits in the per-commit table landed.
* G1, G2, G3, G4 green on the tip.
* Full sweep is 89/0.
* `aeneas-lean-checker/AeneasCheck/Raw/CertEvent.lean` no longer defines `TypeDecl`, `CertVariant`, `CertField`, `TraitDecl`, `TraitImpl`, `TraitMethodDecl`, `TraitImplMethod` (verify with `grep`).
* `aeneas-lean-checker/AeneasCheck/Translate/Forward.lean` no longer defines `rawTyToPTy` or helpers (`parseTAdtGenericTypes`, `extractTRefInner`, etc.).
* `src/cert/CertEvent.ml{,i}` no longer defines `cert_field`, `cert_variant`, `cert_type_decl_kind`, `cert_type_decl`, `cert_trait_decl`, `cert_trait_method`, `cert_trait_impl_method`, `cert_trait_impl`.
* `<input>.llbc.json` files are gone from the repository (`tests/llbc/*.llbc.json` deleted).
* `cert_fmt_version` is `3`; v2 certs are rejected at parse time.
* `documentation/cert-format-and-soundness.md` reflects the new schema (§2 rewritten).
* `documentation/verified-pipeline-architecture.md` §4's "the cert is bound to the LLBC by hash" is rewritten to "the cert *contains* the LLBC."
* `documentation/llbc-sharp-soundness-plan.md` §0.3 updated to reflect the simpler M10 quantifier domain.
* A `.cert-v3-progress.md` file at repo root shows all 15 commits checked off.

---

## Critical files

### Primary (modified across the campaign)

* `/Users/karthik/aeneas/src/cert/CertEvent.ml{,i}` — OCaml type defs
* `/Users/karthik/aeneas/src/cert/CertJson.ml` — OCaml emit
* `/Users/karthik/aeneas/src/cert/CertGen.ml` — calls Charon's serializer
* `/Users/karthik/aeneas/src/Config.ml`, `/Users/karthik/aeneas/src/Main.ml` — `-emit-llbc-json` removal
* `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Raw/CertEvent.lean` — Lean type defs
* `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Json/Parser.lean` — parser
* `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Translate/Forward.lean` — translator rewrite
* `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Translate/Driver.lean` — driver
* `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Cli.lean` — drop LLBC arg

### Created

* `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Raw/LLBCProgram.lean` — Phase A
* `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Typecheck/Consistency.lean` — Phases C + D

### Reference (read-only)

* `/Users/karthik/charon/charon/src/ast/` — Charon's LLBC AST
* `/Users/karthik/charon/charon/src/export.rs` — Charon's JSON serializer
* `/Users/karthik/charon/charon-ml/` — OCaml binding (verify `CrateData` re-export)

---

## Aggregate effort estimate

| Phase | Days | Commits |
|---|---|---|
| Phase 0 (this document) | 1 | 0 |
| Phase A (Lean schema) | 3–4 | 3 |
| Phase B (OCaml emit) | 2–3 | 4 |
| Phase C (Level S) | 2 | 1 |
| Phase D (Level R) | 3–5 | 2 |
| Phase E (rationalisation — the big phase) | 5–10 | 5 |
| Phase F (regen + docs) | 1–2 | 2 |
| **Total** | **17–27 days** | **17 commits** |

Single-developer, no parallelism. Two-developer parallel with worktree isolation: ~12–18 days.

---

## Interaction with M10 soundness campaign

M9.7 lands before M10 begins.

The M10 plan's `cert-format-and-soundness.md` §3.2 "where the replayer is intentionally weaker than the paper" — the M9.6 work eliminated weakness 1 (region abstractions opaque) and weakness 2 (pragmatic join algebra). M9.7 doesn't directly close weaknesses 3 (EvProj) or 4 (no type checking at replayer level), but:

* Level R consistency *is* a partial type check (well-formedness of place projections, function-id validity). Reduces weakness 4's surface.
* M10's Phase A `LStep` definition becomes simpler because `LLBCState` derives directly from `cc.llbcProgram` (one canonical program source). No "which LLBC?" ambiguity.
* The M10 trusted base shrinks: with the cert containing the LLBC, the "OCaml interpreter trace ↔ this LLBC" pairing question goes away entirely — the cert *is* the LLBC.

**Bottom line:** M9.7 is the natural sequencing predecessor to M10. Land it first; M10's design becomes ~10% smaller and cleaner.
