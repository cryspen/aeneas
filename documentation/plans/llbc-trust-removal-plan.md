# LLBC-Trust-Removal Plan

This plan describes the staged pathway by which the cert checker
eliminates its trust dependence on the LLBC metadata embedded in
cert files. It picks up after the Phase 2a + Z1 checkpoint and runs
through Z2 → Z3a → Z4a.

> **Status:** Z1 landed (annotation shim only — no trust shift yet).
> Z2/Z3a/Z4a are unplanned-to-execute today; this document records
> the intended sequence and acceptance criteria so the next campaign
> doesn't start from scratch.

---

## Background

### Where trust sits today (post-Z1)

The cert checker reads two things from `cert.json`:

1. **Per-function events** (`cc.functions[i].events`) — a trace of the
   OCaml symbolic interpreter's run.
2. **An embedded LLBC fragment** (`cc.llbc_program`) — function
   signatures, per-local types, source names, ADT/trait/global decls,
   the LLBC statement body.

The M10 soundness theorem (`replayCrate_correspondence` in
`aeneas-lean-soundness/AeneasSoundness/Soundness/ReplayCrateSound.lean:158`)
proves that the events form a valid LLBC# execution and that no
direct loan leaks at function exit. The theorem says *nothing* about
the embedded LLBC fragment. We trust the OCaml emitter to populate
that fragment honestly; if it lied (wrong type in `localsTypes`,
phantom trait impl, etc.) the Rust model would silently diverge from
the source. Soundness is unaffected; correctness of the emitted
model is.

After Z1, every read of `lf.signature` / `lf.localsTypes` /
`cc.llbcProgram.*` / `lf.body` routes through
`aeneas-lean-checker/AeneasCheck/Translate/LlbcTrusted.lean`. The
shim is annotation-only (each accessor is tagged load-bearing or
cosmetic) and a CI grep gate (`scripts/check-llbc-trust.sh`)
prevents new raw reads from sneaking in. Z1's trust shift is exactly
zero; its value is making the surface visible.

### The end state

After Z4a, the cert checker reads only event-derived metadata. The
embedded `llbc_program` field is gone from the format. Trust
collapses to:

* **Charon** — Rust → LLBC (upstream of Aeneas; out of scope).
* **Aeneas cert emitter** (`src/cert/`) — emits an honest trace of
  the symbolic interpreter (today's trust point, unchanged).
* **Lean kernel** — `{propext, Classical.choice, Quot.sound}`.

Removed from trust:
* **The LLBC-metadata path inside the cert** — replaced by self-typed
  events plus a verified consistency check (Z2), the body-fallback
  removal (Z3a), and the type/trait/global-decl carriage migration
  (Z4a).

---

## Z2 — Self-typing cert events

**Problem.** Today's event payloads carry types as opaque OCaml
pretty-printed strings (`EvCall.dst.ty = "(Generated_Types.TAdt ...)"`),
used only for sanity printing. The walker pulls structured per-local
types from `LlbcTrusted.localType` (which reads `lf.localsTypes`).
That field isn't covered by the soundness theorem.

**Goal.** Promote per-event type info from string-form to structured
`LlbcTy`, add a verified `EventTypeConsistency` check that derives a
per-local type map from the events alone, and prove a lemma:

```
eventTypes_consistent cert → typeMapDerived cert = lf.localsTypes
```

After Z2, the walker reads the *derived* type map. `lf.localsTypes`
stays in the cert as an unverified hint that the consistency check
either confirms or rejects — but the load-bearing reads are gone.

### Tasks

#### Z2-1: cert format bump (v7 → v8)

Extend event payloads to carry structured types:

| Event | Today (string) | After Z2 |
|---|---|---|
| `EvAssign` | `dst.ty : String` | `dst.ty : LlbcTy` |
| `EvCall` | `dst.ty : String`, args untyped | `dst.ty : LlbcTy`, `argTys : Array LlbcTy` |
| `EvCopy` / `EvMove` | place untyped | `src.ty : LlbcTy` |
| `EvBinop` | result untyped | `resultTy : LlbcTy` |
| `EvMutBorrow` / `EvSharedBorrow` / `EvReborrow` | place untyped | `placeTy : LlbcTy` |
| `EvSymExpandMutBorrow` | inner untyped | `innerTy : LlbcTy` |
| `EvLoopInv` | env entries untyped | per-entry `LlbcTy` |
| `EvJoin` | witnesses untyped | per-witness `LlbcTy` |

OCaml side: extend `src/cert/CertEvent.ml` constructors, `CertGen.ml`
emit, `CertJson.ml` serializer.

Lean side: extend `AeneasCheck/Raw/CertEvent.lean` constructors,
`AeneasCheck/Json/Parser.lean` parser (back-compat reading v7 as
all-strings — emits warnings but still typechecks).

Roughly the M9.6* / M10.x.0 schema-bump pattern. ~600 LOC across both
sides.

#### Z2-2: `EventTypeConsistency` check (`AeneasCheck/Typecheck/`)

A new checker, run after `checkLlbcVsCert`:

1. Walk events in order, maintaining a `LocalTypeMap : Std.HashMap
   Nat LlbcTy`.
2. For every event that writes a local, compare the event's claimed
   `dst.ty` against the map's current entry (if any). If they
   disagree, fail.
3. For every event that reads a local, compare the read place's
   projected type against the map. Fail on disagreement.
4. On `EvCall`, validate `argTys` against current local types.
5. Output: a sealed `TypedLocalMap` value (a `Std.HashMap Nat LlbcTy`
   wrapped in a structure that carries a proof
   `EventTypesConsistent events`).

#### Z2-3: Soundness lemma

```lean
theorem typeMapDerived_matches_localsTypes
    (cert : CrateCert) (f : FunCert) (lf : LlbcFunDecl)
    (h : EventTypesConsistent f.events)
    (hConsistent : checkLlbcVsCert cert = .ok ()) :
    ∀ i, deriveTypeMap f.events i = lf.localsTypes[i]?
```

Lives under `aeneas-lean-soundness/AeneasSoundness/Soundness/`. The
lemma might be unprovable without strengthening the cert (e.g. it
might be vacuous if `lf.localsTypes` carries types that the events
never touch). Two responses depending on what we find:

1. **If provable:** great. `LlbcTrusted.localType` is rewritten to
   read from `deriveTypeMap` instead of `lf.localsTypes`, and the
   accessor is retagged as `derived (verified)`.
2. **If unprovable:** there's a real trust gap. The cert generator
   either needs to emit a stronger invariant, or the lemma needs to
   be weakened to "subset" (the derived map is a *subset* of
   `lf.localsTypes`, and the walker tolerates missing entries via
   typed-placeholder synthesis).

#### Z2-4: Walker rewires

Update `AeneasCheck/Translate/LlbcTrusted.lean`:

* `localType` is rewritten to read `TypedLocalMap` (the post-Z2-2
  consistency check output) — no longer reads `lf.localsTypes`.
* Trust tag goes from **load-bearing** to **derived (verified)**.
* `signatureOf`'s `inputs[i]` accessor is similarly rewritten — input
  types are the first N entries of the derived map.

### Z2 acceptance

* OCaml: cert v8 emitter passes the in-tree round-trip (every fixture
  re-emits + reloads cleanly).
* Lean: `EventTypeConsistency` passes for every fixture's cert.
* Lean: `typeMapDerived_matches_localsTypes` is `theorem`, no
  `sorry`, no new axioms (golden axiom file unchanged).
* g_rust pass-count unchanged (today: 53 decls / 13 fixtures).
* G7 warm `lake build` budget for both packages stays under 2s.

### Z2 risks

* **Schema bump churn.** Every fixture needs to be regenerated. The
  meta-harness's `--regen-models` flag handles this, but a coordinated
  ratchet (v8 emitter + v8 parser + regenerated cert corpus) is a
  multi-step commit.
* **OCaml side might not have the typed payload available.** The
  symbolic interpreter knows the type of every value it touches; the
  cert emitter just needs to emit it. If a fixture surfaces a place
  the interpreter typed as `Top`, that's a real type-erasure gap we'd
  need to close in `interp/` (could be small, could be large).
* **`lf.localsTypes` might be unverifiable.** If the consistency
  check produces a strictly smaller map than `lf.localsTypes` (because
  some locals are touched by no events — e.g. dead return slots), Z2
  needs to make peace with a "subset" relation. The walker should
  tolerate missing entries; the typed-placeholder path already does.

### Z2 size estimate

Comparable to one M10.x.N axiom-drop campaign:

* OCaml emit: ~300 LOC
* Lean parsing: ~200 LOC
* `EventTypeConsistency` check: ~400 LOC
* `typeMapDerived` derive function: ~300 LOC
* Soundness lemma: ~500 LOC (depends heavily on how cleanly the
  events' write/read pattern factors)
* Walker rewires + LlbcTrusted retag: ~50 LOC
* Cert corpus regen + fixture fixups: ~200 LOC

Total: **~2000 LOC**, **2–4 weeks**.

---

## Z3a — Drop the LLBC body fallback

**Problem.** `Translate/Forward.lean` calls
`propagateRefsFromBlock lf.body` as a post-walk pass that fills in
`vm` slots the event stream dropped (`Forward.lean:3098`). The cert
emitter deliberately drops some Charon-inserted Ref/Use assigns
because they have no semantic content — but the walker still needs
the resulting bindings. Today we recover them by walking
`lf.body` directly. That's a load-bearing read of unverified LLBC.

**Goal.** Have the cert emitter emit the elided binds explicitly as a
new event variant `EvSeed`. The walker consumes `EvSeed` directly; the
`propagateRefsFromBlock` pass is deleted; `LlbcTrusted.bodyOf` is
removed.

### Tasks

#### Z3a-1: `EvSeed` event design

```lean
| seed (dst : Place) (rhs : SymExpr) (ty : LlbcTy)
```

Semantics: "the walker should set `vm[dst.local_] := lookupSymExpr rhs`
as if a synthetic Assign had occurred, but with no operational effect
on the SymState (the OCaml interpreter has already accounted for
this)." The `ty` field is part of the Z2 self-typing surface.

#### Z3a-2: OCaml emit

In `src/cert/CertObserver.ml`, when the symbolic interpreter walks a
statement the cert filter currently drops (Ref/Use), emit an `EvSeed`
event with the relevant place + sym expression instead of dropping
silently. The trace becomes more verbose but more complete.

#### Z3a-3: Replayer step lemma

`stepEvent`'s handling of `EvSeed`: no-op on `SymState` (it's a Lean-
side bookkeeping event). The Lean side just sets the vm slot. Per-
event soundness lemma is trivial: `LStep` for `EvSeed` is `LStepStar
Ω [] Ω` (zero-step refl).

#### Z3a-4: Walker rewires

Delete `Forward.lean::propagateRefsFromBlock`,
`propagateRefsFromStatement`, `propagateRefsFromSwitch`. Delete the
post-walk pass at line 3096-3100. Delete the `LlbcTrusted.bodyOf`
accessor. `lf.body` is no longer read.

#### Z3a-5: Aggregate-array propagation

`propagateRefsFromStatement` also handles the Aggregate-array
rvalue propagation case for empty/multi-element arrays
(`.aggregate (.array _) ops`). Z3a-2 must also emit `EvSeed` for
these so the walker doesn't lose array-literal bindings.

### Z3a acceptance

* g_rust pass-count unchanged.
* `scripts/check-llbc-trust.sh` no longer reports `bodyOf` in the
  shim (the accessor is deleted; reads are zero).
* G6 zero sorrys.
* Cert file size grows ~10-15% (rough estimate based on how many
  Ref/Use the emitter currently drops). Acceptable.

### Z3a risks

* **EvSeed might leak into the verified-soundness proof.** Adding a
  new constructor to `Event` requires extending the per-event lemma
  family (`stepX_sound`). For `EvSeed` this is trivial (no-op), but
  it does mean a `Soundness/StepEventSound.lean` edit.
* **The cert emitter's drop list might overlap with events that *do*
  have operational effect.** Audit `CertObserver.ml`'s filter
  carefully — emit `EvSeed` only for the Ref/Use shapes the walker's
  ref-propagation today recovers.

### Z3a size estimate

* OCaml emit + Lean parse: ~150 LOC.
* Walker pass deletion: -200 LOC.
* Soundness no-op lemma: ~50 LOC.
* Cert corpus regen: ~100 LOC.

Total: **~500 LOC net delta**, **1 week**.

---

## Z4a — Cert carries type/trait/global decls

**Problem.** `LlbcTrusted.typeDecls` / `traitDecls` / `traitImpls` /
`globalDecls` read from `cc.llbcProgram` — the last remaining
load-bearing LLBC-fragment reads. After Z4a, none of these go through
LLBC; the cert carries its own decl tables.

**Goal.** Cert format v9 carries:

* `cert.typeDecls : Array CertTypeDecl` — struct/enum/opaque info.
* `cert.traitDecls : Array CertTraitDecl` — method signatures.
* `cert.traitImpls : Array CertTraitImpl` — impl method bodies.
* `cert.globalDecls : Array CertGlobalDecl` — global names + types.

The `cc.llbc_program` field is removed (or retained as audit metadata
under a different name).

### Tasks

#### Z4a-1: Schema design

The cert's decl tables should be *what the walker actually consumes*
— possibly less than the full LLBC decl tables. Audit:

* For each `LlbcTypeDecl` field, mark whether `Forward.lean`/`Driver.lean`
  reads it. (`name`, `kind` (struct fields / enum variants),
  `generics`, `isTupleStruct`.)
* For each `LlbcTraitDecl` field, same.
* Etc.

The cert version of each decl carries only the read-from-walker
fields plus a `crateName` so qualified-name reconstruction works.

#### Z4a-2: `EventDeclConsistency` check

After Z2's `EventTypeConsistency`, also walk events to verify every
`tAdt id _` / trait-method-call / global-ref references a decl in
the cert's tables, and that the referenced fields match. Output: a
sealed `TypedDeclTables` value.

#### Z4a-3: OCaml emit + Lean parse

Mirror Z2-1's pattern at a larger surface. ~500 LOC OCaml + ~300 LOC
Lean parse.

#### Z4a-4: Walker rewires

`LlbcTrusted.typeDecls` reads from `TypedDeclTables`. Same for
`traitDecls`/`traitImpls`/`globalDecls`. Retag as `derived (verified)`.

#### Z4a-5: Remove `llbc_program` from cert format

Once every consumer is rewired, the `llbc_program` field becomes
write-only (the OCaml emitter keeps writing it for audit; the Lean
checker stops reading it). After a deprecation period, remove from
the OCaml emitter too.

### Z4a acceptance

* g_rust pass-count unchanged.
* `scripts/check-llbc-trust.sh` reports zero raw reads (since the
  shim's accessors all read from `TypedDeclTables` now).
* The cert `llbc_program` field is either gone or marked
  audit-only.
* New soundness lemma:
  `eventDeclsConsistent → typedDeclTables_matches_llbcProgram` — same
  caveats as Z2-3.

### Z4a risks

* **The cert is now self-contained.** Tooling that consumed the
  embedded `llbc_program` for debugging needs the audit-only field
  to stay, or needs a separate `.llbc.json` companion file (back
  to pre-cert-v3 days). Worth deciding before starting.
* **Trait impl complexity.** Trait impls have method bodies, generic
  bounds, super-trait references. The cert tables need enough surface
  to satisfy the walker's trait-emit logic. The `M9.5o` and
  `M9.7o-E5b` trait work in `Driver.lean` is the surface area Z4a
  needs to cover.

### Z4a size estimate

Larger than Z2 because the surface is wider:

* OCaml emit: ~500 LOC
* Lean parsing: ~300 LOC
* `EventDeclConsistency`: ~600 LOC
* `TypedDeclTables` derive: ~400 LOC
* Soundness lemma: ~700 LOC (trait surfaces are gnarly)
* Walker rewires: ~100 LOC

Total: **~2600 LOC**, **4–6 weeks**.

---

## Sequence + dependencies

```
Z1 (annotation shim, done)
   │
   ▼
Z2 (self-typing events)
   │   ─── unlocks: typed dispatch in placeholder synth
   │
   ▼
Z3a (drop body fallback)
   │   ─── parallel-safe with Z4a but cleaner to land first
   │       (smaller surface, validates the EvSeed pattern)
   ▼
Z4a (cert-carries-decls)
   │
   ▼
[end state: cert is self-contained; embedded llbc_program is gone]
```

Z2 must precede Z3a/Z4a because both downstream stages depend on
typed events.

Z3a and Z4a are independent of each other; either order works, but
Z3a is smaller and lower-risk, so it goes first.

---

## Cumulative trust-base diff

| Stage | Trusted today | After |
|---|---|---|
| Z1 (today) | Lean kernel, cert events, embedded LLBC | unchanged (annotation only) |
| Z2 | + verified type-consistency check | per-local types no longer trusted; signatures derived |
| Z3a | + EvSeed events | LLBC body no longer trusted; `propagateRefs` gone |
| Z4a | + verified decl-consistency check | type/trait/global decls no longer trusted; LLBC embed gone |

End state: TCB is `{Lean kernel, Charon, Aeneas cert emitter}` —
strictly smaller than today's `{Lean kernel, Charon, Aeneas cert
emitter, Aeneas LLBC-metadata-into-cert emitter}` (which is
operationally one binary today but logically two trust surfaces).

---

## What this plan does NOT cover

* **Pre-passes into Lean.** Aeneas's pre-passes run upstream of
  symbolic interpretation and are baked into the LLBC input the
  cert emitter consumes. Removing pre-pass trust would require
  either (a) Charon emitting pre-pass-free LLBC plus verified
  pre-passes in Lean, or (b) treating pre-passes as part of the
  trusted Charon → LLBC frontier. Out of scope for this plan; see
  the architecture-sketch discussion preceding the Z1 commit for
  context.
* **Verified emit.** The Rust model emitter
  (`Backends/RustEmit.lean`) stays unverified. After Z4a, the only
  remaining unverified component in the cert-checker is the emit
  layer itself — it consumes a verified `Pure.expr` and produces
  Rust strings. Verifying the emit is the natural next campaign
  (call it Z5), but it's not strictly required for the trust-base
  reduction this plan targets.
* **Aeneas's micropasses.** The architecture sketch from earlier
  mentioned eventually pulling Aeneas's PureMicroPasses into Lean
  for verification. That's a separate campaign (parallel to
  Z2/Z3a/Z4a). Today's pipeline doesn't run those passes at all on
  the cert-checker side, so there's no trust dependency to remove.

---

## Concrete first commit if/when Z2 launches

A single small commit that does *just* Z2-1 (the schema bump's
write side, no consumer):

1. Extend `src/cert/CertEvent.ml`'s `EvAssign` payload to include
   `dst_ty_structured : Generated_Types.ty option` alongside the
   existing string `dst.ty`. (Optional field, back-compat: defaults
   to `None`.)
2. Extend `src/cert/CertJson.ml` to serialize the structured ty.
3. Extend `AeneasCheck/Raw/CertEvent.lean`'s `EvAssign` to parse the
   field if present.
4. Bump `cert_fmt_version` to 8.
5. Re-emit all 89 fixtures' certs.
6. Verify g_rust 53/13 and soundness G5 axiom-golden unchanged.

That's the smallest defensible Z2 step: it lays the schema for the
self-typed events without yet using the typed payload anywhere. The
consistency check (Z2-2) and the soundness lemma (Z2-3) follow in
subsequent commits.

---

## Open questions

These should be answered before Z2 starts:

1. **Should we keep `cc.llbc_program` as audit metadata?** Even after
   Z4a, some users may want to inspect it. Decision affects whether
   the cert format grows or stays the same size.
2. **Can the cert generator emit complete typed payloads today, or is
   the interpreter's typing too lossy?** A pre-flight scan of
   `interp/` should answer this. If lossy, Z2 needs an interpreter
   touch-up first.
3. **Does the cert's `crate_hash` (SHA-256 of the source LLBC file)
   stay or go?** It's currently audit-only; removing it is a tiny
   cleanup but worth a deliberate decision.
4. **Differential testing expansion.** g_rust today covers 53 / 3143
   decls. Z2/Z3a/Z4a don't require more coverage to land, but a
   widening of g_rust coverage in parallel would catch any
   silent-divergence regressions the trust shift introduces.
