# Zero-Skip Plan — eliminate `--skip-decl` from the differential harness

**Goal.** Every emitted decl ships into the lake build. No decl is silently
dropped. No expected-failure list exists, because there are no expected
failures.

**Why.** Today the diff harness relies on 22 (now 19 after the audit-cleanup
commit removes 3 mis-skipped) `--skip-decl` flags in
`tests/lean-checker/lean-diff/scripts/run-diff.sh`. Each one silently hides a
broken decl, so:

- We have no signal when a change regresses a hidden decl.
- We have no signal when an unrelated fix accidentally repairs a hidden decl.
- The headline "G_lean passes 8 fixtures" overstates real coverage — those 8
  fixtures contain ~19 decls that are not in the build at all.

The audit at [`skip-decl-audit.md`](skip-decl-audit.md) found these 19
remaining skips cluster into **7 root causes**. This doc sequences the fixes.

## Sequencing principle

Order clusters by `(decls unlocked) / (fix size)`. A one-line emit gate that
unlocks 2 enum decls plus their dependents beats a multi-day walker rewrite
that unlocks 5 fns. Cascade unlocks are real: fixing `CList`'s attribute
gate doesn't unlock anything new on its own, but combined with the recursive
match-arm fix it re-enables `list_nth`, `list_nth_mut`, `list_tail`, `sum`,
`i32_id` — the build can finally see them.

We do **not** try to land the expected-failure manifest first. The audit
counts are small enough (19 decls, 7 clusters) that going directly to fixes
is cheaper than building manifest machinery we'd then retire. If the count
were 100+, the calculus would flip — the manifest is the right shape if zero
is genuinely months away.

## The backlog

Eight ordered steps. Each ends in "run the diff harness; if it passes, drop
the corresponding `--skip-decl` flags from `run-diff.sh`."

### Step 0 — DONE inline (this session)

Removed three stale skips (`demo::choose`, `paper::test_incr`, `paper::choose`)
that the audit caught compiling against the current shim. G_lean still
passes at 275 lines; the decls now ship into the build but are not yet
exercised by any runner. Future regressions will surface as lake build
failures rather than silent skips.

Remaining skips: **19** across `constants` (1), `demo` (12), `paper` (6).

### Step 1 — `@[discriminant isize]` attribute gate (Cluster: `discriminant_isize_attr`) — DONE 2026-05-18

**Actual work:** ~10 min (under estimate). Took option (c) from the plan:
added a no-op `initialize Lean.registerBuiltinAttribute { name := \`discriminant, ... }`
to `RuntimeShim/Aeneas/Std.lean`. Shim now parses `@[discriminant isize]` as a
no-op. Removed `--skip-decl CList` and `--skip-decl List` from `run-diff.sh`.
Diff harness PASS at 275 lines (unchanged — neither enum has a runner vector yet).

**Unlocks:** `demo::CList`, `paper::List` directly. Indirectly unlocks every
decl that pattern-matches on them (currently 5+ decls are blocked downstream).

**Fix surface:** one-line emit gate in `Pure/Pretty.lean`'s `EnumDecl.toLean`.
Mainline emits `@[discriminant isize]` because `Aeneas.Std` declares the
attribute. The mathlib-free `RuntimeShim` does not. Either:

- (a) Add a `--target-shim` CLI flag to `aeneas-check` and gate the attribute
  emit on it. Backward-compatible.
- (b) Drop the attribute unconditionally from `aeneas-check`'s output. Loses
  the discriminant tag in the standard-backend equivalence direction (G_byte
  regresses on these two fixtures), but the attribute is purely informational
  for elaboration.
- (c) Add a no-op `attribute` declaration to `RuntimeShim/Aeneas/Std.lean`
  matching `Aeneas.Std`'s signature. Cleanest. Touches one shim file only.

**Recommend (c).** Estimated work: 15 minutes. Risk: nil (additive shim
declaration).

**Acceptance:** remove `--skip-decl CList` from `run-diff.sh:43` and
`--skip-decl List` from `run-diff.sh:63`. Re-run G_lean.

### Step 2 — `alloc.boxed.Box.new` shim binding — PARTIAL 2026-05-18

**Actual work:** ~10 min. Shim binding added to `RuntimeShim/Aeneas/Std.lean`
(returns `Result α`, treating `Box::new x` as `ok x` to match the emitter's
`do let t ← ...` form). The `alloc.boxed.Box.new` reference now resolves.

**Cascade.** `paper::test_nth`'s body calls both `paper.list_nth_mut` and
`paper.sum` directly. Until Step 3 lands and those unskip, `test_nth` would
fail with `Unknown identifier paper.list_nth_mut` / `Unknown identifier
paper.sum`. So the `--skip-decl test_nth` flag stays for now and is
revisited after Step 3.

**Unlocks:** `paper::test_nth` directly. Possibly other fixtures we haven't
audited yet (`list-borrows`, etc.).

**Fix surface:** add a binding to `RuntimeShim/Aeneas/Std.lean`:

```lean
namespace alloc.boxed.Box
  def new {α : Type} (x : α) : α := x
end alloc.boxed.Box
```

The mainline `Aeneas.Std` provides this; the shim does not. Mainline
treats `Box::new x` as identity at the value layer.

Alternative: have the emitter drop `Box::new` wrappers (mainline's
`tests/lean/Paper.lean:99-101` writes `List.Cons 3#i32 (List.Cons 2#i32
List.Nil)` directly, no `Box.new`). This is more invasive (cert walker
change) and only worth it if `Box::new` shows up in many fixtures with
divergent translations.

**Recommend the shim binding.** Estimated work: 5 minutes.

**Acceptance:** remove `--skip-decl test_nth` from `run-diff.sh:69`. Re-run.

### Step 3 — Recursive match-arm scoping in the forward walker (Cluster: `recursive_match_arm_scoping`)

**Unlocks (cascading):** `demo::list_nth`, `demo::list_nth_mut`,
`demo::list_tail`, `demo::i32_id`, `paper::list_nth_mut`, `paper::sum`. That
is **6 decls** (the audit said 5; `paper::list_nth_mut` falls into the same
cluster).

**Symptom:** for a `match l with | CCons x tl => ... | CNil => ...`, the
emitter swaps the arms and loses pattern bindings. The `CCons` arm emits
`ok ()` and the recursive call (which belongs in `CCons`) lands in `CNil`.

**Fix surface:** the match-arm assembler in
`aeneas-lean-checker/AeneasCheck/Translate/Forward.lean`. Two things to verify
first:
- Are the arms genuinely swapped (variant index off-by-one), or is the bug
  in arm-body assembly (each arm gets the wrong sub-walk's binds)?
- Does the binding loss come from the `payloadBinders` map not being seeded
  for recursive enums?

The audit didn't go deep enough to pinpoint the exact line. **Estimated
work: half a day** (one session of careful walker debugging with a minimal
reproducer, probably `paper::sum` since it has the simplest match).

**Acceptance:** remove `--skip-decl list_nth`, `--skip-decl list_nth_mut`,
`--skip-decl list_tail`, `--skip-decl i32_id` from `run-diff.sh:48-53`
(demo) and `--skip-decl list_nth_mut`, `--skip-decl sum` from
`run-diff.sh:67-68` (paper). Re-run.

### Step 4 — Closure-leak in trait `&mut self` methods (Cluster: `closure_leak_trait_mut_self`)

**Unlocks:** `demo::Counter`, `demo::Std.Usize.Insts.DemoCounter`,
`demo::Std.Usize.Insts.DemoCounter.incr`, `demo::use_counter`. **4 decls**
(the trait, the impl, the impl method, and the user of the impl). The
audit treats the trait `Counter` as cascade-only.

**Symptom:** for `trait Counter { fn incr(&mut self) -> ... }`, the impl
method body is generated as if it returns `Self → Result (Self × (Unit →
Self))` (a forward-and-backward pair) when the trait signature is `Self →
Result Self`. Same root as the existing "closure-everywhere" carry-forward
item — but the trait impl case is worse because the SIGNATURE diverges
from the trait's expected one, so `def DemoCounter : Counter Usize := { ... }`
fails to elaborate.

**Fix surface:** trait-impl signature shaping in
`aeneas-lean-checker/AeneasCheck/Translate/Forward.lean` (and possibly
`Translate/Driver.lean`'s `traitImplOfLlbcTraitImpl`). The translator needs
to consult the trait method's signature when shaping the impl-method body,
not just the impl-method's own LLBC signature.

**Estimated work: half a day to a day.** Needs to land before any
trait-impl-heavy fixture (`traits`, `default`, `defaulted_method`,
`blanket_impl`, ...) can be cleanly wired.

**Acceptance:** remove `--skip-decl Counter`, `--skip-decl
"Std.Usize.Insts.DemoCounter"`, `--skip-decl
"Std.Usize.Insts.DemoCounter.incr"`, `--skip-decl use_counter`. Re-run.

### Step 5 — Loop body emits undefined locals (Cluster: `loop_body_undefined_locals`)

**Unlocks:** `demo::list_nth1`, `demo::list_nth1_loop`,
`demo::list_nth1_loop.body`. **3 decls**, all part of one loop fn.

**Symptom:** the loop-body translator references `s33` / `t3` — locals that
were never bound. The wrapper's return type is `Result T` (the type
variable) when it should be `Result Std.U32` (the concrete type the body
returns).

**Fix surface:** `aeneas-lean-checker/AeneasCheck/Translate/Loops.lean`'s
`buildLoopBody` and `buildTopLevelLoopFn`. Likely two bugs:
- Stale local-index references when the walker emits names from the parent
  scope's vm without rewriting them to the loop-body's binders.
- Loop-state type inference picks a too-general `T` when the body's
  state is concrete.

**Estimated work: half a day.**

**Acceptance:** remove the three `list_nth1*` skips. Re-run.

### Step 6 — Back-closure tail position not wrapped in `ok` (Cluster: `tail_back_closure_wrap`) — PARTIAL 2026-05-18

**Actual work:** ~2 hours. `test_choose` unlocked; `call_choose` deferred
(see BLOCKED subsection below). Net: 1 of 2 decls in the cluster ship.

**`test_choose` fix:** for a Unit-returning function whose `vm[0]` was
written with a back-closure application (an `.app` head with no `.` / `:`
qualifier, not a binop, not a `__cast::` head — the cert walker writes
this when an `&mut`-borrowing helper's effect is dropped at end-of-scope),
discard the tail value via `let _ := <tailE>` and emit `ok ()`. Lives in
`Forward.lean::translateFunWith`, just after the existing tail-placeholder
adjustment for non-Unit ADT returns. The discard is gated on an
`isBackClosureApp` predicate so existing Unit-tail paths (empty trait
bodies, pure qualified calls) stay byte-identical — verified against
`blanket_impl` which remains the lone G_byte-pass trait fixture.

**Bonus:** the same fix incidentally repairs `paper::test_nth`'s tail
shape (it also drops a `(t3_back t4)` at end-of-scope). `test_nth` still
cascade-depends on the Step 3-blocked `list_nth_mut` and `sum`, so it
stays in the skip list for now — but once Step 3 lands, no further fix
will be needed for `test_nth`.

**Decl counts.** Skips: 17 → 16. Removed `--skip-decl test_choose` from
`run-diff.sh:61`. Kept `--skip-decl call_choose` per BLOCKED notes.

#### Step 6 — BLOCKED on `call_choose`

The walker emits `(paper.choose true p p)` for a call whose Rust source
is `choose(true, &mut p.0, &mut p.1)` — the two `&mut`-field args have
been collapsed into the parent tuple `p`. Then `p_post_v : U32 × U32`
(the post-state of the *whole* tuple, not of the borrowed field) is
arithmetic'd as if it were a `U32`. The mainline emit threads each field
separately via an explicit `let (px, py) := p` at function entry, which
makes the call args `px py` and the post-state per-field.

Fixing this requires:
1. Detecting tuple-typed inputs at `translateFunWith` time and
   synthesising a `letPat` destructure binding to seed.
2. Updating `vm` so the field-projected places resolve to the
   destructured locals (not back to the parent tuple).
3. Plumbing through to the call-args resolver (`lookupSymExpr`
   chain) so `EvCall`'s `args.map (lookupSymExpr ...)` produces the
   destructured names, not the tuple.
4. Threading the post-state back from the destructured slots, and
   rebuilding the return value from those slots.

That's a multi-day walker change touching `Forward.lean`,
`Loops.lean`, and probably the `WalkState` shape itself. Well outside
Step 6's 2-4 hour scope. Suspected to share root with Step 3
(recursive match-arm scoping) and Step 4 (closure-leak trait `&mut
self`) — all three are walker-shaping bugs where the cert event
stream's "post-state per place" model doesn't line up with what the
emitted Lean wants. Recommend bundling into a deeper walker session
alongside Steps 3-5 rather than narrow-fixing here.

**Acceptance (revised):** removed `--skip-decl test_choose` from
`run-diff.sh:61`. Kept the remaining `paper` skips (`list_nth_mut`,
`sum`, `test_nth`, `call_choose`).

### Step 7 — `use_v` generic-global arity mismatch (Cluster: `use_v_arity`) — DONE 2026-05-18

**Actual work:** ~1.5 hours. Audit's assumption that `V.LEN` was shimmed
was wrong — `V.LEN` is locally emitted under `namespace constants`. The
real bug had three layers:

1. **`Decl` had no const-generic binder slot.** `use_v` and `V.LEN`
   both have a const-generic `N`; the emitter only carried
   `typeParams` so neither signature bound `N`, even though the seed
   pass already emitted `(constants.V.LEN T N)` referencing it.

2. **At the call site, `T` was passed positionally as an explicit
   arg.** With `V.LEN`'s emit-time signature `{T : Type} (N : Std.Usize)`,
   `(V.LEN T N)` mis-applied `T` to the const-generic slot. Lean
   reports `T has type Type of sort Type 1 but expected Usize`.

3. **`V.LEN`'s def landed *after* `use_v` in the namespace.** The cert
   stream's source order had `use_v` first; the topo-sort in
   `LeanEmit.lean::topoSortCallerDecls` looks up call-head names in
   the sibling-decl index, but my `@`-prefix on the call head broke
   the lookup (sanitised head was `@constants.V.LEN`, the index has
   `V.LEN`).

**Fix surface (one commit, four files):**

- `Pure/Syntax.lean::Decl` — added `constParams : Array String := #[]`.
- `Pure/Pretty.lean::Decl.toLean` — emit `(N : Std.Usize)` after the
  implicit type binders. Empty for the 99% of fixtures without const-
  generics, so byte-identical fixtures stay byte-identical.
- `Translate/Forward.lean::translateFunWith` — populate
  `constParams := lsig.generics.constGenerics`.
- `Translate/Forward.lean::buildGlobalGenericCall` — when type-args are
  non-empty, prefix the call head with `@` so the callee's implicit
  `{T : Type}` binder takes the type-arg explicitly. (For globals
  without type-args, `@` is omitted so the byte shape stays unchanged.)
- `Pure/Pretty.lean::PExpr.calledNames` — strip a leading `@` from
  the call head before sanitising, so the topo-sort recognises the
  call as in-crate and reorders `V.LEN` before `use_v`.

**Decl counts.** Skips: 16 → 15. Removed `--skip-decl use_v` from
`run-diff.sh:34` (the only `constants` skip — the fixture is now
fully shipped). Gate-level deltas: G_lean stays at 275 lines (no
runner vector added for `use_v` yet); G_byte stays at 3 pass; G_rust
stays at 44.

**Acceptance:** removed `--skip-decl use_v` from `run-diff.sh:34`.

## Total estimate

Step | Decls | Estimated work
---|---:|---
1. Discriminant attribute | 2 | 15 min
2. Box.new shim | 1 | 5 min
3. Match-arm scoping | 6 | half day
4. Closure-leak trait | 4 | half-to-full day
5. Loop body locals | 3 | half day
6. Tail back-closure wrap | 2 | 2-4 hours
7. use_v arity | 1 | 1 hour
**Total** | **19** | **~3 working days**

This is the entire backlog. After step 7, `run-diff.sh` has no
`--skip-decl` flag anywhere, every decl in every wired fixture ships into
the lake build, and the headline "N fixtures pass" reflects real coverage.

## What this plan does not do

- **It does not wire in new fixtures.** Once a cluster is fixed, future
  Phase-2 wire-ins (`traits`, `loops-issues`, etc.) benefit from the same
  fix but don't need their own special-casing. Fixture wire-in is a
  separate workstream.
- **It does not address the meta-harness work.** Building a project-agnostic
  harness (see [`meta-harness-contract.md`](meta-harness-contract.md)) is
  orthogonal. A meta-harness with skips is still dishonest; a hand-curated
  harness without skips is honest. The two questions sit on different axes.
- **It does not solve the G_byte divergences.** Many decls compile under
  the shim but byte-diverge from mainline (param naming, paren style,
  decl ordering, etc.). G_byte is a separate gate with separate fixes.

## Operational note

Each step ends with a regen + re-run of the G_lean harness. If a step is
supposed to unlock N decls but the lake build still fails on one of them,
that's a sign the audit's failure-class classification was wrong for that
decl and a fresh round of `lake build +{fixture}` is needed to identify
the remaining root cause. Update this doc rather than silently re-adding
the skip flag.
