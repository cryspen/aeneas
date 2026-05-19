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

### Step 3 — Recursive match-arm scoping in the forward walker (Cluster: `recursive_match_arm_scoping`) — PARTIAL 2026-05-18

**Actual work:** ~3 hours. `demo::list_nth` and `paper::sum` unlocked. The
other five decls in this cluster (`demo::list_nth_mut`, `demo::list_tail`,
`demo::i32_id`, `paper::list_nth_mut`, `paper::test_nth`) all turned out to
be blocked by *pre-existing* emit gaps that the cluster-3 fix exposed but
doesn't resolve — see BLOCKED subsection below.

**Root cause (now confirmed):** Charon emits match-arm events in two
distinct layouts:

- *Interleaved* (`list_tail`-style): `[matchArm A][body A][matchArm B][body B]`.
  The pre-existing walker handles this correctly.
- *Grouped* (`sum` / `list_nth*` / `list_nth_mut`-style): `[matchArm A]
  [matchArm B][body B][body A]` — markers all up front, bodies trailing in
  *reverse* variant-id order. The pre-existing walker collapsed each arm's
  range to `(marker_i+1, marker_{i+1})`, which made arm 0 an empty body
  (emitted `ok ()`) and arm 1 inherit the entire residue. That's the
  audit's "swap" report.

**Fix (Forward.lean):** three coordinated changes.

1. **Layout detection + re-slice** (lines around 1727-1855): after the
   pre-existing `collect` produces armsRaw, detect the grouped layout (every
   arm except the last has an empty `(start, endIdx)` range) and partition
   the trailing event stream by *top-level* terminators (`EvReturn` /
   `EvPanic`, with `findBranchEnd` used to skip past Assert-pair if/elses).
   Assign body chunks to markers in reverse marker order. The new
   `lastEnd` for the parent walk is the max `endIdx` across arms (chunk
   order ≠ marker order).
2. **Variant-binder seeding** (around `variantFieldBinderName` +
   `seedGlobalRefsFromStatement`): when the seed pass sees an
   `Assign localK ← Ref(scrut.[Deref, Field _ (some vid) fIdx])`
   statement, prefer the binder name (`localsNames[localK]` if set, else
   synthesized `xL`) over propagating the scrutinee's pure value. Without
   this the body emitted `(paper.sum l)` (the inherited scrutinee) instead
   of `(paper.sum tl)`.
3. **Pattern-slot ↔ body alignment** (`collectVariantBinders*` family +
   `WalkState.variantBinders`): build a `(vid, fIdx) → binderName` map
   from the LLBC body so the match-arm walker's `binderName` picks the
   *same* name the seed pass used. This handles
   `demo::list_nth_mut`-shaped functions where Charon injected MIR temps
   before the named binders, so the K-th binder isn't at `numParams+1+K`.

Plus two tail-fixes for the new sub-walks:

4. **Panic-arm tail** (around line 1956): when an arm body contains
   `EvPanic`, emit `error panic` (RuntimeShim's `Result.error`
   constructor) instead of inheriting the parent's `vm[0]` — fixes
   `| CNil => ok x` (where `x` isn't bound in CNil) → `| CNil => error
   panic`.
5. **Call-as-tail heuristic** (`pickBranchTail` in the Assert-pair
   handler + the arm-walker's `tailRaw`): when a sub-walk doesn't write
   to `vm[0]` and `lastWrite` points to a fresh local introduced in this
   sub-walk (not present in the parent's `vm`), use `vm[lastWrite]` as
   the tail. Fixes `list_nth`'s `else` branch where Charon elides
   `Assign local 0 ← Move t_call_dst` after a tail-call.

**Acceptance:** removed `--skip-decl list_nth` (demo) and `--skip-decl sum`
(paper) from `run-diff.sh`. G_lean passes 275 lines byte-identical. G_byte
pass count unchanged at 3. G_rust still at 44.

**BLOCKED (not Step 3 root):**

- `demo::list_nth_mut`, `paper::list_nth_mut`: now emit the right CCons
  body but the surrounding `ok (match ...)` wrap is wrong (the back-
  closure-returning fn's outer wrap should be `match l with | ... | ...
  => fail panic`, not `ok (match ...)`). Pre-existing back-closure-emit
  issue.
- `demo::list_tail`: CCons body correct; CNil arm emits `ok l, fun ret =>
  l)` for the identity-back-closure shape — pre-existing closure-tail
  rendering issue (same family as `paper::test_choose` from Step 6).
- `demo::i32_id`: not a match at all. Pre-existing dropped-recursive-call
  issue (the recursive call result is bound to `t3` then the tail returns
  the never-bound `t3`).
- `paper::test_nth`: cascade — depends on `list_nth_mut`, which stays
  skipped.

**Walker scaffold:** `aeneas-lean-checker/tests/Walker/match_arm_scaffold.py`
runs `aeneas-check` against the seven decls and asserts cluster-3-shape
substrings. Reusable for follow-up clusters that touch the same
match-arm/branch machinery.

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

### Step 5 — Loop body emits undefined locals (Cluster: `loop_body_undefined_locals`) — PARTIAL 2026-05-18

**Actual work:** ~2 hours. Wrapper-signature half of the cluster shipped;
the loop-body half (architectural mismatch — see below) is deferred. Net:
0 of 3 decls unlock in this commit, but the typeParams + tdm fix is
prerequisite groundwork for the body rewrite that will unlock all 3.

**Unlocks:** `demo::list_nth1`, `demo::list_nth1_loop`,
`demo::list_nth1_loop.body`. **3 decls**, all part of one loop fn.

**Symptom:** the loop-body translator references `s33` / `t3` — locals that
were never bound. The wrapper emits `(l : Std.U32)` (the catch-all
placeholder) where the oracle has `(l : CList T)` and is missing the
`{T : Type}` binder line entirely.

**Fix surface:** `aeneas-lean-checker/AeneasCheck/Translate/Loops.lean`'s
`buildLoopBody`, `buildLoopWrapper`, `buildTopLevelLoopFn`, and
`translateLoopFun`. Two independent bugs:

1. **tdm + typeParams not threaded.** `translateLoopFun` built a local
   `tdm := {}`, so every ADT-typed input fell through to
   `llbcTyToPTyWithVars`'s `Std.U32` catch-all; the three Decl records
   omitted `typeParams`, so the renderer dropped the implicit
   `{T : Type}` binder. **Fixed in commit `a51913d6` (this commit).**
   `tdm` now flows from `Driver.translateCrate`'s
   `buildTypeDeclMapFromLlbc` call into `translateLoopFun`, and
   `typeParams := lsig.generics.types` propagates into all three
   emitted Decls.

2. **buildLoopBody assumes the wrong body shape.** The current design
   expects `[setup events] EvAssert(c, true) [continue body]
   EvAssert(c, false) [break body]` — a flat conditional, modelled
   after the M12.1 `count_to` fixture. But `list_nth1_loop`'s body is
   match-then-branch: `[EvMatchArm CCons] [setup + asserts + recurse]
   [EvMatchArm CNil] [EvPanic]`. The match-arm walker in
   `Forward.lean::walkEvents` consumes the entire match before
   `findBodyBranch` ever sees the asserts, so the cond falls back to
   `lookupSymExpr` on a bare `SymVal 33` (renders as `s33`) and the
   cont/done payloads default to `()` (because no state-local is
   tracked through the arm sub-walks). **Not fixed in this commit.**
   The repair is a buildLoopBody rewrite — likely: walk the body as a
   normal function expression, then rewrite the recursive self-call
   into `cont <args>` and the function's `Return v` into `done v`.
   Out of scope here.

**Scaffold:** `aeneas-lean-checker/tests/Walker/loop_body_scaffold.py`
shipped alongside the typeParams fix. Asserts the wrapper /
top-level signature shape (now passing) and the body's absence of
`if s33` / `ok t3` (still failing, single remaining assertion).

**Acceptance for partial:** scaffold passes 8/9; the wrapper-signature
shape on `list_nth1` / `list_nth1_loop` / `list_nth1_loop.body` now
matches the oracle. Skip list unchanged because the broken body
prevents the whole 3-decl chain from elaborating.

**Acceptance for full (deferred):** remove the three `list_nth1*` skips
and re-run after the buildLoopBody rewrite.

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

## Relaunch session — 2026-05-19 (PARTIAL)

Followed `prompts/zero-skip-relaunch-prompt.md`. Worked Cluster A
infrastructure plus two opportunistic fixes. Net result: c_lean
per-fixture **25 → 30** (+5); per-decl **146 → 329** (+183).

Commits, in order:

1. **`ebd0ea6d`** — Cluster A keyword escape extended to record-literal,
   field-access, and struct-update emit sites. `0195f149` had covered
   only struct *declarations*; this commit adds the four use sites where
   `{ start := …, end := … }` was producing the keyword-cascade parse
   error. Unlocks `issue-807-missing-symbolic-value`. (+1 fixture,
   +100 decls.)

2. **`68ba7969`** — Cluster A stdlib shim layer. Three coordinated
   changes:
   * `sanitizeCallName.pickType` recognises `[T]`/`[T@N]` (→ `Slice`)
     and `[T; N]`/`[T@N; C@N]` (→ `Array`) brace-inner forms so
     `core::slice::{[T]}::len` → `core.slice.Slice.len`.
   * `sanitizeCallName` strips leading `@` for SINGLE-segment names
     so Charon's builtin intercepts (`@ArrayIndexShared`,
     `@ArrayToSliceShared`, etc.) elaborate as plain idents instead
     of explicit-args forms that mis-bind the first arg to the
     implicit type slot. Multi-segment `@constants.V.LEN` (Step 7's
     explicit-args form) is intentionally preserved.
   * `RuntimeShim/Aeneas/Std.lean` gains top-level abbrevs
     `ArrayIndexShared`/`ArrayToSliceShared`/etc., the
     `core.slice.Slice.len` binding, `core.option.Option.unwrap`/
     `is_none`/`is_some`, and universal-instance `class Clone`/
     `PartialEq`. Infrastructure-only — no fixture flips on its own.

3. **`ef66babc`** — Extended shim stubs for the post-Cluster-A
   missing-identifier bulk probe. Adds `Aeneas.Std.U128`/`I128`/`Range`
   plus stubs for `core.slice.index.Slice.{index,index_mut}`,
   `core.slice.Slice.{get,get_mut,chunks_exact}`, `core.slice.iter.*`,
   `core.iter.adapters.step_by.StepBy.next`,
   `core.iter.range.Range.next`, `core.array.Array.*`,
   `core.clone.impls.{bool,U32,U64,I32}.clone`, `core.mem.replace`,
   `core.ptr.null`, `core.convert.T.{into,from'}`, `core.num.U32.*`,
   `core.fmt.*`, `std.io.stdio._print`, `alloc.vec.Vec.*`,
   `alloc.boxed.Box.{deref,deref_mut,as_mut}`. Plus the missing
   bare-int macros `#u8`/`#u16`/`#u64`/`#i8`/`#i16`. Two fixtures
   flip: `builtin-auto`, `print`. (+2 fixtures, +45 decls.)

4. **`1a92b31b`** — `adt` collision fix: when an inherent-impl method
   `def Struct.field` would collide with the auto-generated structure
   projection `Struct.field`, rename to `Struct.impl.field` (mirroring
   mainline's shape). The driver builds a `struct-name → field-set`
   map, computes the rename map, applies it to both the def header
   (`nameOverride`) and call sites (`allCalleeRenames`). Unlocks
   `adt`. (+1 fixture, +5 decls.)

5. **`4a08e607`** — Make `Range.start` default-valued so a RangeTo-
   style `s[..k]` emit (`Range { «end» := k }` with no `start`)
   elaborates. The cert pipeline drops the literal-zero `start` for
   `RangeTo` syntactic sugar; the shim adds an Inhabited-derived
   default that fills the slot at use time. Unlocks `range`.
   (+1 fixture, +33 decls.)

### What stopped progress

Of the remaining 59 failing fixtures, none has a single-error or
two-error profile that yields to a focused shim or one-line emit
fix. Common remaining patterns and their roots:

* **`Application type mismatch`** in 17+ fixtures — the cert
  walker's per-local type tracking is wrong (the `paramName` /
  `lookupSymExpr` chain returns an arg with the wrong inferred type,
  often a fallback `Std.U32` or the parent place's type when the
  borrow-projected field's type was expected). Same family as the
  Step 4 trait closure-leak; needs the trait-method-signature
  threaded through `translateFunWith`'s retTy/body shaping.
* **`Unknown identifier xN` / `xN_post`** in 6+ fixtures — uninitialised
  local references. The translator's seed pass missed the local; the
  body references it as `x1` / `t3` / `x1_post`. Same family as the
  Step 3 / Step 5 walker scoping bugs.
* **`Unknown identifier i`** in loop bodies (3 fixtures, all match-
  bearing) — Step 5's `loop_body_undefined_locals` cluster, the
  half-rewrite that was deferred.
* **`failed to synthesize instance`** (`joins`, etc.) — nonsensical
  `HAdd U32 Enum`-style errors from type-tracking bugs.

Each of these requires multi-hour translator work. The relaunch
prompt's 2x-estimate stopping rule for cluster overrun applied: the
Step 4 trait closure-leak in particular hits `paper`, `demo`,
`traits`, `default`, `defaulted_method` and is the highest-leverage
remaining target.

### Carry-forward for next session

* **Cluster B / Step 4 (closure-leak trait `&mut self`).** Pre-
  requisite: read `Translate/Forward.lean::translateFunWith`'s
  `retTy` construction and find where it differs from the trait's
  declared method signature. The trait declaration is in
  `Pure.Syntax.TraitDecl.methods[k].ty`; need to thread it through
  the impl-method body translation. Likely 1 day of work; unlocks
  4 demo decls + several trait-impl-heavy fixtures.

* **Translator-side fix for `xN_post` / `xN` uninitialised locals.**
  Probably easier than Cluster B — the translator's seed pass needs
  to also seed `<paramName>_post` slots. Several fixtures (`drop`,
  `issue-803-self-in-array`, `arrays_defs`) would flip with this.

* **Loop-body match-bearing fix (Step 5 second half).** Already
  scoped in `prompts/zero-skip-step-5-loop-body-prompt.md`.

* **The remaining 16 `Application type mismatch` fixtures.** Most
  share a root with Step 4 — once the trait-method-signature
  plumbing exists, the per-local type tracking should fall into
  place.

### Gate snapshot at session close

```
c_lean per-fixture: 30 / 89 (was 25)
c_lean per-decl:    329 / 3143 (was 146)
g_byte:             3 pass (unchanged)
g_rust:             44 hand + 42 auto = 86 (unchanged)
diff-harness:       PASS at 275 lines byte-identical
```

## Translator-fixes session — 2026-05-19 (in progress)

Followed `prompts/zero-skip-translator-fixes-prompt.md`. Cluster D /
emit-shape bugs.

### Bug 5 — Option / String type-emit gap → DONE (`249de0e9`)

Three coordinated changes:
* `Json.Parser`'s `Adt { id = Builtin "Str" }` branch now returns
  `LlbcTy.tStr` (was `.tOpaque "Builtin(Str)"`).
* `Forward.lean::llbcTyToPTyWithVars` lowers `.tStr` to
  `.adt "String" #[]` so the param renders as Lean's builtin `String`.
* The seed accumulator's `vm` is pre-populated with input names so
  `seedGlobalRefsFromBlock`'s `Ref(localRef.deref, _)` propagation
  branch can carry input names through to borrow temps. Without this,
  `options::test_expect` resolved arg 2 (a `&msg` borrow at local 4)
  through `lookupPlace`'s vm[1] fallback, emitting `expect x x`.
* RuntimeShim `Option.is_none`/`is_some` wrapped in `Aeneas.Std.Result`.

c_lean per-fixture: 30 → 31. Per-decl: 329 → 336. Unlocks `options`.

### Bug 3 — Loop body second half (stateless loops) → DONE (`7b17d790`)

When `inferStateLocals` returned an empty list (state-less loops like
`mini_tree::explore`, `issue-270::foo`), the emit had two interrelated
errors: `ControlFlow () Unit` had `()` (unit *value*) where Lean
expected a type, and the body's tail emitted bare `cont i` referencing
an unbound `i`.

`Loops.lean::buildLoopBody`/`buildLoopWrapper` now synthesise a virtual
single-state slot `(i : Unit)` whenever `stateLocals.isEmpty`. Body
takes the extra param so it fits the
`loop : (α → Result (ControlFlow α β)) → α → Result β` signature; the
`ControlFlow Unit β` type renders correctly; `cont`/`done` tails carry
a unit value `()`. Wrapper stays state-less at the user-visible API
level (the unit state is internal).

c_lean per-fixture: 31 → 34. Per-decl: 336 → 349. Unlocks
`issue-134-loop-shared-borrows`, `issue-270-loop-list`, `mini_tree`.

### Bug 2 — Uninitialised local refs → DONE (`ea6b5d89`)

Two coordinated fixes:

1. `buildTopLevelLoopFn` was dropping `preSt.binds` on the floor. The
   pre-loop walk emits monadic bindings (e.g. `let x1_post ← Slice.len
   s` in `drop::fill`) whose results feed into the wrapper call's args.
   Thread `preSt.binds` through `assembleBody`.

2. New `propagateRefsFromBlock` post-walk pass over the LLBC body. The
   cert event stream often flattens away Charon's `Assign(localTgt,
   Ref(localSrc.deref, _))` borrow chains; the LLBC body still carries
   them. Re-walking with the post-event-walk vm propagates
   `vm[localSrc]` (typically a call result like `t0`) into
   `vm[localTgt]`. *Fill-only* — never overwrites event-walker values.

c_lean per-fixture: 34 → 35. Per-decl: 349 → 449. Unlocks `drop`.

### Bug 1 — Trait `&mut self` impl-method shape → DONE (`169ca529`)

`traitDeclOfLlbcTraitDecl` built the trait method's return type as
`buildArrow (.result retInner) inputs` with raw output, producing
`Counter::incr : Self → Result Std.Usize` — but the matching impl uses
`backSigOfLlbcWithVars + emitRetTy` to reshape `&mut self -> usize`
into `Self → Result (Std.Usize × (Unit → Self))`. The trait/impl
signature diverged.

Switch the trait declarator to the same BackSig pair. No fixture flips
on its own — `demo`, `traits`, `default`, `defaulted_method`,
`blanket_impl` still fail downstream Bug 4 type-tracking errors —
but the structural mismatch is resolved.

c_lean per-fixture: 35 → 35 (deferred unlocks pending Bug 4).
c_lean per-decl:    449 → 449.

### Bug 4 — Per-local type tracking → PARTIAL (`3ec15a2e`)

The largest cluster (`Application type mismatch` in 15+ fixtures
plus `failed to synthesize HSub U32 Enum`-style errors). Symptoms
include:
* `static::read`: `Slice.index_usize x1 i` with `x1 : S` (generic
  param) instead of `x1 : Slice U16` — trait-bound resolution at the
  call site needs to consult the trait method's signature.
* `joins::use_enum`: `x + e` where `x : U32` and `e : Enum`.
* `joins::call_choose`: `let t0 ← b + 1#u32` where `b : Bool`.

This session only added shim stubs (`Range.step_by`, `Slice.iter`,
`Slice.iter_mut`) so the deeper walker errors surface instead of
being masked by `unknown identifier`. The walker fix requires editing
`Forward.lean::lookupSymExpr` and the EvAssign re-bind path to keep
`localTypes` updated when a local's effective type changes, plus
plumbing trait method signatures through call sites — a session-sized
investment on its own.

c_lean per-fixture: 35 → 35 (no flip from shim stubs alone).
c_lean per-decl:    449 → 449.

## Translator-fixes session — close

```
c_lean per-fixture: 35 / 89 (was 30)
c_lean per-decl:    449 / 3143 (was 329)
g_byte:             3 pass (unchanged)
g_rust:             44 hand + 42 auto = 86 (unchanged)
diff-harness:       PASS at 275 lines byte-identical
```

Commits in order:
1. `249de0e9` — Bug 5 (Option/String): `+1` fixture (`options`).
2. `7b17d790` — Bug 3 (stateless loops): `+3` fixtures
   (`issue-134-loop-shared-borrows`, `issue-270-loop-list`,
   `mini_tree`).
3. `ea6b5d89` — Bug 2 (uninitialised locals): `+1` fixture (`drop`).
4. `169ca529` — Bug 1 (trait reshape): structural fix, `+0` immediate
   (unblocks Bug 4-gated trait fixtures).
5. `3ec15a2e` — Bug 4 (shim stubs): scaffolding only.

### Carry-forward for next session

* **Bug 4 (per-local type tracking)** — the largest remaining cluster.
  Surface: `Forward.lean::lookupSymExpr` and the EvAssign re-bind
  path. Compounds with Bug 1's trait-method-signature plumbing.
  Estimate: 6-12 hours; expected unlock: 5-10 fixtures including
  `static`, `joins`, `iterators-scalar`, `arrays`, `slices`.

* **Aggregate-rvalue propagation** — `issue-803-self-in-array`'s
  `Assign(local 0, Aggregate([Array, [local 2]]))` isn't handled by
  the post-walk `propagateRefsFromBlock` (which only does Ref/Use).
  Extending it to recognise Aggregate(Array, [singleSrc]) would emit
  a singleton-array literal and unlock the fixture. Small fix.

* **`constants` placeholder** — `use_static::PREFIX` body emits `ok
  0#u32` against a `Result (Array Std.U8 1#usize)` return type
  (placeholder synthesiser doesn't recognise `Array`). Mirror the
  `Pair` placeholder logic in `placeholderPExprOfWith` for `Array`.

## Bug 4 session — 2026-05-19 (close)

Following `prompts/zero-skip-bug4-prompt.md`. Three sub-bugs.

```
c_lean per-fixture: 38 / 89 (was 36)
c_lean per-decl:    463 / 3143 (was 451)
g_byte:             3 pass (unchanged)
g_rust:             44 hand + 42 auto = 86 (unchanged)
diff-harness:       PASS at 275 lines byte-identical
```

Commits in order:
1. `145ed187` — Sub-bug 4a (vm[1] type-incompat): `+1` fixture (`joins`).
2. `c5dcb3fd` — Sub-bug 4c (multi-elem Array): `+0`, scaffolding only.
3. `988a6153` — Sub-bug 4b (Slice/Array/tVar typed fallback): `+1` fixture (`static`).

### Sub-bug 4a — `lookupPlace` vm[1] fallback drops type info → DONE (`145ed187`)

`lookupPlace` falls back to `vm[1]` (the first input parameter)
when the queried local is missing. For `incr(x:&mut u32){*x += 1}`-
shape fixtures the over-approximation is right (the temp's
projected `U32` matches input-1's peeled `&mut U32`), but
`joins::call_choose` reads `local 7 : U32` whose `vm` slot is unset
because the join's binding got dropped — and input-1 is `Bool b`.
The fallback emitted `b + 1#u32`. Same shape kills
`joins::use_enum`.

Add `vm1FallbackCompatible`: peel outer refs from both candidate
types and compare. Block the vm[1] fallback only when both sides
are concretely identifiable as different `litTy`s, different
`tAdt`s, or litTy↔tAdt — every other shape (including unknown
sides) preserves the legacy behaviour. When blocked, fall through
to the existing typed-placeholder path (`placeholderPExprOf`).

c_lean per-fixture: 36 → 37 (+`joins`).
c_lean per-decl:    451 → 459 (+8).

### Sub-bug 4c — Multi-element Array aggregates → DONE (`c5dcb3fd`, scaffolding)

Extend the Aggregate-array rvalue propagator and the
`placeholderPExprOfWith` Array path from single-element only to
arbitrary length. Multi-element literals `[e₁, …, eₙ]` (n ≥ 2)
lower to `Aeneas.Std.Array.ofList (e₁ :: … :: List.nil)`; zero-
length `[]` lowers to `Array.ofList List.nil`. Add the `Array.ofList`
shim alongside `Array.singleton`. No fixture flips — every
candidate has at least one independent upstream issue. Scaffolding-
only commit; the right shape so downstream fixes don't have to
revisit array literals.

c_lean per-fixture: 37 → 37 (no flips).
c_lean per-decl:    459 → 459 (no flips).

### Sub-bug 4b — Trait-bound Self / Slice typed fallback → PARTIAL (`988a6153`)

Two coordinated extensions to the 4a typed-fallback machinery:

(1) Extend `vm1FallbackCompatible` to reject `tVar`↔concrete pairs
and `tSlice`/`tArray`↔`litTy`/`tAdt` pairs. Catches Charon-elided
const-item reads like `static::read`'s `S::SLICE` (local 5 is
`&Slice U16`, input-1 is generic `S`).

(2) Extend `placeholderPExprOfWith` for `tSlice` (emit
`Aeneas.Std.Slice.placeholder`) and `tRef` (peel and recurse).
Switch `lookupPlace`'s typed-fallback path to the tdm-aware
variant so a missing `Slice α` slot emits the shim's empty-slice
helper instead of the catch-all `0#u32`. Add shim helpers
`Slice.placeholder` / `Array.placeholder`.

c_lean per-fixture: 37 → 38 (+`static`).
c_lean per-decl:    459 → 463 (+4).

The wider 4b unlock (`traits`, `default`, `defaulted_method`,
`blanket_impl`, `demo`) was not reached — those fixtures have
distinct upstream issues:
* `traits` — "unsupported pattern in syntax match: Option.Some x2".
* `default` — parse-level emit gap (unexpected token `;`).
* `defaulted_method` — `Unknown constant
  defaulted_method.YesOverride.Insts.Defaulted_methodTrait.required_method`
  (impl-method qualifier mismatch from Bug 1 cascade).
* `demo` — `Counter.incr` body `self + 1` typed as `Usize` not
  `Result _` (Bug 1 incomplete coverage of body shape).

### Carry-forward for next session

* **Trait-impl-heavy fixtures** (`traits`, `default`,
  `defaulted_method`, `blanket_impl`, `demo`) — five fixtures
  blocked on a mix of pattern-syntax, parse-level emit gaps, and
  Bug 1's incomplete body shaping. Each looks like a separate
  small fix rather than a single shared root.

* **Iterator / slice-iter fixtures** (`step_by`, `iterators-array`,
  `iterators-scalar`, `chunks_exact`) — blocked on missing shim
  bindings for `core.slice.Slice.iter`,
  `core.iter.adapters.step_by.StepBy.next`, etc. Worth a dedicated
  shim-extension session.

## Bug 4 deep session — 2026-05-19 (close-1)

Following `prompts/zero-skip-bug4-deep-prompt.md`. First sub-bug
landed; remaining three to follow.

### Sub-bug 4d — Stdlib-ADT placeholder synthesis → DONE

Three coordinated fixes for the typed-fallback machinery so a
missing `Option α` slot synthesises a usable placeholder, plus the
empty-array literal `[]` pins its element type to avoid an
unconstrained metavariable through `Array.ofList List.nil →
ArrayToSliceShared → Slice.iter → …`:

1. **`Option.placeholder`**. New top-level shim
   (`Option.placeholder : Option Unit := none`) — Unit-pinned so
   the call site doesn't leave a higher-order metavariable on
   `α`. `core.option.Option.is_none` / `.is_some` returns `Bool`
   regardless of `α`, so the type pin is safe.
   `Forward.lean::placeholderPExprOfWith`'s `tAdt` branch now
   recognises `info.name == "Option"` and emits
   `.app "Option.placeholder" #[]` instead of the catch-all
   `0#u32`.

2. **`Array.ofList` autoParam-style `n` default**. Made `n` an
   *explicit* arg with default `Usize.ofNat xs.length`, so
   `Array.ofList [a, b, c]` resolves `n = 3#usize` without
   needing downstream context. Restores type inference for the
   typical
   `ArrayToSliceShared (Array.ofList [0#u32, 0#u32, 0#u32])` chain
   where the slice coercion erases `n` from the result.

3. **`Array.empty` (Unit-pinned)**. New shim
   (`Array.empty : Array Unit 0#usize := ⟨[]⟩`) for the
   empty-array case. The `Forward.lean`'s `Aggregate(.array _,
   #[])` propagation and `placeholderPExprOfWith`'s `tArray _ 0`
   branch both now emit `Aeneas.Std.Array.empty` instead of
   `Array.ofList List.nil` — element type Unit, length 0#usize,
   no metavariables to resolve.

c_lean per-fixture: 38 → 40 (+`step_by`, +`arrays_defs`).
c_lean per-decl:    463 → 573 (+110).
Diff harness:       PASS at 275 lines byte-identical.
g_rust:             86 (44 hand + 42 auto, unchanged).

### Sub-bug 4f — Typed placeholders + iterator shim shape → DONE

Four coordinated extensions so the chunks_exact-style `&mut self`
iterator chain compiles end-to-end:

1. **`ChunksExact.next` shim shape**. Returns
   `Result (Option (Slice T) × ChunksExact T)` (was
   `Result (Option (Slice T))`). Matches the standard backend's
   `Self → Result (Option α × Self)` convention; the cert walker
   destructures `(value, new_state)` so the pair is required.

2. **Opaque ADT registration with `isOpaque := true`**.
   `Driver.lean::buildTypeDeclMapFromLlbc` now records opaque
   stdlib types (StepBy, Iter, IterMut, ChunksExact, NonZero, …)
   in `tdm` with the `isOpaque` tag. `llbcTyToPTyWithVars` still
   maps them to the legacy U32 fallback (signatures can't emit
   unknown `StepBy T`-style heads), but the typed-fallback path
   in `placeholderPExprOfWith` now dispatches on `info.name`.

3. **Typed-ascription emit via `__typed::<typeStr>` head**.
   New PExpr head + pretty-printer rule (mirrors the existing
   `__cast::` mechanism). `renderConcreteLlbcTy` renders a concrete
   `LlbcTy` to a Lean type string (scalars, slices, arrays, named
   ADTs); the placeholder synthesiser wraps `Slice.placeholder`,
   `Option.placeholder`, `ChunksExact.placeholder` with the
   concrete ascription so call sites that don't constrain `α`
   (e.g. `Slice.len Slice.placeholder`, whose result is
   `Result Usize` regardless of element type) still elaborate.

4. **`ChunksExact.placeholder` shim + top-level alias**. The shim
   is polymorphic in `α`; a top-level `abbrev ChunksExact (T : Type)`
   alias resolves the cert's bare-name typed-ascription
   (`ChunksExact U32`) to `core.slice.Slice.ChunksExact U32`.

c_lean per-fixture: 40 → 41 (+`chunks_exact`).
c_lean per-decl:    573 → 671 (+98).
Diff harness:       PASS at 275 lines byte-identical.
g_rust:             86 unchanged.

### Sub-bug 4e — Loop body state-tuple drop → DONE

`iterators-scalar::iter_loop.body` had params `(n : Usize) (i : Range Usize)
(j : I32)` and return type `Result (ControlFlow (Range Usize × I32) Unit)`,
but the body was `ok (cont i)` — packing only the *first* state local
when the ControlFlow state type was the tuple `(Range Usize × I32)`.
The loop wrapper then couldn't apply the body (`iter_loop.body n i` had
type `I32 → Result …` after partial application). Same shape on every
multi-state loop.

* `Loops.lean::buildLoopBody` no-branch case (line 218) now packs all
  state locals as a tuple when `stateNames.size ≥ 2`. Single-state
  stays bare. (The conditional-branch path already had the right
  shape; this just brought the unconditional-body case into
  alignment.)
* `Loops.lean::buildLoopWrapper` lambda now destructures via the
  Lean `fun (i, j) => body n i j` sugar (encoded by passing the
  literal `"(i, j)"` as a single `.lam` param "name" — the pretty
  printer renders it verbatim). For single-state we keep the bare
  `fun i => body n i` shape.
* New `Vec.from` shim (`alloc::vec::Vec::from`) with a parametric
  second-arg type so the cert's elided-binding call shape
  `Vec.from <placeholder>` typechecks. Unblocked by 4e via the
  iterators-scalar sweep.

c_lean per-fixture: 41 → 42 (+`iterators-scalar`).
c_lean per-decl:    671 → 770 (+99).
Diff harness:       PASS at 275 lines byte-identical.
g_rust:             86 unchanged.

### Sub-bug 4g — Opaque iterator-state transparency → DONE

The prompt framed 4g as "Call-return type refresh on EvCall", but on
inspection `localTypes` was already seeded correctly from
`lf.localsTypes` — the visible failure (wrapper sig
`iter_range_step_by_loop (i : U32)` but call passes `t0 : Range Usize`)
came instead from `llbcTyToPTyWithVars` falling back to U32 for
opaque ADT types. Each iterator wrapper has a specific underlying
type that the corresponding shim flows through; treat the wrapper as
transparent at the signature level so wrapper-sig matches the shim's
return.

* `StepBy<X>` → `X` (the shim's `Range.step_by` returns `Range Usize`,
  so `StepBy<Range<Usize>>` renders as `Range Usize`).
* `Iter<T>` / `IterMut<T>` → `Slice T` (the shim's
  `Slice.iter` / `Slice.iter_mut` returns the same `Slice`).
* `IntoIter<T>` → `Vec T` (the shim's `Vec.into_iter` returns the same
  `Vec`; the cert's `IntoIter<T>` wrapper holds the Vec value).
* `Vec<T, A>` → `Vec T` (drop the `Allocator` generic so the emitted
  type aligns with the mono-arg `alloc.vec.Vec T` shim).
* `core::ops::range::Range` added to `isStdlibTypeDecl` so the
  translator no longer emits a fixture-local `Range` struct that
  would shadow `Aeneas.Std.Range` and create two distinct types at
  the wrapper-call site.
* New top-level `abbrev Vec (T : Type) := alloc.vec.Vec T` so the
  bare-name `Vec U32` (after the allocator drop) resolves.

c_lean per-fixture: 42 → 43 (+`iterators-array`).
c_lean per-decl:    770 → 863 (+93).
Diff harness:       PASS at 275 lines byte-identical.
g_rust:             86 unchanged.

### Carry-forward

* **`iterators`** — still mismatched. After 4g the wrapper signatures
  match, but `slice_iter_mut_while` and `slice_iter_while` have an
  emitter issue: the loop body has `if t0 then cont i else done i`
  where `t0` is the `IterMut.next` result (a `Option × Slice` pair,
  not a `Bool`). The fix is to translate the cert's
  match-on-Option-arm into `if t0.fst.isSome then …` (or a real
  match). Distinct from the 4g surface; needs a separate sub-bug.
* **Trait-impl-heavy fixtures** (`traits`, `default`,
  `defaulted_method`, `blanket_impl`, `demo`) — unchanged from prior
  session; each has a distinct upstream issue.
