# G_rust coverage expansion plan

*Status: plan only; no implementation in this document.*
*Companion docs: `meta-harness-contract.md` (gate definitions),
`meta-harness-build-progress.md` (build campaign), the
`scripts/regen-fixture-mirrors.sh` workflow for verify-tainted
fixtures.*

## 1. Goal & non-goals

**Goal**: raise `meta-harness --sweep tests/llbc --gates g_rust` per-
fixture pass count from **13/86** today to **~37/86**, by closing
specific blocker categories. The remaining ~49/86 are fixtures with
zero public functions (e.g. `assert-cfg`, `builtin`, `drop`,
`adt-borrows`) — they have no differential-testable surface by
design; their cert pipeline is exercised by g_byte.

**Non-goals**: don't change the g_rust gate's contract; don't touch
the soundness theorems; don't break any of the 86 hand-written + auto-
generated tests passing today; don't synthesise inputs for closures /
async / FFI (the contract calls these out as honest skips).

## 2. Current state (post-merge of `28a0b3d3`)

| Metric | Value |
|---|---|
| Fleet fixtures | 89 |
| **c_rust** (Rust compile via charon) | **89/89** ✓ |
| **g_byte** processed (pass + divergent) | **86/89** |
| **c_lean** (L₁ typechecks via lake env lean) | **25/89** |
| **g_rust** per-fixture pass (≥1 decl) | **13/89** |
| g_rust per-decl pass | 53 |
| Auto-generated proptests | 42 |
| Hand-written proptests | 44 |
| `cargo test` count | 86, all pass |
| Generator emit skips (last run) | `non-public=107  non-simple-sig=177  missing-model=68  missing-source=4` |

The c_lean gate landed in this branch. Per-decl: 146 pass (in the 25
typechecking fixtures), 2997 fail. Failure clusters (first-error per
fixture):

- 18 type mismatch
- 11 `end <ns>` mismatch (emitter doesn't close namespace right)
- 9 "function expected" (call-site shape wrong)
- 7 parse errors (tokens the elaborator rejects)
- 1 field/fn name collision (`struct.len` vs `fn len`)
- 18 other (Lean-side semantic errors)

These are emitter-side gaps. The zero-skip campaign (planning doc
`zero-skip-plan.md`) is the natural workstream for fixing them; this
plan focuses on the differential-test side.

## 3. Blocker taxonomy

Per-fixture analysis of the 73 untested fixtures bucketed by the
shape of their public functions:

| Bucket | Fixtures | Decl total (≈) | Primary blocker |
|---|---|---|---|
| **A — scalar-sig + model gap** | 10 | ~40 | All-scalar args/return, but the model fn isn't in `src/model.rs` (the regen body filter rejected it) |
| **B — reshape** | 7 | ~16 | `&mut T` / `&T` args that aeneas reshapes to value-returning fns; original Rust signature differs from the model's, so a hand-written `ref_impl` wrapper is needed |
| **C — ADT** | 1 | ~1 | Args use a fixture-local struct/enum (e.g. `list_basic::Node`); needs a per-fixture module pattern like the existing `aggregates_basic`/`reborrows` |
| **D — generic / trait** | 6 | ~80 | Generic fns without a monomorphised call site, or trait-object args |
| **E — zero public fns** | 49 | ~1500 | No `pub fn` surface; g_rust can't reach by design. Out of scope for this plan. |

**Total reachable**: 24 fixtures across A–D, accounting for roughly
~140 decls.

### Phase-A fixture list (scalar-sig + model gap)

- `arrays_defs` (1 decl)
- `chunks_exact` (9)
- `deref` (1)
- `loops` (4)
- `loops_simple` (1)
- `order` (2)
- `paper` (4)
- `rename_attribute` (1)
- `step_by` (11)
- `traits` (5)

These are the closest-to-ready: signature already simple, source
either plain-Rust or behind the verify-mirror Agent B added. The
only thing standing in their way is the body filter in
`--regen-models` rejecting their R₁ body as un-compilable.

### Phase-B fixture list (reshape wrappers)

- `array_slice_index` (6)
- `curve25519` (2)
- `discriminant` (2)
- `loop_shared_loan_in_join` (1)
- `mini_tree` (1)
- `multi_region` (2)
- `slices_basic` (2)

These have only-`&mut`-or-`&` signatures. The model has the
reshape (e.g. `fn(&mut u32)` → `fn(u32) -> u32`); R₀ needs the
matching wrapper.

### Phase-C fixture list (ADT)

- `list_basic` (1) — a single linked-list shape.

### Phase-D fixture list (generic / trait)

- `derive` (24 decls, all generic)
- `generics_basic` (1)
- `hashmap` (10+)
- `list_generic` (1)
- `slices` (4 generic, 1 ADT)
- `traits_basic` (1)

## 4. Phased plan

### Phase A — body filter relaxation (~10 fixtures, ~40 decls)

**Hypothesis**: most missing-model decls have a body that looks like
either:
- A small `match` (e.g. `step_by` iteration cases)
- A `let`-chain leading to a single return expression
- Some specific stdlib calls aeneas's `--rust-model` knows how to emit

**Approach**:

1. Pick `step_by` (11 candidates) as the pilot. Run `aeneas-check
   --rust-model tests/llbc/step_by.cert.json --out /tmp/step_by.rs`
   and look at exactly which bodies were rejected.
2. Extend the body-filter rules in `tools/meta-harness/src/regen.rs`:
   - Accept `match <local> { Pattern => expr, ... }` where every arm
     produces a scalar.
   - Accept `let` chains where every RHS is composed of already-
     accepted patterns.
   - Accept enum constructors *if* the enum is defined in the same
     fixture and consists of all-scalar variants (overlap with Phase
     C ADT support).
3. The regen tool already has per-fn rollback via `cargo check`. As
   the body filter loosens, the rollback safety-net catches anything
   that survives the filter but still doesn't compile.
4. After each fixture, re-run `meta-harness --generate-tests` and
   `cargo test --release`. Count the new pass.

**Acceptance**:
- Phase A is **done** when `meta-harness --sweep` reports g_rust pass
  for at least 7 of the 10 fixtures, with no regressions in the
  existing 86 tests and no fleet mismatches. The 3 remaining can be
  documented as Phase-A residuals.

**Effort**: ~1 engineer day. Filter extension is mostly bounded; the
per-fn rollback prevents catastrophic compile breakage.

### Phase B — reshape-aware `ref_impl` auto-gen (~7 fixtures, ~16 decls)

**Hypothesis**: aeneas reshapes follow predictable patterns. The
common ones already documented in `lib.rs`'s hand-written `ref_impl`:
- `fn f(x: &mut T)` → `fn f(x: T) -> T`  (return the new value)
- `fn f(x: &T) -> T'` → `fn f(x: T) -> T'`  (drop the borrow)
- `fn f(x: &mut T, y: U) -> V` → `fn f(x: T, y: U) -> (V, T)`

**Approach**:

1. Add a new flag `--generate-ref-impl` to the meta-harness that
   walks each cert decl. For each one with a reshape:
   - Read the original signature from `tests/src/<fixture>.rs` (or
     the mirror) via syn-style parsing of the `pub fn` lines.
   - Read the reshaped signature from the cert.
   - Generate a `ref_impl::<fixture>_<fn>` wrapper whose body calls
     the original and packages the result to match the reshape.
2. Emit the wrappers into a new auto-generated file
   `src/ref_impl_auto.rs`. `include!()` it from `lib.rs`'s
   `pub mod ref_impl`.
3. Update the `--generate-tests` emitter to prefer
   `ref_impl::<fixture>_<fn>` over `<fixture>_src::<fn>` when the
   wrapper exists (the existing convention).

**Acceptance**:
- Phase B is **done** when 5 of the 7 Phase-B fixtures gain at least
  one g_rust pass.

**Effort**: ~1.5 engineer days. Parser for `pub fn` lines is straight-
forward; the reshape-pattern catalogue may need expansion as new
patterns surface.

### Phase C — `list_basic` per-fixture module (~1 fixture, ~1 decl)

**Approach**: hand-mirror the existing `aggregates_basic`/`reborrows`
per-fixture module pattern in `lib.rs`. Define the fixture's `Node`
type once, copy the original Rust impl as `<fixture>_<fn>_ref`,
include the regen'd model file. Add a proptest block in `tests/diff.rs`
(hand-written; not via auto-gen) since the auto-gen flat-namespace
model can't reference per-fixture struct types.

**Acceptance**: g_rust pass for `list_basic`.

**Effort**: ~half engineer day.

### Phase D — generic & trait cases (~6 fixtures, ~80 decls)

The honest answer: most generic decls **can't** be auto-tested
without a monomorphisation site. The exceptions:

- Decls where the generic parameter has a single concrete
  monomorphisation already in the fixture (e.g. some `hashmap`
  methods specialised to `HashMap<u32, u32>` via the fixture's own
  `__test_*` callers).
- Trait-impl methods on concrete `Self` types whose vtable is
  inferable from the cert.

**Approach**: case-by-case. Pick `hashmap` first — it has the most
decls and the clearest concrete-monomorphisation pattern. Document
the unblock recipe in `documentation/plans/grust-generic-recipes.md`.
Iterate on the remaining 5 fixtures only if the recipe transfers.

**Acceptance**: Phase D is **done** when at least 2 of the 6 Phase-D
fixtures gain g_rust passes and the unblock recipe is documented.
The remaining 4 are explicitly **deferred** with reason classes
(e.g. `g_rust: skip, reason: no_monomorphisation_site`).

**Effort**: ~2-3 engineer days, depending on how far the recipe
transfers.

### Phase E — zero-public-fn fixtures (49 fixtures, ~1500 decls)

**Action**: none on the g_rust side. Update the meta-harness's sweep
report to surface these as `g_rust: not-applicable, reason:
no_public_fns` rather than the misleading `skip(no_test_coverage)`.

**Effort**: ~half engineer day (one tweak to `sweep.rs`'s per-fixture
classifier).

## 5. Expected outcomes

| Phase | Fixtures gained | Cumulative coverage |
|---|---|---|
| Today | (baseline) | 13/86 |
| After A | +7 | 20/86 |
| After B | +5 | 25/86 |
| After C | +1 | 26/86 |
| After D | +2 | 28/86 |
| After E (relabel only) | +0 | 28/86 with 49 honestly labelled |

Phases A+B+C+E are roughly 3 engineer-days of work. Phase D is
optional (2-3 more days) and stops adding value past ~28.

## 6. Stopping conditions

- Any phase breaks a hand-written test in `tests/diff.rs` → revert,
  investigate (most likely root cause is a body-filter regression or
  a name collision in the regen).
- Any phase introduces a `mismatch` outcome in the fleet sweep →
  treat as a real differential bug, do not paper over with manifest
  skips.
- Phase-D recipe stops transferring after the second fixture → stop
  Phase D and document residuals.

## 7. Out of scope (explicit)

- **The 3 g_byte-skip fixtures** (`closures`, `issue-804-closure-
  return-ref`, `raw_pointers`): mainline aeneas can't emit them, so
  there's no L₀ to compare against. Already documented as
  unprocessable.
- **Async / FFI fixtures**: none in the current 86, but if any are
  added later, they fall into the same "no cert" bucket.
- **Cross-language gates** (G_rfl, direct R₀↔L₁ via Lean elaborator):
  separate plans.
- **External crates**: the `--crate` flag already works; this plan
  is in-tree only.

## 8. Open questions

1. **Where does `--regen-models` write the body-filter rules?**
   Currently hard-coded in Rust. As we tighten/loosen, do we want a
   `meta-harness.toml`-style allowlist of accepted body patterns?
2. **Per-fixture `meta-harness.toml`** vs **a global manifest at
   `tests/lean-checker/differential/meta-harness.toml`**? The
   contract §2 suggests the former; this plan is agnostic. Lean
   toward global for in-tree fixtures since they share a build.
3. **Naming convention for auto-generated ref_impl wrappers**: keep
   the existing `<fixture>_<fn>` naming, or switch to
   `<fixture>::<fn>_ref` to distinguish from the model's `_model`
   suffix? The current convention is fine.
