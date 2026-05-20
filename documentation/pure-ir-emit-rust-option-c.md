# pure-ir-emit-rust — Option C: Route Everything Through `core-models`

A self-contained plan to lift `rust/pure-ir-emit-rust` from "synthetic
shims with `unimplemented!()` bodies" (today, after Option A) to
**every reference to a `core::*` or `alloc::*` item in the emitted
Rust resolved to its `core_models::*` analogue**.

This is the eventual goal the user named when Option A landed
(commit `8a8e03a4`). Option A staged the work: the path-mapping
module (`rust/pure-ir-emit-rust/src/core_models_map.rs`) and the
post-processor (`src/bin/route-shims.rs`) carry over; the emitter
itself was untouched. Option C is where the emitter starts calling
the mapping table directly at emit time, and the post-processor
goes away.

---

## Goal

Every line of Rust that `pure-ir-emit-rust` writes references
`core_models` for any item whose Charon `item_meta.name` starts with
`core::*` or `alloc::*`. Native Rust syntax (`+`, `if`, `let`,
primitive types `u32` / `bool` / `(T, U)` / `[T; N]`) is preserved
only where `core_models` has no analogue or where the semantics are
identical to native and routing would be pure ceremony (e.g. `==` on
`u32` against `core_models::cmp::eq::<u32>`).

Diff testing under Option C compares R₀ (the original
`tests/src/<fixture>.rs` using `std::*`) against R₂ (the emit, now
routed through `core_models::*`). Disagreement = bug in either the
emitter **or** `core_models`. The two trees become mutual
regression bounds for each other.

---

## Why

1. **One Rust model, many backends.** `core_models` already feeds
   hax-F\*, hax-Lean, and Aeneas-Lean. `pure-ir-emit-rust` becomes a
   fourth consumer. Each backend's bugs surface as `core_models` /
   downstream-emit disagreement.
2. **Diff testing becomes bidirectional.** Today the harness can
   only catch emitter bugs (assuming `core_models` is correct);
   under Option C, the same harness also catches `core_models`
   bugs (because a working emitter against a broken model
   diverges from the source).
3. **Coverage gaps become actionable.** When the emitter wants to
   route something `core_models` doesn't model, a build artifact
   records the gap — a TODO list for upstream `core_models` work.
4. **Removes the shim/post-processor dance.** Option A's
   `route-shims` binary plus the two-phase regen script are
   workarounds; under Option C the emitter produces routed Rust
   directly.

---

## Non-goals

- **Replacing native operators where rustc's compilation is identical**
  to the routed call. E.g. `u32` non-overflow `+` on release mode is
  the same machine instruction as `core_models::num::wrapping_add`;
  pure ceremony to route it. We route **only** where the IR's
  semantics imply something native syntax doesn't carry — overflow
  modes (`OPanic` / `OUB` / `OWrap`), checked variants, etc.
- **Extending `core_models` itself.** Gaps are surfaced; extensions
  are separate campaigns (probably in `~/rust-core-models`'s repo, not
  here).
- **Removing native `core::*` types.** `Option<T>` syntax stays
  visually as `Option<T>` in the emit — but the `use` statement at
  the top of every emitted file maps it to `core_models::option::Option<T>`.

---

## Stages

### C.1 — Dep promotion + mapping infrastructure (~1h)

- Move `core-models` from `[dev-dependencies]` to `[dependencies]`
  in `rust/pure-ir-emit-rust/Cargo.toml`. The mapping module
  (`src/core_models_map.rs`) was already in the emitter library —
  now `pir2rs`'s output crate type-checks against `core_models`.
- Add `MissingModels` sink — a `RefCell<Vec<MissingEntry>>` on
  `EmitCtx` that records `(charon_path, callsite_location)` every
  time the emitter looks up a path and gets `None`. Dump to
  `target/missing_models.json` at the end of each `pir2rs` run.
- Cargo feature `route-through-core-models` (default `on`) gates
  the routing. With the feature off, emit reverts to today's
  shim behavior (escape valve if `core-models` build breaks).

### C.2 — Operator lowering (~2-3h)

- Re-route `Binop::Add(OverflowMode, IntTy)` / `Sub` / `Mul` / `Div`
  / `Rem` etc. when operands are `core_models`-modeled integer
  types. Concretely:
  - `Add(OWrap, U32)` → `core_models::num::wrapping_add::<u32>(x, y)`
  - `Add(OPanic, U32)` → `core_models::num::checked_add::<u32>(x, y).ok_or(())?`
  - `Add(OUB, U32)` → `core_models::num::unchecked_add::<u32>(x, y)` (or
    panic-equivalent if `core_models` doesn't model UB ops).
- `AddChecked` / `SubChecked` / `MulChecked` → `core_models::num::overflowing_*`.
- `Shl(OverflowMode, IntTy, IntTy)` / `Shr` → `core_models::num::rotate_*` /
  `wrapping_shl` etc.
- `Eq(Ty)` / `Ne(Ty)` → `core_models::cmp::eq(x, y)` for modeled types,
  native `==` otherwise.
- `Lt(IntTy)` / `Le` / `Gt` / `Ge` → `core_models::cmp::lt` /
  `le` / etc.
- `BitXor` / `BitAnd` / `BitOr` → native (bit ops are identical
  semantics).
- `Cmp(IntTy)` (PartialOrd-like) → `core_models::cmp::cmp`.
- `BoolOr` (`||`) → native (no `core_models` analogue).

Touch points: `emit.rs::emit_binop` (or wherever today's binop
dispatch lives). Test the easy cases first (`Add(OWrap)`) before
the dense overflow-mode switch.

### C.3 — Inherent methods on primitives (~1-2h)

- `u32::wrapping_add` / `wrapping_sub` / etc. — these were the
  Option-A targets, already mapped. Move the lookup from
  `route-shims` to `emit.rs`.
- Associated constants: `u32::BITS` → `core_models::num::U32_BITS` (or
  whatever the model names them; today's emit returns `Ok(0u32)` which
  is the known emitter bug from the diff harness).
- Subsumes A's 18-entry mapping table. Expand to ~30-40 entries as
  more inherent-method shims surface during testing.

### C.4 — `core::*` types (~3-4h)

- Replace the emitted prelude's `Result<T> = core::result::Result<T, ()>`
  with `pub use core_models::result::Result as Result;` (or a single
  `use` at the top of each emitted file).
- Same for `Option<T>` → `core_models::option::Option<T>`,
  `Vec<T>` → `core_models::vec::Vec<T>`, etc.
- Watch out for **interop**: emitted code is self-contained — it does
  not need to interoperate with native `core::*` types crossing the
  boundary. R₀ (the diff-test reference) uses native `core::*`; that's
  fine because diff tests compare *values*, not types, and proptest
  inputs are constructed in the diff-test harness layer using whichever
  Option/Result/etc. type each side expects.
- Charon name → Rust path translation: walk `item_meta.name`, swap
  `PeIdent("core")` for the literal `"core_models"`, then sanitize.
- For trait-impl path elements (`PeImpl`): the trait is a
  `core_models::*` trait, the receiver is the same. e.g.
  `<u32 as core::iter::Iterator>` → `<u32 as core_models::iter::Iterator>`.

### C.5 — Trait method calls (~3-4h)

- Every `Qualif::TraitMethod { trait_decl_id, method_name, .. }`
  whose resolved trait's `item_meta.name` starts with `core::*` or
  `alloc::*` routes through `core_models`.
- The hard sub-case: **generic** trait methods. When the receiver
  type is a generic param `T` (not a concrete `u32` / `i32` / etc.),
  the emit needs to either:
  - Constrain `T: core_models::SomeTrait` (the natural shape — `T` lives
    in `core_models`-land).
  - Emit the call via UFCS: `<T as core_models::iter::Iterator>::next(x)`.
  Both work; UFCS is more verbose but avoids needing to thread the
  trait bound up the call chain.
- Method names like `next`, `index`, `as_ref` — these may collide
  across multiple `core_models` traits. Disambiguate via the
  Charon `trait_decl_id` lookup.
- Fall back to today's `unimplemented!()` shim when no mapping
  exists; the `MissingModels` sink records the gap.

### C.6 — Drop the post-processor (~30 min)

- Delete `src/bin/route-shims.rs`.
- Remove the route-shims step from `scripts/regen-diff-models.sh`.
- The committed `tests/models/*_pir.rs` files now contain emitter
  output verbatim — no post-processing layer.
- Verify all diff tests + compile_check still pass.

### C.7 — Coverage tracking + plan-doc update (~1h)

- `target/missing_models.json` (per-run artifact) lists every
  unresolved path. Aggregate across the 89-fixture sweep into a
  committed report at `rust/pure-ir-emit-rust/MISSING_MODELS.md`.
- Plan doc (this file): update the acceptance table; record the
  final coverage stats.

---

## Diff testing under Option C

The harness compares R₀ (`std::*`-using source from `tests/src/*.rs`)
to R₂ (emit, routed through `core_models::*`). Any divergence
indicts either side:

- **Emitter bug**: emit chose the wrong `core_models::*` path or
  applied wrong arity.
- **`core_models` bug**: model body diverges from real `core::*`
  behavior. This is a finding upstream `core_models`-maintainers
  care about.

`core_models` has its own test suite (`~/rust-core-models/tests/`)
exercising it against `std::*` directly. That's our trust bound:
if a `core_models` item passes its own tests, we treat it as a
ground truth in our diff comparisons.

A useful future addition: emit R₃ = R₂ with all `core_models::*`
paths swapped back to `core::*` (so it uses native rustc lowering).
If `R₀ == R₃` and `R₀ != R₂`, the divergence is in `core_models`;
if `R₀ != R₃`, the emitter is wrong. This requires a small
in-harness rewriter (cheap — string substitution at test load
time). Mark as a follow-up after C.6.

---

## Risks

1. **`hax-lib` git dep weight.** `core-models` depends on
   `hax-lib` (git dep on `cryspen/hax`). Promoting `core-models`
   to non-dev means `cargo build` of `pure-ir-emit-rust` itself
   needs `hax-lib` to build cleanly. Mitigation: feature-flag
   route-through-models (default on); when off, emit reverts to
   today's behaviour and `hax-lib` isn't needed.

2. **`core_models` coverage gaps.** Many `core::*` items aren't
   modeled. The `MissingModels` sink + fallback to shims keeps
   emit complete but introduces silent gaps in diff fidelity.
   Mitigation: the gap list is committed; campaigns to extend
   `core_models` are tracked.

3. **PR independence under C.** `pure-ir-emit` PR now hard-deps
   on `core-models`. Options:
   - Path dep (local), git dep (PR-mergeable, pinned SHA),
     crates.io (if `core-models` is published).
   - Vendor a subset into `rust/core-models-subset/` (keeps PR
     independent at the cost of model duplication).
   - We picked the git-dep route in the staging discussion; document
     the pinned SHA in the Cargo.toml comment.

4. **Build complexity.** The mapping table needs to stay in sync
   with `core_models` reality. Drift surface: rename / reorganize in
   `core-models` → emit breaks. Mitigation: cargo build of
   `pure-ir-emit-rust` catches most drift at compile time (the emit
   would reference paths that no longer exist). For runtime
   correctness drift, only diff testing catches it.

5. **Privacy gotcha (carry-over from A).** Some `core_models`
   items (e.g. `core_models::num::<T>::wrapping_add` inside
   `#[hax_lib::attributes]` impl blocks) aren't `pub`. The A
   workaround was emitting native Rust calls instead. Under C
   we need either (a) lobby for the items to become `pub`, (b)
   route to the publicly-exposed delegate (`rust_primitives::*`),
   or (c) re-export them via a thin facade in `pure-ir-emit-rust`'s
   prelude.

---

## Sequencing

- C.1 → C.2 → C.3 are mechanical and small. Can land as a single
  agent invocation (~4-6h of work).
- C.4 (types) is its own larger stage. Distinct agent. ~3-4h.
- C.5 (traits) is the most complex. Distinct agent. ~3-4h. Builds
  on C.4's name-translation infrastructure.
- C.6 + C.7 land after C.1–C.5 are stable. ~1-2h cleanup.
- Total: ~12-16 hours, likely 3-4 agent invocations.

---

## Acceptance

1. Every emitted file's preamble has `use core_models::*` (or
   specific imports).
2. Every binop / inherent method / trait method whose IR path
   starts with `core::*` is routed (verifiable via
   `MISSING_MODELS.md` being empty for that class).
3. `cargo test` in `rust/pure-ir-emit-rust` passes:
   - `compile_check` (89-fixture sweep) — unchanged.
   - `diff` (hand-written) — same or more tests; zero new
     failures.
   - `diff_auto` (auto-generated) — count rises significantly
     (today: 40; target: ≥80 once previously-skipped panicking
     models become testable).
4. Build cleanly with and without the `route-through-core-models`
   feature flag.
5. `target/missing_models.json` is empty (or documents known gaps
   with rationale) for the 16+ currently-diff-tested fixtures.

---

## Estimate

| Stage | Effort |
|---|---|
| C.1 — Dep + infrastructure | ~1h |
| C.2 — Operators | ~2-3h |
| C.3 — Inherent methods | ~1-2h |
| C.4 — Types | ~3-4h |
| C.5 — Trait methods | ~3-4h |
| C.6 — Drop post-processor | ~30m |
| C.7 — Coverage tracking | ~1h |
| **Total** | **~12-16h** |

Likely 3-4 separate agent invocations, each scoped to one or
two adjacent stages.

---

## Open questions

1. **`hax-lib` weight.** Empirical: how long does `cargo build` of
   `pure-ir-emit-rust` take with `core-models` as a non-dev dep?
   If it's bad (>30s incremental), consider vendoring or feature
   gating more aggressively.
2. **`core_models` privacy hardening.** Should we file an issue
   against `~/rust-core-models` to make
   `core_models::num::<T>::wrapping_add` (etc.) `pub`? The Option A
   privacy workaround is brittle.
3. **R₃ in the diff harness.** Worth implementing the `core_models
   → core` swap-back rewriter to tri-corner the diff?
4. **Distinction between `core::*` and `alloc::*`.** `core_models`
   has separate `alloc/` crate. Do we treat them as one or two
   deps?
