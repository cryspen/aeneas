# Handoff prompt — Session 6: cast-keyword fix + G_byte sweep + cert-format follow-throughs

Paste into a fresh Claude Code session at `/Users/karthik/aeneas`.

---

You are continuing the four-artifact differential testing rollout for
Aeneas on branch `aeneas-lean-certificate-diff-test`. Phases 0 + 1 +
4a are complete; Phase 4b is at G_rust 39 proptests across 11
fixtures, G_lean 267 vectors across 7 fixtures. Session 5 landed Item
1 (cert-walker `S3`-class fix via a two-sided cert-format change) and
Item 2 (`demo.lean` wire-in via the new `--skip-decl` CLI flag).
Items 3 (cast keyword) and 4 (G_byte sweep) deferred — your job
picks them up. Plus a cheap-win carry-forward worth a half-hour of
sweep work before either.

Work in the worktree at `/Users/karthik/aeneas/.claude/worktrees/diff-test`,
NOT in the parent tree.

## Boot sequence — read in order

1. **Plan**:
   `documentation/plans/differential-testing-plan.md` — read §"Gates"
   (G_rust 39 / 11, G_lean 267 / 7) and §G_lean / §G_rust "Known
   unblockers". Session 5 closed nine constants-fixture unblockers
   via the cert-format change (X1, Q2, Q3, S2, S3, unwrap_y, YVAL,
   get_z1, get_z2) and the demo wire-in.
2. **Progress note**:
   `documentation/plans/differential-testing-progress.md` — §"Session
   5 (2026-05-18)" is the canonical handoff source. Pay attention to:
     - Item 1 outcome — the **OCaml** cert-format change in
       `src/cert/LlbcJson.ml::j_place` was the root cause; Forward.lean's
       `seedGlobalRefsFromBlock` is the Lean-side consumer.
     - Item 2 outcome — the new `--skip-decl` CLI flag is a localised
       escape hatch; reuse it for any future fixture with isolable
       broken decls.
     - §"Carry-forward into Session 6" — five items in priority order.
3. **Recent commits on the branch**:
   ```
   git log --oneline aeneas-lean-certificate-diff-test -10
   ```
   Top of the log should show `62a572b2 docs: Session 5 progress
   note`, then `2b3855ae Phase 4b Item 2: demo.lean wire-in`, then
   `c87c6eb9 Session 5 Item 1b: Lean cert walker seeds vm`, then
   `de834705 Session 5 Item 1a: cert serializer preserves PlaceGlobal`,
   then a parent-merge of M10.x.6-8. Below those: the Session-4 stack.
4. **Existing harnesses**:
   - G_rust: `tests/lean-checker/differential/` — 39 proptests / 11 fixtures
   - G_lean: `tests/lean-checker/lean-diff/` — 267 vectors / 7 fixtures

## Critical operational constraints

Same as Session 2/3/4/5. Restated verbatim because they keep mattering:

- **The M10 soundness agent commits to `aeneas-lean-certificate` (the
  parent branch).** All your work belongs on
  `aeneas-lean-certificate-diff-test`. Do NOT touch any file under
  `aeneas-lean-soundness/` or `aeneas-lean-checker/AeneasCheck/Theorems/`.
  The parent gets merged into your branch every now and then; never
  the other way without explicit user say-so. Treat the parent as
  read-only input.

- **Worktree isolation is fragile.** Three of four agents dispatched
  in Session 2 found their isolated worktrees pinned to a stale
  `004e11fe` commit predating `aeneas-lean-checker/`. **For every
  agent dispatch with `isolation: worktree`**: the FIRST Bash call
  must be `echo "[status] boot" && pwd && git log -1 --oneline && git
  branch --show-current`. If HEAD is `004e11fe` or any commit not in
  the diff-test ancestry, the agent MUST abort with a clear report —
  NOT fall back to editing the live worktree. Sessions 3 + 4 + 5 did
  all work inline (no agent dispatches); if you parallelise, this
  guard is still mandatory.

- **Pre-built binaries can lie.** Session 5 had to rebuild *both*
  `bin/aeneas` (the OCaml binary at
  `src/_build/default/main.exe`) and `aeneas-check` from the
  diff-test worktree's source. The May-18 timestamp on `bin/aeneas`
  in the parent worktree is no evidence that the binary contains
  diff-test-only fixes — in particular, the Session-5 cert-format
  change (`j_place` preserving `PlaceGlobal` info) is *only* in the
  diff-test worktree's built aeneas. Use
  `/Users/karthik/aeneas/.claude/worktrees/diff-test/src/_build/default/main.exe`
  for any `-emit-cert` invocation; the parent's `bin/aeneas` won't
  carry the global-info field.

- **Cert JSON v6 (Session-5-extended) is the current format.**
  `bin/aeneas -emit-cert` from the diff-test worktree emits v6 with
  optional `"global"` fields on `LlbcPlace`. The cert parser accepts
  both old (pre-Session-5) and new shapes — old certs work
  unchanged; new certs gain the seed-pass benefit in
  `Forward.lean`.

- **Streaming-watchdog guard**: every Bash call should be preceded by
  an `echo "[status] ..."` line so the 600s no-stream-output watchdog
  doesn't kill long builds.

- **Pre-built binaries that are safe to use by absolute path**
  (after rebuilding from this worktree):
  - `/Users/karthik/aeneas/.claude/worktrees/diff-test/src/_build/default/main.exe`
    (aeneas) — rebuild via `cd src && opam exec -- dune build`.
  - `/Users/karthik/aeneas/.claude/worktrees/diff-test/aeneas-lean-checker/.lake/build/bin/aeneas-check` —
    rebuild via `cd aeneas-lean-checker && lake build aeneas-check`.

- **Periodic parent merge**: `git merge aeneas-lean-certificate`
  mid-session keeps the eventual merge-back cost low. Session 5 did
  it once cleanly (M10.x.6-8 axiom-drop commits — pure soundness
  territory). Do it at least once.

## Scope of Session 6

Four items, in priority order. Item 0 (cheap regen) is a half-hour
warm-up that may unblock more fixtures for "free" before you commit
budget to Items 1–3. Land it first; then pick Items 1 + 2.

### Item 0 — Regen all 89 cert.json through Session-5 aeneas (~30 min)

Session 5's cert-format change (`j_place` now preserves
`PlaceGlobal` info) only landed for the three fixtures the diff
harness regen'd: `constants`, `scalars`, and `demo`. The other 86
cert files in `tests/llbc/*.cert.json` were emitted by pre-Session-5
aeneas and carry the lossy `local: 0` sentinel for every
`PlaceGlobal`.

**Action**: sweep every `.llbc` through the new aeneas binary and
re-emit. For each fixture whose body reads a global, the regen
swaps a typed-zero placeholder for the source-true reference. The
existing G_lean / G_rust harnesses won't change shape, but the
**output** of `aeneas-check --out` against the new cert may
elaborate more cleanly — candidate fixtures to spot-check after
regen: `constants-lean`, anything with `static`/`const` in its
source (look for `const-shadow`, `defaulted_method`,
`issue-815-global-referencing-fallible-global` — the last one has
"global" in the name and is exactly the shape Session 5 fixes).

  ```bash
  cd /Users/karthik/aeneas/.claude/worktrees/diff-test
  AENEAS=src/_build/default/main.exe
  for f in tests/llbc/*.llbc; do
    "$AENEAS" -emit-cert "$f" 2>&1 | grep -E "Wrote|Error" | head -1
  done
  git diff --stat tests/llbc/*.cert.json | tail -5
  ```

**Then**: run `bash tests/lean-checker/lean-diff/scripts/run-diff.sh`
to confirm no regression (267/267 should still hold), and
`cargo test --release` in `tests/lean-checker/differential/` for
G_rust. Commit the regen as one atomic commit ("regen all cert.json
through Session-5 aeneas binary") so the diff is reviewable.

**Pitfall**: some of the regen'd certs may have non-`"global"`
diffs — Charon source-span paths that Charon stores as absolute
when the LLBC was generated from an absolute-path cargo invocation
and as relative when from a relative one. Session 5 reverted
`incr_cert.cert.json` for this exact reason. If a regen diff is
*only* `"file": "tests/src/X.rs"` ↔ `"file":
"/Users/karthik/aeneas/tests/src/X.rs"` swaps, revert that file.
Real changes look like new `"global"` fields.

### Item 1 — Cast keyword emit fix (~half day)

Carry-over from Session 4 Item 4c + Session 5 Item 3. Two
companion bugs, both at the cert-walker layer (Forward.lean), NOT
RustEmit polish:

1. **`as`-casts drop the wrapper**: `cast_u32_to_i32_model(x1: u32)
   -> i32 { x1 }` is the symptom (syntactically invalid Rust).
   Expected: `(x1 as i32)`.
2. **`get_max`-class branch-variable confusion**: `get_max_model(x1:
   u32, x2: u32) -> u32 { let t0 = (x1 >= x2); if x1 { x1 } else {
   x2 } }` — the `if` should use `t0`, not `x1`. The cert walker
   emits the precomputed boolean but then forgets to thread it into
   the branch condition.

**Where to look:**

1. `aeneas-lean-checker/AeneasCheck/Translate/Forward.lean`'s
   handling of `Rvalue::Cast` (or whatever Charon names it; check
   the cert JSON event list for the variant tag).
2. `Forward.lean`'s `if`/`match` lowering — find where the
   precomputed `t0 : bool` would be assigned and confirm whether
   the subsequent switch reads `vm[t0]` or the original
   scrutinee's local.

**Acceptance criteria:**

- `cast_*` fixtures emit `(x1 as i32)` (Rust) / `x1.toInt32`
  or similar coerce-via-shim shape (Lean).
- `get_max::{u32,i32}` emits `if t0 then x1 else x2`.
- In G_rust: wire `no_nested_borrows::{cast_u32_to_i32,
  cast_i32_to_u32, get_max_u32, get_max_i32, test2, refs_test1}`
  as new proptests (~6 fixtures).

**Pitfall**: the Session-4 deferred `Coe` shims (already in
`RuntimeShim/Aeneas/Std.lean`) keep the Lean side compiling for
*narrow* cast cases (U32→U16, U16→U32, etc.); the Rust side still
won't compile until the emit-level fix lands. If the emit fix
exposes a cast Coe combo not yet shimmed (e.g. I32→I64), add the
instance the same shape as the existing entries.

### Item 2 — G_byte sweep mode (~3 hours)

Lowest-effort highest-signal gate after Item 1. Current state:

  `scripts/compare-backends.sh` is interactive, per-fixture — runs
  `bin/aeneas` (mainline) and `aeneas-lean-checker` against the same
  cert and diffs their outputs.

Extend to:

  `scripts/compare-backends.sh --sweep` runs the diff over every
  cert in `tests/llbc/*.cert.json`, classifying each as
  `pass / fail / mismatch / skip`. Mismatches land in a per-fixture
  allowed-divergence list (`scripts/compare-backends-known-divergent.txt`)
  with a one-sentence reason — same shape as G_rust's existing
  `tests/lean-checker/differential/known-divergent.md`.

**Acceptance criteria:**

- A single `bash scripts/compare-backends.sh --sweep` command that:
  - Iterates every fixture in `tests/llbc/*.cert.json`.
  - For each, emits L₀ via mainline `bin/aeneas -backend lean -dest
    /tmp/aeneas-out-<fixture>/` and L₁ via `aeneas-check
    --out /tmp/checker-out-<fixture>.lean`.
  - Diffs L₀ and L₁ byte-by-byte.
  - Classifies: **pass** (byte-identical), **divergent** (mismatched
    but listed in known-divergent), **mismatch** (mismatched and
    unlisted — surfaces as a fail), **skip** (L₀ or L₁ emit failed
    upstream).
  - Prints a Markdown table summary + exits non-zero on any
    unlisted mismatch.
- Initial population of `known-divergent.txt`: expect 40–60 entries
  (whitespace, banner differences, hand-rolled instance ordering).
  Each entry one line: `<fixture>: <reason>`.

**Why this is cheap and useful.** The plan §"Why this is cheap and
useful" already makes the case. Byte-equal coverage is a strong
signal — if L₀ and L₁ are textually equal, then any property
mainline's Lean satisfies, ours does too. The 89-fixture sweep
already runs cert pipeline and lake build; adding a parallel
mainline emit + diff is linear additional time.

CI integration deferred to Phase 5 (per the plan); just produce a
working `--sweep` mode for now.

### Item 3 — Generic-aware global propagation (~half day stretch)

Session 5's `seedGlobalRefsFromBlock` skips globals whose name
carries `<` (a generic-instantiation marker) because the cert events
don't surface the caller's generic args. The classic missed case:

  ```rust
  pub fn use_v<const N: usize, T>() -> usize {
      V::<N, T>::LEN
  }
  ```

Emits `def use_v {T : Type} : Result Std.Usize := do ok 0#usize`
(placeholder) instead of `do constants.V.LEN` because the seed pass
filters globals with `<` in the name.

The right fix is OCaml-side: surface the resolved
`global_decl_ref.generics` in the cert JSON, then thread them
through the Lean call. **Where to look:**

1. `src/cert/LlbcJson.ml::global_decl_ref_name` (new in Session 5)
   currently calls `Print.name_to_string env def.item_meta.name`,
   which folds the generic args into the printed path. We probably
   want both the generic-free *qualified name* and the generic args
   structured separately.
2. The Lean parser's `LlbcPlace` would gain a
   `globalGenerics : Option (Array String)` or similar, and the
   seed pass would emit a typed call.

**Acceptance criteria:**

- `use_v` emits a body that reads `V.LEN` with the appropriate
  implicit type instantiation (matching mainline's `V.LEN T N`
  shape after Session 5's view of mainline).
- Add a `use_v` vector to ConstantsRunner (5 + the existing 37 ⇒
  42 constants vectors).

**Pitfall**: the standard backend renders `V::LEN<T, N>` as
`V.LEN (T : Type) (N : Std.Usize)` (explicit type + const-generic
params). The shim's current `V.LEN {T : Type} : Result Std.Usize`
emit uses implicit `{T}` only and drops `N` entirely. Bringing the
shim in line with mainline would need both the seed pass change
*and* a Forward.lean change to recover the const-generic params
from the cert. If the const-generic recovery is too big, settle for
a `V.LEN T` call (implicit `T` ⇒ explicit) and document the
N-drop as a known divergence.

### Item 4 — Cross-fixture mod-crate wraps (~1 hour per fixture stretch)

If Item 1 + 2 are too big or fast, the Session-3 + Session-4
mod-crate-wrap pattern is a 1-hour-per-fixture grind that scales
G_rust steadily. Candidates:

- `nested_borrows::call_inner_mut` (skipping closure-returning
  callees)
- `no_nested_borrows::test2` / `test3` (skipping the assertion
  bodies, which Charon turns into Result panic returns that don't
  diff-test cleanly)
- `paper::ref_incr` (existing `paper::add_borrowed` works fine)
- `iterators-scalar::*` (simple primitive iteration)

Each is `mod <crate> { ... }` in `src/model.rs` mirroring the
auto-generated emit, plus proptests in `tests/diff.rs`.

## What's NOT in this handoff

- **Phase 3** (G_rfl harness) — still deferred. Items 1 + 2 + 3
  will surface the next blockers there.
- **Phase 5** (CI integration) — still deferred.
- **Show1 instances for `Pair` / `Wrap`** — the long-standing
  blocker for the constants fixture's ADT-returning fns (`P3`, `S3`,
  `S4`, `Y`). Add when convenient; not Session 6's main scope.

These remain subsequent sessions.

## Done condition for this session

- Item 0 complete: all 89 cert.json regen'd, harnesses still passing.
- Item 1 complete: cast keyword + `get_max` branch fix landed, with
  at least 4 new G_rust proptests in `no_nested_borrows`.
- Item 2 complete OR Item 3 complete (your choice). Item 2 is the
  higher-impact one; Item 3 is the more localised one and a good
  fallback if Item 2 hits an unexpected mainline-Aeneas wrinkle.
- Item 4 if neither blows up.
- `differential-testing-plan.md` §Gates fixture counts updated.
- `differential-testing-progress.md` appended with a Session 6 note
  following the established structure (commit summary, per-item
  outcome, bug table, coverage matrix snapshot, carry-forward list).
- Branch ready to merge back to parent. Run `git merge
  aeneas-lean-certificate` mid-session if the parent has moved.

## Push policy

Local commits only. Do NOT push to origin. The user pushes manually
when ready, after running `/lean4:checkpoint` to satisfy the Lean
guardrail hook.
