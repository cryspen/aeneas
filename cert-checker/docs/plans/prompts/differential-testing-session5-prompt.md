# Handoff prompt — Session 5: cert-walker S3 fix + demo wire-in + Phase 4b stretch

Paste into a fresh Claude Code session at `/Users/karthik/aeneas`.

---

You are continuing the four-artifact differential testing rollout for
Aeneas on branch `aeneas-lean-certificate-diff-test`. Phases 0 + 1 +
4a are complete; Phase 4b is now well-scaled (G_rust 39 proptests
across 11 fixtures, G_lean 224 vectors across 6 fixtures). Session 4
landed Item 1 (scalars G_lean), Item 4a (demo intra-crate G_rust),
and Item 4b (enum-ctor `::` fix in RustEmit). Items 2 (demo G_lean
wire-in) and 3 (S3-class cert walker) deferred — your job picks them
up.

Work in the worktree at `/Users/karthik/aeneas/.claude/worktrees/diff-test`,
NOT in the parent tree.

## Boot sequence — read in order

1. **Plan**:
   `documentation/plans/differential-testing-plan.md` — read §"Gates"
   (fixture counts now G_rust 39 / 11, G_lean 224 / 6) and §G_lean /
   §G_rust "Known unblockers". Session 4 added the `rustifyPath`
   entry on the G_rust side and the scalars wire-in entry on G_lean.
2. **Progress note**:
   `documentation/plans/differential-testing-progress.md` — §"Session
   4 (2026-05-18)" is the canonical handoff source. Pay attention to:
     - Item 1 outcome — what shim instances landed; cast-`CoeHead`
       table; the LeanEmit pure-binop letBind detection.
     - Item 2 deferral — the four demo emit gaps blocking wire-in.
     - Bugs-found table (§"Bugs found by the differential pipeline
       (Session 4)") — the one real RustEmit bug + the emit-side
       gaps surfaced.
     - §"Carry-forward into Session 5" — five items in priority order.
3. **Recent commits on the branch**:
   ```
   git log --oneline aeneas-lean-certificate-diff-test -10
   ```
   Top of the log should show `ac810866 docs: Session 4 progress
   note`, then `644e4336 Phase 4b Item 4a: scale G_rust — demo`,
   then `c84781e4 Phase 4b Item 4b: RustEmit Type.Ctor → Type::Ctor`,
   then a parent-merge commit, then `6539a087 Phase 4b Item 1: scale
   G_lean — add scalars fixture`. Below those: the Session-3 stack.
4. **Existing harnesses**:
   - G_rust: `tests/lean-checker/differential/` — 39 proptests / 11 fixtures
   - G_lean: `tests/lean-checker/lean-diff/` — 224 vectors / 6 fixtures

## Critical operational constraints

Same as Session 2/3/4. Restated verbatim because they keep mattering:

- **The M10 soundness agent commits to `aeneas-lean-certificate` (the
  parent branch).** All your work belongs on
  `aeneas-lean-certificate-diff-test`. Do NOT touch any file under
  `aeneas-lean-soundness/` or `aeneas-lean-checker/AeneasCheck/Theorems/`.
  The parent gets merged into your branch every now and then; never
  the other way without explicit user say-so. Treat the parent as
  read-only input.

- **Worktree isolation is fragile.** Three of four agents dispatched
  in Session 2 found their isolated worktrees pinned to a stale
  release-nightly commit (`004e11fe`) predating
  `aeneas-lean-checker/`. **For every agent dispatch with
  `isolation: worktree`**: the FIRST Bash call must be
  `echo "[status] boot" && pwd && git log -1 --oneline && git branch --show-current`.
  If HEAD is `004e11fe` or any commit not in the diff-test ancestry,
  the agent MUST abort with a clear report — NOT fall back to editing
  the live worktree. Sessions 3 + 4 did all work inline (no agent
  dispatches), so the issue didn't recur; if you choose to
  parallelise, this guard is still mandatory.

- **Pre-built binaries can lie.** Sessions 3 + 4 rebuilt aeneas-check
  from the diff-test worktree's source before every regen. Do the
  same — the May-18 timestamp on `.lake/build/bin/aeneas-check` is
  no evidence that the binary contains diff-test-only fixes.

- **Cert JSON v6 is the current format.** `bin/aeneas -emit-cert`
  emits v6; the cert parser
  (`aeneas-lean-checker/AeneasCheck/Json/Parser.lean`) has full v6
  support after Phase 0's `235d8753`.

- **Streaming-watchdog guard**: every Bash call should be preceded by
  an `echo "[status] ..."` line so the 600s no-stream-output watchdog
  doesn't kill long builds.

- **Pre-built binaries that are safe to use by absolute path**
  (assuming you don't need a diff-test-only fix):
  - `/Users/karthik/aeneas/bin/aeneas`

- **Periodic parent merge**: `git merge aeneas-lean-certificate`
  mid-session keeps the eventual merge-back cost low. Session 4 did
  it once cleanly (M10.x.3/4/5 axiom-drop commits — pure soundness
  territory). Do it at least once.

## Scope of Session 5

Four items, in priority order. Land #1 (the cert-walker S3 fix)
first; it's the highest-leverage / most-instructive fix on the table.

### Item 1 — Cert-walker fix for `S3`-class static placeholders (~half day)

This is a `Translate/Forward.lean`-layer fix, NOT an emit or shim
fix. Symptom (carried over from Session 3):

  `static S3: Pair<u32, u32> = P3;`

emits

  `def S3 : Result (Pair U32 U32) := do ok { x := 0#u32, y := 0#u32 }`

i.e. the value is correctly typed but the placeholder zeros are used
instead of `P3`'s value `{ x: 0, y: 1 }`. Same shape across:

  - `X1 = u32::MAX` → `ok 0#u32` (placeholder, not max)
  - `Q2 = Q1` → `ok 0#i32` (placeholder, not 5)
  - `S2 = incr(S1)` → `ok 0#u32` (placeholder)
  - `S3 = P3` → `ok { x := 0, y := 0 }` (placeholder for both fields)
  - `Q3 = add(Q1, 3)` → `ok 0#i32` … etc.

The unifying pattern is "static / const whose initialiser reads
another global". The cert walker's `EvAssign` case has several
sub-branches; the one that handles "RHS is a global getter" is
either missing or falling through to a typed-zero default.

**Where to look:**

1. `aeneas-lean-checker/AeneasCheck/Translate/Forward.lean`'s
   `EvAssign` case. Search for `EvAssign` and trace the dispatch.
2. The cert JSON: `tests/llbc/constants.cert.json`. Find the events
   list for `S3` / `X1` / `Q2` — that's the canonical input.
3. Compare against a *working* case: the `X0 = 0` const works
   correctly (`ok 0#u32` is the right answer). What does its event
   list look like vs `X1 = u32::MAX`?

Hypothesis: the cert is emitting an `EvCall(<global-getter>)` event
or an `EvGlobal` event that the walker doesn't route through the
local-value map. Confirm by inspecting events for the simplest case
first (`X1` — single integer, no ADT).

**Acceptance criteria:**

  - `X1` emits `ok 0xFFFFFFFF#u32` (or whatever the cert's source
    value is — verify against `tests/src/constants.rs`).
  - `Q2` emits `ok 5#i32` (matching `Q1`).
  - `S2` emits a non-placeholder body.
  - `S3` emits `ok { x := 0#u32, y := 1#u32 }`.
  - `LeanDiff.ConstantsRunner` regains the now-unblocked nullary
    consts (X1, Q2, Q3, S2, S3, etc.) — add ~10 new vectors.

**Pitfall:** the `c59c91ed`-Phase-4a-3 typed-placeholder logic in
`LeanEmit.lean` was the *band-aid* for this — keep it in place so
fixtures that genuinely need a placeholder (truly opaque external
state) still typecheck. Your fix is upstream of it.

### Item 2 — `demo.lean` wire-in via per-decl skip (~half day)

`demo.lean`'s regen has five differential-testable fns (`mul2_add1`,
`incr`, `use_mul2_add1`, `use_incr`, `mod_add`) but the surrounding
defs are emit-broken in four distinct ways:

| Broken def | Issue |
|---|---|
| `CList` inductive | `@[discriminant isize]` is not a known Lean attr |
| `Std.Usize.Insts.DemoCounter.incr` | returns `Result (Usize × (Unit → Usize))`, but the `Counter` trait field expects `Self → Result Usize` |
| `list_nth` / `list_nth_mut` / `list_tail` / `list_nth1_loop.body` / `i32_id` | broken bodies: `ok ()` where `T` expected, `if x1` on a non-bool, undefined `s33` / `t3`, `partial_fixpoint` on non-recursive |
| `choose` | returns closure (M12.2a placeholder) |

Two paths forward:

**(a) Cheap — per-fixture include-only Lake setup.** Don't ask
`aeneas-check` to elide anything; instead change `Generated.demo`'s
Lake roots so only the well-emitted fns are imported. Concretely: hand-
write a `tests/lean-checker/lean-diff/generated/demo_subset.lean`
that contains *only* the five well-emitted defs (copy-pasted from
the auto-generated `demo.lean`), plus a regen note explaining why.
The runner imports `demo_subset` rather than `demo`. Brittle — drifts
if the cert changes — but localised.

**(b) Heavier — emit-side per-decl skip list.** Add a CLI flag
`--skip-decl <name>` to `aeneas-check` (parsed once, threaded to
`emitTranslatedCrate`), so the emitter drops the named decls. Adopt
in `scripts/run-diff.sh`'s regen invocation with a hardcoded skip
list per fixture. Cleaner but touches CLI surface; better for
long-term scaling.

Recommended (b) — the skip list will scale as you add more fixtures
in Phase 4. The CLI flag plumbing is ~30 LOC across `Cli.lean` and
`Backends/LeanEmit.lean`.

After either: write `LeanDiff.DemoRunner` (mirror `BitwiseRunner` —
similar U32-in/U32-out shape), add ~15 new vectors. The Rust oracle
already has `demo_mul2_add1`/`demo_incr` plus the new Session-4
`mod demo::{mul2_add1, use_mul2_add1_model, mod_add_model}` (G_rust
side); reuse those exact bodies for the Lean-diff Rust runner.

### Item 3 — Cast-keyword emit fix (~half day)

The cert walker drops `as`-casts; `cast_u32_to_i32_model(x1: u32)
-> i32 { x1 }` is the symptom (and is syntactically invalid Rust).
Companion bug: `get_max_model(x1: u32, x2: u32) -> u32 { let t0 =
(x1 >= x2); if x1 { x1 } else { x2 } }` — the `if` should use `t0`,
not the original scrutinee `x1`. Both happen at the cert-walker
layer, not RustEmit.

Where to look:

1. `Forward.lean`'s handling of `Rvalue::Cast` (or whatever Charon
   names it; the variant name appears in the cert JSON event list).
   Currently the walker probably elides the wrapper and threads the
   inner operand straight through.
2. `Forward.lean`'s if/match lowering — the precomputed boolean
   `t0` is the right scrutinee, but `EvAssign t0` doesn't always
   replace the original branch operand. The `get_max` case is the
   minimal repro.

**Acceptance criteria:**

  - `cast_*` fixtures emit `(x1 as i32)` (Rust) / `(x1.toInt32)`
    (Lean — coerce via the shim's existing `CoeHead`).
  - `get_max::{u32,i32}` emits `if t0 then x1 else x2`.
  - Then in G_rust: wire `no_nested_borrows::{cast_*, get_max,
    test2, refs_test1}` as new proptests (~6 fixtures + maybe more,
    depending on what else this fix unblocks).

If the cert-walker fix is too big to land cleanly, the Session-4
deferred `Coe` shims (already in `RuntimeShim/Aeneas/Std.lean`)
keep the *Lean* side compiling for some narrow cast cases; the
Rust side still won't compile until the emit-level fix lands.

### Item 4 — Phase 2 (G_byte sweep) bring-up (~3 hours)

Lowest-effort highest-signal next gate after Phase 4b stabilises.
Current state:

  `scripts/compare-backends.sh` is interactive, per-fixture — runs
  `bin/aeneas` (mainline) and `aeneas-lean-checker` against the same
  cert and diffs their outputs.

Extend to:

  `scripts/compare-backends.sh --sweep` runs the diff over every
  cert in `tests/llbc/*.cert.json`, classifying each as
  `pass / fail / mismatch / skip`. Mismatches landed in a
  per-fixture allowed-divergence list (`known-divergent.md` shape)
  with a one-sentence reason — same shape as G_rust's existing
  `known-divergent.md`.

CI integration deferred to Phase 5 (per the plan); just produce a
working `--sweep` mode for now. Goal: a single command that surfaces
"how many of the 89 fixtures are byte-identical against mainline."

## What's NOT in this handoff

- **Phase 3** (G_rfl harness) — still deferred. Items 1 + 2 will
  surface the next blockers there.
- **Phase 5** (CI integration) — still deferred.

These remain subsequent sessions.

## Done condition for this session

- Item 1 complete: at least `X1`, `Q2`, `S3` emit the correct value
  (verified by adding their Lean-runner vectors and the G_rust
  proptest equivalents).
- Item 2 OR Item 3 complete (your choice — Item 2 is the cheaper
  win, Item 3 is the higher-impact one). Item 4 if neither blows
  up.
- `differential-testing-plan.md` §Gates fixture counts updated.
- `differential-testing-progress.md` appended with a Session 5 note
  following the established structure (commit summary, per-item
  outcome, bug table, coverage matrix snapshot, carry-forward list).
- Branch ready to merge back to parent. Run `git merge
  aeneas-lean-certificate` mid-session if the parent has moved.

## Push policy

Local commits only. Do NOT push to origin. The user pushes manually
when ready, after running `/lean4:checkpoint` to satisfy the Lean
guardrail hook.
