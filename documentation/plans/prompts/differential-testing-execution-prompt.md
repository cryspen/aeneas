# Handoff prompt — Continue differential-testing rollout

Paste this into a fresh Claude Code session at `/Users/karthik/aeneas`.

---

You are continuing the four-artifact differential testing rollout for
Aeneas on branch `aeneas-lean-certificate-diff-test`. Work in the
worktree at `/Users/karthik/aeneas/.claude/worktrees/diff-test`, not in
the parent tree.

## Boot sequence

Read these in order before dispatching anything:

1. **The plan**: `documentation/differential-testing-plan.md`. Defines
   the four artifacts (R₀ source Rust, R₁ emitted Rust model, L₀
   mainline Aeneas Lean, L₁ our cert-pipeline Lean), the six pairwise
   comparisons collapsing to four primary gates (G_rust, G_lean,
   G_byte, G_rfl), and the phased rollout. §"Phased rollout" §"Bug
   surfacing as a feature" and §"Critical files" are the most load-
   bearing sections.
2. **Recent commits on the branch**: `git log --oneline -5` —
   - `555e4bda docs: Add four-artifact differential testing plan`
   - `3d086b79 RustEmit: strip brace-decorated path segments`
   - `f2520f7f tests: Add Lean execution differential harness`
   - parent: `aeneas-lean-certificate` tip
3. **Existing harnesses to extend**:
   - `tests/lean-checker/differential/` — G_rust proptest harness
     (currently 1 fixture; Phase 0 scales to 5–7)
   - `tests/lean-checker/lean-diff/` — G_lean executed harness (3
     fixtures, 60 vectors; already passing)
4. **Cert-pipeline orientation** (skim, don't read in full):
   - `documentation/verified-pipeline-architecture.md` (pipeline
     overview)
   - `documentation/llbc-sharp-soundness-plan.md` (M10 campaign
     context; M10 agent is actively committing to the parent branch)

## Critical operational constraints

These were learned the hard way in the prior session:

- **The M10 soundness agent is actively committing to
  `aeneas-lean-certificate` (the parent branch).** Do NOT switch the
  main tree to another branch, do NOT touch files under
  `aeneas-lean-soundness/`, do NOT touch
  `aeneas-lean-checker/AeneasCheck/Theorems/`. All your work lives on
  `aeneas-lean-certificate-diff-test` via the diff-test worktree.

- **Worktree isolation occasionally fails.** The prior session saw
  worktrees pinned to a stale commit (`004e11fe`, predating
  `aeneas-lean-checker/`) when the agent expected current-branch HEAD.
  Symptom: the file the agent wants to edit doesn't exist in the
  worktree. **Mitigation**: have every dispatched agent print `git
  log -1 --oneline` and `pwd` as its FIRST Bash call. If the commit
  isn't recent / the file isn't where expected, abort the agent
  immediately rather than letting it fall back to editing the parent
  tree (which one prior agent did — caught after the fact).

- **Pre-built binaries exist in the main tree (use these by absolute
  path, don't rebuild)**:
  - `/Users/karthik/aeneas/aeneas-lean-checker/.lake/build/bin/aeneas-check`
  - `/Users/karthik/aeneas/bin/aeneas`
  - Caveat: `aeneas-check` may have been rebuilt with the brace-path
    fix during the prior session; if your new branch worktree builds
    its own copy of `aeneas-check`, it will incorporate commit
    `3d086b79`'s fix. Agents needing the *fixed* binary should rebuild
    in their worktree (cold; emits per-file progress so watchdog OK).

- **Streaming-watchdog guard**: every Bash call should be preceded by
  an `echo "[status] ..."` line. Prior session lost two agents to the
  600s no-stream-output watchdog mid-build.

## Phase 0 — Recover lost Rust-diff work (~90 min)

Dispatch ONE agent with `isolation: worktree`, background mode. Goal:
recover the 11 proptests / 5 fixtures from the prior session's
unrecoverable worktree, plus the 2 newly-unblocked fixtures.

### Agent prompt for Phase 0

> Extend `tests/lean-checker/differential/` on branch `aeneas-lean-
> certificate-diff-test` from 1 fixture to 6 working fixtures + 13
> proptests. Worktree-isolated; do not push or merge.
>
> Pre-built binaries: `/Users/karthik/aeneas/aeneas-lean-checker/.lake/build/bin/aeneas-check`, `/Users/karthik/aeneas/bin/aeneas`. Use absolute paths; do not rebuild these.
>
> First Bash call: `echo "[status] starting" && git log -1 --oneline && pwd`. If `git log` shows anything other than `555e4bda` or a descendant, abort immediately and report.
>
> Add proptests for (rebuilding the lost work):
> - `constants.rs`: incr, mk_pair0, add (3 tests)
> - `bitwise.rs`: xor_u32, or_u32, and_u32, shift_u32, shift_i32 (5 tests)
> - `compare_simple.rs`: id_u32 (1 test)
> - `calls.rs`: incr_inner (1 test, shim &mut u32 → u32 per cert convention)
>
> Plus the two newly-unblocked by commit 3d086b79 (will need rebuilt aeneas-check):
> - `compare_simple.rs`: add_u32 — was blocked on `core::num::{u32}::wrapping_add` brace-path
> - `calls.rs`: pick — same fix; backward closure case
>
> Use `tests/lean-checker/differential/src/lib.rs` `incr_*` setup as the template. Pattern is: copy source `pub fn` into lib.rs, generate model via `--rust-model`, append model `pub fn` to model.rs, add proptest in tests/diff.rs.
>
> `echo "[status] ..."` every Bash call. Time-box: 90 min.
>
> Report: fixtures landed + cargo test pass count + 1-paragraph note per skipped fixture. Worktree path via `pwd`.

After completion: review the agent's worktree, commit on
`aeneas-lean-certificate-diff-test`, dispose of the worktree.

## Phase 1 — File three emitter bug-fix agents (parallel; ~2h each)

Dispatch THREE agents in parallel, each `isolation: worktree`,
background. Each fixes one bug; each unblocks specific fixtures in
the diff sweeps.

### Phase 1A — RuntimeShim `#isize` macro

> Add the `#isize` macro to `aeneas-lean-checker/RuntimeShim/Aeneas/Std.lean` so that `LeanEmit`'s generated `16#isize` typechecks. Today `RuntimeShim` only registers `#usize` and `#u32`; the committed `aeneas-lean-checker/tests/Generated/Bitwise.lean` was hand-patched to `(16 : Std.Isize)`, masking the drift from gate G3. The fix unblocks `bitwise.rs` in G_lean.
>
> Two acceptable fixes: (a) add `#isize` (and `#i32`, `#i64` for completeness) macros to the shim; (b) change `LeanEmit`'s integer-literal rendering to use the `(N : Std.X)` parenthesised form universally. (a) is narrower; (b) is more idiomatic. Pick (a).
>
> Worktree-isolated; ~2h time-box. Verify by:
> - regenerating `tests/lean-checker/lean-diff/generated/bitwise.lean` via `aeneas-check --out`
> - rebuilding the lean-diff harness with that fixture added
> - running `scripts/run-diff.sh` (in `tests/lean-checker/lean-diff/`) — expect bitwise's vectors to pass
>
> Same worktree-verification protocol as Phase 0.

### Phase 1B — LeanEmit ill-typed constants

> `aeneas-check --out tests/llbc/constants.cert.json` emits a `constants.lean` containing `def unwrap_y : Result Std.I32 := do ok 0#u32.value` and `def get_z1 : Result Std.I32 := do ok 0#u32` — return type `I32` but body U32-typed. Diagnose where the type-mismatch enters (likely in `aeneas-lean-checker/AeneasCheck/Translate/Forward.lean` for the const-evaluation path, or in `Pure/Pretty.lean` for the rendering of `Z1::Z1::Y` and `S1`/`S2` constant shapes).
>
> Fix in the narrowest scope. Verify: regenerate `constants.lean`, add it to `tests/lean-checker/lean-diff/`, expect 3+ vectors passing for the `incr`, `mk_pair0`, `add` functions there.
>
> Worktree-isolated; ~2h time-box. Same verification protocol as Phase 0.

### Phase 1C — RustEmit ADT placeholders (DESIGN DECISION REQUIRED)

> `aeneas-check --rust-model` currently emits `record_lit { f1: e1, f2: e2 }` for record literals and `with_<field>(base, value)` for struct field updates. Neither is valid Rust without hand-written shims. These placeholders block ADT-heavy fixtures from G_rust.
>
> Before fixing: present a design choice. Two paths:
> (a) **Implement real ADT support in RustEmit.** Plumb the struct's qualified name from PExpr or the cert event through to the emit site so `record_lit` becomes `Foo { f1: e1, f2: e2 }` and `with_field` becomes Rust's `Foo { field: value, ..base }`. ~200 LOC; unblocks ~10–15 fixtures.
> (b) **Accept the placeholders permanently.** Document as a Rust-model gap in `tests/lean-checker/differential/known-divergent.md`; ADT fixtures are tested only through G_lean. ~0 LOC; permanent ~10–15 fixture loss in G_rust.
>
> Strong recommendation: (a) — the PExpr struct-name plumbing is the same plumbing other emitters (LeanEmit, the planned Rocq/F* emitters) will need. Investing once pays off across backends.
>
> Implement (a) unless you find a blocker the plan didn't anticipate. Verify by regenerating ADT fixture models (e.g. `adt.rs`, `default.rs`) and confirming `rustc --crate-type=lib --edition=2021` parses them cleanly. Add at least 2 new ADT proptests to `tests/lean-checker/differential/tests/diff.rs`.
>
> Worktree-isolated; ~3h time-box (this one is bigger). Same verification protocol as Phase 0.

After all three complete: review each worktree's changes, commit each
on `aeneas-lean-certificate-diff-test` as separate logical commits,
update `differential-testing-plan.md`'s "known unblockers" sections
to reflect what's fixed.

## What's NOT in this handoff (later sessions)

Phases 2–5 of the differential plan are not scoped here:

- **Phase 2** — G_byte sweep extension to `scripts/compare-backends.sh`
- **Phase 3** — G_rfl harness at `tests/lean-checker/lean-rfl/`
- **Phase 4** — Scale G_rust + G_lean to ~30 fixtures each
- **Phase 5** — Single-command sweep + CI integration

Tackle these in their own sessions, in order. Each is a 2–7 day chunk
of work.

## Done condition for this session

- Phase 0 + Phase 1A + Phase 1B + Phase 1C complete; 4 new commits on
  `aeneas-lean-certificate-diff-test`.
- `differential-testing-plan.md` updated to mark the surfaced bugs as
  resolved (delete or downgrade their entries in the "Known
  unblockers" sub-sections of G_rust / G_lean).
- A short Session 2 wrap-up note appended to either
  `documentation/differential-testing-plan.md` or a new
  `documentation/differential-testing-progress.md` (model after
  `.cert-v3-progress.md`).
- Branch `aeneas-lean-certificate-diff-test` ready to push for review,
  not yet pushed.

## Worktree hygiene reminder

After every successful agent run:
1. Inspect the agent's worktree (`pwd` reported in their final
   message).
2. Copy / cherry-pick changes to your own diff-test worktree.
3. Commit on `aeneas-lean-certificate-diff-test`.
4. Leave the agent's worktree to be cleaned up by the harness.

NEVER let an agent's work sit uncommitted in a transient worktree —
the prior session lost 11 proptests this way.
