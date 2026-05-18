# Autonomous campaign — eliminate all 19 remaining `--skip-decl` flags

Paste into a fresh Claude Code session at `/Users/karthik/aeneas`.
Execute autonomously: do not ask clarifying questions; commit between
steps; only stop on the documented hard-stop conditions.

---

You are running a campaign to drive the count of `--skip-decl` flags in
`tests/lean-checker/lean-diff/scripts/run-diff.sh` from **19 to 0**, in
priority order, on branch `aeneas-lean-certificate-diff-test` in
worktree `/Users/karthik/aeneas/.claude/worktrees/diff-test`.

## Boot sequence — read in order, do not skip

1. **`documentation/plans/zero-skip-plan.md`** — the canonical backlog.
   Seven sequenced cluster fixes (Step 1 through Step 7). Each step
   has: cluster name, decls unlocked, fix surface, estimated work,
   acceptance criterion. Treat the step numbering as a hard ordering;
   do NOT reorder.
2. **`documentation/plans/skip-decl-audit.md`** — the underlying
   per-decl audit. Use the "Concrete error (first line)" column in
   §2 to know what error to expect when you re-emit a decl without
   its skip flag. Use §2.2 (root-cause clustering) to confirm a fix
   resolved its cluster's decls before moving on.
3. **`documentation/plans/differential-testing-progress.md`** §"Session
   7" — for context on the param-naming / generic-globals / sweep
   work the prior session committed. Don't try to relitigate Session 7
   choices; build on them.
4. **Recent commits on the branch**:
   ```
   git log --oneline aeneas-lean-certificate-diff-test -8
   ```
   Top of log should be the inline cleanup commit removing the three
   mis-skipped flags (`demo::choose`, `paper::test_incr`,
   `paper::choose`), then the Session 7 commits. If HEAD does not
   look like that, abort with a status report — something is wrong.

## Critical operational constraints

Same as Session 7. Restated:

- **Parent-branch read-only.** Do NOT touch any file under
  `aeneas-lean-soundness/` or `aeneas-lean-checker/AeneasCheck/Theorems/`.
  These belong to the M10 soundness agent. If a fix would require
  changes to those paths, abort the step and document the blocker in
  `zero-skip-plan.md`.
- **Worktree isolation.** Work in
  `/Users/karthik/aeneas/.claude/worktrees/diff-test`, never in
  the parent tree. For any agent dispatch with `isolation: worktree`,
  the FIRST Bash call MUST be `echo "[status] boot" && pwd && git log
  -1 --oneline && git branch --show-current`. If HEAD is not in the
  diff-test branch's ancestry, abort with a clear report — do NOT
  fall back to editing the live worktree.
- **Pre-built binaries lie.** Rebuild both binaries from this worktree
  before each step's "regen + re-run" check:
  ```bash
  cd src && opam exec -- dune build
  cd /Users/karthik/aeneas/.claude/worktrees/diff-test/aeneas-lean-checker && lake build aeneas-check
  ```
- **Streaming-watchdog guard.** Every Bash call preceded by `echo
  "[status] ..."` so the 600s no-stream-output watchdog doesn't kill
  long builds.
- **Local commits only.** Do NOT push to origin. The user pushes
  manually after the campaign closes.
- **Periodic parent merge.** At session start AND if the campaign
  spans multiple sessions, run `git merge aeneas-lean-certificate
  --no-edit` to keep merge-back cost low. If the merge has conflicts,
  resolve them in `Translate/Forward.lean` / `LLBCSharp/Step.lean`
  cautiously — these are the ones the soundness agent touches.

## Per-step protocol

For each step N in `zero-skip-plan.md` (in order, from 1 to 7):

1. **Read the step's section.** Note the cluster name, the decls it
   unlocks, the fix surface, and the acceptance criterion (which
   `--skip-decl` flags to remove).

2. **Confirm the symptom.** Regen the affected fixture WITHOUT
   removing the flag yet:
   ```bash
   src/_build/default/main.exe -emit-cert tests/llbc/<fx>.llbc
   aeneas-lean-checker/.lake/build/bin/aeneas-check tests/llbc/<fx>.cert.json \
     --out /tmp/<fx>-full.lean
   # then mock the diff harness's lake build against the unfiltered file
   ```
   Compare the actual first-line error against the audit's "Concrete
   error" entry. If they differ substantially, the audit is stale —
   record the new error in `zero-skip-plan.md`'s step section as a
   nested note and proceed with the fix targeting the actual symptom.

3. **Implement the fix.** Follow the "Fix surface" guidance in
   `zero-skip-plan.md` for the step. Touch ONLY the files the step
   identifies; do not refactor adjacent code.

4. **Rebuild + regen + verify.** Build aeneas-check, regen every
   cert under `tests/llbc/*.llbc` (some clusters affect multiple
   fixtures), then run the diff harness:
   ```bash
   bash tests/lean-checker/lean-diff/scripts/run-diff.sh
   ```
   The harness should still PASS — note Lean-line count delta.

5. **Remove the corresponding `--skip-decl` flags.** Edit
   `tests/lean-checker/lean-diff/scripts/run-diff.sh`. The step's
   acceptance criterion names exactly which flags to drop. Re-run
   the diff harness. Expected outcome:
   - **PASS, Lean-line count unchanged**: the decl compiles but no
     runner exercises it. Acceptable. The runner can be added in a
     follow-up; the win is that future regressions on this decl will
     surface as a lake build failure.
   - **PASS, Lean-line count grew**: a runner that was previously
     calling a related decl now picks the un-skipped one up. Also
     acceptable.
   - **FAIL with lake build error**: the cluster fix was incomplete.
     Iterate: read the error, refine the fix, rebuild, re-test.
   - **FAIL with byte-stream mismatch**: the un-skipped decl's
     behavior differs from the Rust oracle. This is real signal,
     not a regression — investigate. Most likely the decl needs a
     corresponding Rust mirror in `rust-runner/src/main.rs` AND a
     runner vector entry, OR the emitted decl has a semantic bug
     that was masked by the skip.

6. **Run G_byte sweep + G_rust as sanity checks.** A cluster fix
   could accidentally regress unrelated fixtures:
   ```bash
   bash scripts/compare-backends.sh --sweep | tail -2
   cd tests/lean-checker/differential && cargo test --release | grep "test result"
   ```
   G_byte: pass count must not decrease (currently 3/89). G_rust:
   all 44 proptests must still pass.

7. **Commit.** One commit per step, message format:
   ```
   Zero-skip Step N (cluster <name>): unlock <K> decls in <fixtures>

   <one-paragraph summary of the fix>

   <one-paragraph what changed in run-diff.sh>

   Decl counts: <prev> → <new> skips (target: 0).
   G_lean: <prev lines> → <new lines>.
   G_byte: <unchanged or new pass count>.
   G_rust: 44 (unchanged).

   Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
   ```

8. **Update `zero-skip-plan.md`.** Mark Step N as DONE; record
   actual work time vs estimate; note any nested findings worth
   carrying forward.

## Hard-stop conditions

Stop the campaign and write a status report (do NOT commit a
partially-failed step):

- **A cluster fix would touch `aeneas-lean-soundness/` or
  `AeneasCheck/Theorems/`.** That's parent-branch territory; the
  M10 agent owns it. Document the dependency in `zero-skip-plan.md`
  and skip to the next step (mark the blocked step DEFERRED).
- **A cluster fix would require a Charon-side change.** Charon lives
  at `/Users/karthik/charon`, a separate repo. Same rule: document
  the dependency, skip to next step.
- **A cluster fix takes >2x its estimate.** Step 3 (`recursive_match_arm_scoping`)
  is estimated at half a day. If you've spent a full day on it and
  the decls still don't compile, stop and write a "what we tried
  and why it didn't work" note in the step's section. Move on to
  later steps if their fixes are independent (most are).
- **G_rust regresses.** Any proptest failure is hard-stop. Revert the
  step's commit and investigate.
- **G_byte pass count drops.** A previously byte-identical fixture
  diverging is hard-stop. Same recovery.
- **A step's acceptance criterion can't be met because the
  un-skipped decl exposes a new bug downstream.** Document the new
  bug in `zero-skip-plan.md` under a new "Step N follow-up"
  subsection; either fix it inline if cheap, or skip the step and
  mark BLOCKED.

## What "done" looks like

- `grep --skip-decl tests/lean-checker/lean-diff/scripts/run-diff.sh`
  produces zero output.
- All three `<fixture>.lean` files in
  `tests/lean-checker/lean-diff/generated/` are full regens with no
  filtering.
- The diff harness still PASSes.
- G_byte sweep: pass count >= 3 (the post-Session-7 baseline).
- G_rust: 44 / 44.
- `zero-skip-plan.md` has all 7 steps marked DONE with actual
  work-time notes.
- One follow-up commit cleans up: remove the `--skip-decl` CLI
  plumbing if no caller uses it anymore (check
  `aeneas-lean-checker/AeneasCheck/Cli.lean` and
  `aeneas-lean-checker/AeneasCheck/Backends/LeanEmit.lean`).
- A final progress-note entry in
  `documentation/plans/differential-testing-progress.md`
  ("Zero-Skip Campaign — completed YYYY-MM-DD") with the same
  shape as the Session 7 entry: commit summary, per-step outcome,
  bug table, coverage snapshot, carry-forward.

## What "almost done" looks like

If you hit hard-stops on steps 3, 4, or 5 (the half-day-or-more
fixes) but completed steps 1, 2, 6, 7, the campaign has still
landed real value: ~6 decls unlocked, no regressions, the cheap
fixes done. Document the remaining clusters' blockers in
`zero-skip-plan.md`, commit a "Zero-Skip Campaign — partial" note,
and stop. The next session can pick up the deferred steps with
fresh context.

## Quick reference — useful commands

```bash
# Boot guard
cd /Users/karthik/aeneas/.claude/worktrees/diff-test
pwd && git log -1 --oneline && git branch --show-current

# Rebuild both binaries (do after every fix)
( cd src && opam exec -- dune build )
( cd aeneas-lean-checker && lake build aeneas-check )

# Regen all certs (after OCaml changes)
for f in tests/llbc/*.llbc; do
  src/_build/default/main.exe -emit-cert "$f" >/dev/null 2>&1
done

# Run gates
bash tests/lean-checker/lean-diff/scripts/run-diff.sh
bash scripts/compare-backends.sh --sweep | tail -2
( cd tests/lean-checker/differential && cargo test --release | grep "test result" )

# Single-fixture aeneas-check probe (without skip flags)
aeneas-lean-checker/.lake/build/bin/aeneas-check \
  tests/llbc/<fx>.cert.json --out /tmp/<fx>-probe.lean

# Single-fixture lake build probe (to confirm error)
( cd tests/lean-checker/lean-diff && lake build +<fx> )

# Compare cert format / event traces between fixtures
python3 -c "import json; print(json.dumps(json.load(open('tests/llbc/<fx>.cert.json'))['functions'][0]['events'][:10], indent=2))"
```

## Push policy

Local commits only. Do NOT push to origin. After the campaign closes
the user pushes manually after running `/lean4:checkpoint` to satisfy
the Lean guardrail hook.
