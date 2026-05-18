# Handoff prompt — Phase 4: scale differential coverage

Paste into a fresh Claude Code session at `/Users/karthik/aeneas`.

---

You are continuing the four-artifact differential testing rollout for
Aeneas on branch `aeneas-lean-certificate-diff-test`. Phases 0 + 1 are
complete and merged to the parent branch `aeneas-lean-certificate`.
Your job is Phase 4: scale G_rust and G_lean from their current
~7-fixture coverage to ~30 each.

Work in the worktree at `/Users/karthik/aeneas/.claude/worktrees/diff-test`,
NOT in the parent tree.

## Boot sequence — read in order

1. **The plan**:
   `documentation/differential-testing-plan.md` — four artifacts (R₀ R₁
   L₀ L₁), six pairwise comparisons collapsing to four primary gates
   (G_rust, G_lean, G_byte, G_rfl). §"Phased rollout" §"Critical files".
2. **Session 2 progress note**:
   `documentation/differential-testing-progress.md` — what landed in
   Phases 0+1, the operational lessons learned, the carry-forward
   LeanEmit follow-ups in `constants.lean` (these are your first
   targets).
3. **Recent commits on the branch**:
   ```
   git log --oneline aeneas-lean-certificate-diff-test -15
   ```
   You should see merge commit `64ef5adb` at HEAD, with 11 Phase 0+1
   commits + M10's `7f07f8f0` / `f3761dc7` below it.
4. **Existing harnesses**:
   - G_rust: `tests/lean-checker/differential/` — 7 fixtures / 18 proptests
   - G_lean: `tests/lean-checker/lean-diff/` — 4 fixtures / 90 vectors

## Critical operational constraints (lessons from prior sessions)

These were learned the hard way and the prompt enforces them:

- **The M10 soundness agent is actively committing to
  `aeneas-lean-certificate` (the parent branch).** All your work
  belongs on `aeneas-lean-certificate-diff-test`. Do NOT touch any file
  under `aeneas-lean-soundness/` or
  `aeneas-lean-checker/AeneasCheck/Theorems/`. The parent gets merged
  into your branch every now and then; never the other way without
  explicit user say-so. Treat the parent as read-only input.

- **Worktree isolation is fragile.** In Session 2, three of four
  dispatched agents found their isolated worktrees pinned to a stale
  release-nightly commit (`004e11fe`, predating `aeneas-lean-checker/`).
  Two of them bailed out of isolation and committed directly to the
  diff-test worktree instead of aborting. **For every agent dispatch
  with `isolation: worktree`**: the FIRST Bash call must be
  `echo "[status] boot" && pwd && git log -1 --oneline && git branch --show-current`.
  If HEAD is `004e11fe` or any commit not in the diff-test ancestry,
  the agent MUST abort with a clear report — NOT fall back to editing
  the live worktree. The handoff should also instruct the agent how to
  recover (`git fetch && git checkout aeneas-lean-certificate-diff-test
  && git reset --hard <known-good-HEAD>`).

- **Pre-built binaries can lie about which branch they came from.**
  In Session 2, `/Users/karthik/aeneas/aeneas-lean-checker/.lake/build/bin/aeneas-check`
  had a recent timestamp but did NOT contain a fix committed to the
  diff-test branch. The binary was built from the parent branch's
  source. **Don't trust pre-built binaries to contain branch-specific
  fixes.** If an agent needs a fix that landed on diff-test, it should
  rebuild aeneas-check in its own worktree:
  `cd aeneas-lean-checker && lake build aeneas-check`.

- **Cert JSON v6 is the current format.** `bin/aeneas -emit-cert` emits
  v6 (with `holderLocal`, `JoinEntryDelta`, `stmtRefs`); the cert
  parser in `aeneas-lean-checker/AeneasCheck/Json/Parser.lean` has full
  v6 support after the parent merge.

- **Streaming-watchdog guard**: every Bash call should be preceded by
  an `echo "[status] ..."` line so the 600s no-stream-output watchdog
  doesn't kill long builds.

- **Pre-built binaries that are safe to use by absolute path**
  (assuming you don't need a diff-test-only fix):
  - `/Users/karthik/aeneas/bin/aeneas`
  - `/Users/karthik/aeneas/aeneas-lean-checker/.lake/build/bin/aeneas-check`
    (rebuilt regularly by the M10 agent on the parent branch)

## Scope of Phase 4

The plan calls for ~30 fixtures each in G_rust and G_lean. Current
state: 7 / 4 distinct fixtures, of 89 cert-tracked / 93
source-tracked fixtures available. You won't finish all of Phase 4 in
one session — the plan estimates ~1 week. Plan to land ~10–15 new
fixtures and leave a clear baton for the next session.

### Phase 4a — Unblock `constants.lean` (G_lean), ~2 hours

The G_lean harness has `constants.lean` regenerated but NOT wired in
because four independent LeanEmit gaps remain. Each unblocks a class
of fixtures, so prioritize these before scaling. From
`differential-testing-progress.md` §"Carry-forward LeanEmit follow-ups":

1. Bare `(x1 + x2)` on i32 `add` — no `HAdd I32 I32 (Result I32)`
   shim instance. Either add the missing instance to
   `aeneas-lean-checker/RuntimeShim/Aeneas/Std.lean`, or have LeanEmit
   render `Std.I32.add x1 x2` instead of `(x1 + x2)`. Pick the shim
   approach (parallels how Phase 1A added `#isize`).
2. Brace-decorated identifier `def {constants.Wrap<T>}.new` — invalid
   Lean syntax. Mirror Phase 1C's brace-sanitization fix in
   `aeneas-lean-checker/AeneasCheck/Backends/LeanEmit.lean` (it
   already exists in `RustEmit.lean` as `sanitizeRustPath`).
3. `Pair Std.U32 Std.U32`-typed record literal `ok`-applied as a
   scalar — type-flow bug in LeanEmit for `S1` / `S2` constants.
4. `V` struct shape `Array T 0#usize` — wrong length literal. Cert
   carries the actual array length but LeanEmit is dropping it.

Land each as a separate commit. After all four, wire `constants.lean`
into `tests/lean-checker/lean-diff/` (mirror how `bitwise.lean` is
wired in `lakefile.lean` / `LeanDiff/Main.lean`) and verify the diff
harness still passes.

### Phase 4b — Batch add "easy" fixtures, ~6–8 hours

Pick fixtures from `tests/llbc/*.cert.json` that:
- Have NO closures, dyn traits, or generics-with-trait-bounds
- Have a simple cargo-buildable `tests/src/*.rs` (no nightly-only
  features, no external crates beyond what's already wired)
- Generate clean `aeneas-check --rust-model` output (parse-checkable
  with `rustc --crate-type=lib --edition=2021`)
- Generate clean `aeneas-check --out` Lean output (`lake build`
  succeeds against the existing `RuntimeShim`)

Sweep the 89 cert fixtures to identify candidates:
```
for cert in tests/llbc/*.cert.json; do
  name=$(basename "$cert" .cert.json)
  echo "=== $name ==="
  /Users/karthik/aeneas/aeneas-lean-checker/.lake/build/bin/aeneas-check \
    "$cert" --rust-model "/tmp/$name.rs" 2>&1 | tail -3
  rustc --crate-type=lib --edition=2021 --emit=metadata \
    -o /dev/null "/tmp/$name.rs" 2>&1 | tail -3
done
```

Classify into:
- **green** (both succeed): add proptests
- **rustc-only fail**: emitter bug to file; skip
- **aeneas-check fail**: cert-side gap; skip

Target ~10–15 new fixtures landed in G_rust, with ~3 proptests each
(input range edge cases — small, full, top of range). For ADTs use
the Phase 1C per-fixture-module pattern; for flat fixtures use the
`ref_impl` / `model` flat-namespace pattern. Both live in
`tests/lean-checker/differential/src/lib.rs`.

For G_lean, pick a subset of the green fixtures and emit hardcoded
test vectors per `LeanDiff/BitwiseRunner.lean` style. Each new
fixture wires into `lakefile.lean` and `LeanDiff/Main.lean`.

### Phase 4c — Update fixture-count tally, ~30 min

Update `documentation/differential-testing-plan.md` §"Gates" fixture
counts and the §"Phased rollout" Phase 4 status. Add an entry to
`documentation/differential-testing-progress.md` for Session 3.

## Multi-agent orchestration (optional)

If you want to parallelize, the four `constants.lean` fixes are
independent and could be dispatched as separate agents. But each is
small enough (~30-60 LOC) that a single agent can probably knock them
out in sequence within ~2h. The fixture-sweep work (4b) is harder to
parallelize because conflict-prone: every fixture touches
`lib.rs` / `tests/diff.rs` / `lakefile.lean`.

**If you do dispatch agents**: include the FULL HEAD-verification
guard (echo "[status] boot" && pwd && git log -1 ... and abort on
stale HEAD) in every prompt. See lessons-learned in
`differential-testing-progress.md`.

## What's NOT in this handoff

- **Phase 2** (G_byte sweep extension)
- **Phase 3** (G_rfl harness)
- **Phase 5** (single-command sweep + CI integration)

These are subsequent sessions.

## Done condition for this session

- Phase 4a complete: 4 LeanEmit fixes landed; `constants.lean` wired
  into the G_lean harness; diff harness still byte-identical.
- Phase 4b: ~10–15 new fixtures in G_rust (≥30 fixtures total is the
  ultimate Phase 4 target; partial progress is fine).
- `differential-testing-plan.md` fixture counts updated.
- `differential-testing-progress.md` appended with a Session 3 note
  (or new `differential-testing-session3.md` if you prefer).
- Branch ready to merge back to parent (the prior session showed that
  a periodic merge of parent into your branch keeps the eventual
  merge-back cost low — do this at least once mid-session).

## Push policy

Local commits only. Do NOT push to origin. The user pushes manually
when ready, after running `/lean4:checkpoint` to satisfy the Lean
guardrail hook.
