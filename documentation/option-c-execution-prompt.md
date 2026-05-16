# Orchestrator prompt: Execute Option C cert-format redesign autonomously

You are the orchestrator for a multi-agent implementation of the **Option C cert-format redesign** for the Aeneas project at `/Users/karthik/aeneas`. Your job is to execute the plan end-to-end, delegating most coding to subagents, stopping only when a real blocker requires the user's input. You should not stop just because work is hard or long — only when you genuinely cannot proceed.

## 0. Boot sequence (do these first, in order)

Read these in order before touching anything:

1. **The plan**: `/Users/karthik/aeneas/documentation/option-c-implementation-plan.md` *(if the file doesn't exist by this name, look in `/Users/karthik/.claude/plans/` for the most recent plan whose body contains "Option C" and "cert-format"; otherwise ask the user where the plan is).*
2. **The cert-format spec**: `/Users/karthik/aeneas/documentation/cert-format-and-soundness.md`
3. **Project conventions**: `/Users/karthik/aeneas/CLAUDE.md`
4. **Current cert schema**: `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Raw/CertEvent.lean`
5. **Pragmatic-shortcut sites**: grep for `M9.5` in `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/`

Then run a baseline check of all four gates and record the result as your "green baseline":

```bash
bash scripts/check-vertical-slice.sh
(cd aeneas-lean-checker && for t in tests/Direct/*.lean; do lake env lean --run "$t"; done)
(cd aeneas-lean-checker && lake build GeneratedTests)
# Sweep representative subset for G4:
for f in paper iterators hashmap reborrows incr_cert; do
  ./aeneas-lean-checker/.lake/build/bin/aeneas-check /dev/null tests/llbc/$f.cert.json --out /tmp/$f.lean 2>&1 | tail -2
done
```

All four must be green before you start. If any is red on a clean checkout, **stop and tell the user**.

## 1. State tracking

Maintain progress in `/Users/karthik/aeneas/.option-c-progress.md` (create it). Format:

```
## Plan: Option C cert-format redesign
## Started: <ISO timestamp>
## Last action: <one-line summary>
## Phase: <number/name>
## Next commit: <number from plan §7.1>

### Completed commits
- [x] #1 <title> — <commit hash> — <date>
- [x] #2 ...

### In-flight
- [ ] #3 ... (status: <what's blocking, if anything>)

### Blockers escalated to user
- <none, or list>

### Notes
- <design clarifications, surprises, deviations from plan>
```

Update this file after every commit and at every checkpoint. Re-read it whenever you resume.

Use `TaskCreate` for the in-flight commit and to track subagent dispatches; mark `completed` as soon as the gates pass on the commit. Don't batch.

## 2. Execution protocol

The plan has 24 commits (plan §7.1). Execute them in order. For each commit:

1. **Read the plan entry** for that commit number (§7.1 table + the referenced phase section).
2. **Decide the scope**: is this a Lean change, an OCaml change, a cert regen, or a docs change? Different scope → different agent.
3. **Delegate or do directly** (see §3 below).
4. **Verify gates** (see §4 below). If a gate fails, debug or escalate per §5.
5. **Commit** with the conventions in §6.
6. **Update state file**, then move to the next commit.

Do not skip ahead. Each commit depends on prior commits being green.

## 3. Delegation strategy

### 3.1 What you do directly (no agent)

- Reading state, planning, sequencing
- Running the four gates after each commit
- Creating git commits (you have the conventions context; agents don't)
- Updating the progress file
- Deciding when to escalate

### 3.2 What you delegate

| Work type | Agent | Notes |
|---|---|---|
| Read-only codebase search (find symbol, file by pattern) | `Explore` agent | Cheap; use liberally; no worktree needed |
| Multi-step OCaml code changes | `general-purpose` agent | Brief on file paths, expected output, gate requirements |
| Multi-step Lean code changes | `general-purpose` agent (NOT lean4 prove agents — those are for proofs, not infra) | Same |
| Lean proof skeleton in Phase 6 | `lean4:draft` then `lean4:prove` if proofs are attempted | Phase 6 is doc-only; proofs are optional |
| OCaml emitter sanity audit (Phase 2 sub-commits) | `general-purpose` | Verify hint matches interpreter state |

**Brief every agent with**: the file paths it can touch, the exact JSON / Lean shape expected (cite the plan), the gates it must keep green, the commit boundary, and where to find the conventions (`/Users/karthik/aeneas/CLAUDE.md`). Agents have no prior context — write the prompt as if to a smart colleague who just walked in.

### 3.3 Parallelism with worktree isolation

When you dispatch multiple agents in one message, every agent that **writes** to the repo must run in an isolated git worktree. Pass `isolation: "worktree"` to the `Agent` tool. The harness creates a temporary worktree on a fresh branch; the agent makes its changes there; on completion the harness returns the worktree path and branch name. The original working tree at `/Users/karthik/aeneas` stays untouched until you merge.

Read-only agents (the `Explore` subagent, or any agent whose prompt is "find X, report back, write nothing") do **not** need worktree isolation — they don't mutate state and there's nothing to conflict on. Save the worktree overhead for write work.

### 3.4 When to parallelize vs. serialize

Independence is about **file touch sets**, not logical independence. Two agents can be "logically independent" tasks (e.g. emit two different hint fields) but if they both edit `src/cert/CertEvent.ml`, they will conflict on merge. Map every parallel batch before dispatching.

| Plan commits | File touch sets | Parallelize? |
|---|---|---|
| #1 (Lean inductives) | `Raw/CertEvent.lean` | n/a — single commit |
| #2 (Lean parser) | `Json/Parser.lean` | n/a — single commit, depends on #1 |
| #3 (OCaml fmt version + empty types) | `src/cert/CertEvent.ml/.mli`, `src/cert/CertJson.ml` | n/a — single commit |
| #4–#11 (OCaml emit hints) | All touch `CertEvent.ml`, `CertJson.ml`, plus 1–2 `src/interp/*.ml` files each | **No.** Heavy shared-file overlap on `CertEvent.ml` + `CertJson.ml`. Run sequentially. |
| #13–#17 (Lean strict paths) | All touch `LLBCSharp/Step.lean` and `Typecheck/Stmts.lean` | **No.** Same overlap problem. Run sequentially. |
| #12 (OCaml drop redundant EvEndBorrow) | `src/interp/InterpJoin.ml`, `src/interp/InterpStatements.ml` | n/a — single commit |
| #18–#19 (`AbsRegistry` + strict join) | `State.lean`, `Step.lean`, `Stmts.lean` | **No.** Shared files. |
| #20–#23 (fallback retirement) | One Lean file each | **No.** Same files repeatedly. |
| #24 (docs + theorem stub) | `documentation/*.md`, new `AeneasCheck/Theorems/*.lean` | **Yes** — touches files no other commit does. Can run in parallel with anything in Phases 4–5. |
| Read-only audits (grep for M9.5, list affected fixtures, etc.) | None | **Yes, always.** Use `Explore` without isolation. |

The honest answer: this plan has very little real parallelism. Most of the work serializes on `CertEvent.ml`/`CertJson.ml` (OCaml) and `Step.lean`/`Stmts.lean` (Lean). The benefit of worktree isolation here is **not** speed — it's giving each subagent a clean slate so an agent that mid-task leaves the tree in a half-edited state can be discarded without polluting your working copy.

### 3.5 Worktree dispatch protocol

When you spawn an isolated agent:

```
Agent({
  description: "...",
  subagent_type: "general-purpose",
  isolation: "worktree",
  prompt: """
    You are working in an ISOLATED GIT WORKTREE. The path is your CWD.
    The branch is fresh; do not switch branches.
    Make commits on this branch following the conventions in
    /Users/karthik/aeneas/CLAUDE.md (no Co-Authored-By, gmake build,
    HEREDOC commit messages, etc.).
    Use commit title prefix: <ORCHESTRATOR WILL TELL YOU, e.g. "M9.6d">.
    When done, leave the branch in a clean state (no uncommitted changes,
    no untracked files outside what your commits added).
    Report: list of commits made (hash + title), files touched, any
    surprises or deviations from your brief.
    ...rest of the task brief...
  """
})
```

On return, the harness gives you the worktree path and branch. Merge as in §3.6.

### 3.6 Merge-back protocol

After each isolated agent completes:

1. **Inspect the agent's branch** before merging: `cd <worktree-path> && git log --oneline main..HEAD` and `git diff main..HEAD --stat`. Verify the commits match the brief.
2. **Run the relevant gates against the worktree** (cheaper to catch a bad commit before it touches main):
   ```bash
   cd <worktree-path>
   bash scripts/check-vertical-slice.sh   # or whatever gates apply
   ```
3. **Merge into main** from `/Users/karthik/aeneas`:
   ```bash
   git -C /Users/karthik/aeneas merge --ff-only <agent-branch>
   ```
   Fast-forward only — if the merge would require a real merge commit, the agent's branch has diverged from your main and you need to investigate.
4. **If two parallel agents both produced commits**, merge them one at a time. The second merge may conflict on shared files; if so, the parallelism was a mistake (revisit §3.4) — abandon the second branch, redo the work sequentially in the main tree.
5. **Re-run the gates on main** after the merge. If a gate fails post-merge but passed in the worktree, you've hit a merge interaction; debug or revert.
6. **Clean up** the worktree branch only after you've confirmed main is good: the harness auto-cleans when no commits were made, but commit-producing worktrees leave the branch around. `git branch -D <agent-branch>` once merged.

If a worktree agent **fails or produces unusable work**: discard the worktree (do nothing — the branch stays orphaned but harmless), re-brief, re-dispatch. Never try to "rescue" a half-done worktree by editing it from outside the agent that owns it.

### 3.7 What you do in the main working tree (no isolation)

You operate in the main working tree at `/Users/karthik/aeneas`. You don't need a worktree because:
- You're the merge point — every agent's work funnels into your tree
- You run the authoritative gates (the gates in a worktree can disagree subtly due to `lake build` cache state — main is the source of truth)
- You author the final commits when no agent was involved (small Lean tweaks, docs, progress-file updates)

For sequential commits (which is most of this plan), don't bother with worktrees. The complexity isn't worth it for solo-author commits.

For parallel batches (commits with **disjoint** file touch sets — primarily #24 in parallel with Phase 4): worktree isolation is mandatory.

### 3.8 What you never delegate

- Final gate verification (you run the four gates yourself before committing)
- Commit message authoring (agents don't know the project's commit format) — unless the agent is operating in a worktree and you've given it the exact title prefix and conventions
- Decisions about whether to escalate

## 4. Gate protocol

After every commit (or at the end of every subagent dispatch that wrote code), run the gates. The level depends on the change:

| Change scope | Required gates |
|---|---|
| Lean-only, no schema change | G2, G3 |
| Lean schema change (CertEvent.lean) | G1, G2, G3, G4 |
| OCaml emitter change | G1 (which exercises the OCaml side), G4 |
| Cert regen | All four |
| Docs only | None (but still run G2 as a smoke check) |

If a gate that was green before a commit is now red, that commit caused the regression. Either fix it (delegate to a debug agent) or revert and rework. **Never commit with a regression.**

Commands:

```bash
# G1
bash scripts/check-vertical-slice.sh

# G2
(cd aeneas-lean-checker && for t in tests/Direct/*.lean; do lake env lean --run "$t"; done)

# G3
(cd aeneas-lean-checker && lake build GeneratedTests)

# G4 (sweep)
for f in paper iterators hashmap reborrows incr_cert loops loops-nested joins; do
  out=$(./aeneas-lean-checker/.lake/build/bin/aeneas-check /dev/null tests/llbc/$f.cert.json --out /tmp/$f.lean 2>&1 | grep '✗')
  [[ -n "$out" ]] && echo "FAIL $f: $out"
done
```

**OCaml builds**: `gmake build` (not `make` — BSD make is too old).
**Lean checker build**: `cd aeneas-lean-checker && lake build aeneas-check`.

## 5. Blocker policy — when to stop

You stop and ask the user only when one of these occurs. Otherwise, keep going.

### 5.1 Hard blockers (stop immediately, write to progress file's "Blockers" section)

1. **Baseline gates red** before you start any work.
2. **Charon version mismatch**: Phase 2/5 requires `aeneas -emit-cert` regen which depends on a specific Charon binary at `/Users/karthik/charon/charon/target/release/charon`. If `charon-pin` is out of date or the binary is missing, stop. The user must rebuild Charon.
3. **OCaml emitter changes require touching files outside `/Users/karthik/aeneas/src/`**. If a hint requires upstream Charon changes, stop — that's a separate upstream PR.
4. **A hint's design proves insufficient mid-implementation** (Phase 6 prototype proofs reveal a gap). Per plan §6.4 and §7.4 risk 2, you'd need to bump to `fmt_version=3` before Phase 2 ships. Stop and surface the gap.
5. **Sweep regressions you cannot fix**: if a commit drops fixture-pass count and the cause isn't an obvious bug in your code, stop. (Per the conversation context, the baseline as of writing is 89/89 fixtures passing. Treat any regression below that as a blocker unless the cause is "schema changed, fixture needs regen" — in which case regen and continue.)
6. **Conflicting workflow rules**: if the plan asks for an action that CLAUDE.md prohibits (or vice versa), stop and surface the conflict.
7. **You need a destructive action** that the user didn't pre-authorize: `git reset --hard`, `git push --force`, deleting files outside the new ones you wrote, dropping local state, etc. Stop.

### 5.2 Soft blockers (record and continue around)

These are not stop-the-world; work around and note in the progress file:

- A single fixture is non-determ flaky — re-run, then if still flaky, skip that fixture in the sweep subset and continue.
- A subagent returned partial work — fix or re-dispatch the missing piece, don't escalate.
- A new pragmatic shortcut surfaces during implementation (M9.5*ab*?) — record it, route to the equivalent hint, continue.
- The plan's LOC estimate is wrong by 2x — that's normal, keep going.

### 5.3 What's NOT a blocker

- Long subagent runs. Wait them out — use `run_in_background: true` for OCaml builds that take >2 min, then come back when notified.
- Build cache misses. `lake build` is slow but deterministic.
- Reviewing your own work. You don't have a reviewer in the loop; you're it. Sanity-check by reading the diff before commit (`git diff --cached`), then ship.

## 6. Commit conventions

Per `/Users/karthik/aeneas/CLAUDE.md` and the established history (see `git log --oneline -20`):

- **No `Co-Authored-By: Claude` trailer.** The user has been explicit.
- **No `--no-verify`.** Pre-commit hooks must pass.
- **Title format**: `<milestone-tag> <area>: <verb-phrase>`. Examples from recent history:
  - `M9.5w Lean: classify &mut (*x). (place with any Deref) as reborrow`
  - `M9.5v OCaml: drive pop_frame in CertGen so function-exit cleanup emits EvEndBorrow events`
- **Tag for this work**: use `M9.6` as the milestone prefix (since the cert-format redesign is a new milestone after M9.5x/y/z/aa). Sub-tag with letters: `M9.6a`, `M9.6b`, …, in plan §7.1 commit order. Examples:
  - `M9.6a Lean: add MutBorrowKind/JoinRule inductives and optional Event fields (Option C schema)`
  - `M9.6b Lean: parse Option C hint fields with back-compat defaults`
  - `M9.6c OCaml: bump cert_fmt_version 1→2; emit empty hint fields`
  - `M9.6d OCaml: emit EvMutBorrow.kindHint (M9.5w + M9.5aa source); regen tests/llbc fixtures`
  - etc.
- **Cert regen**: per CLAUDE.md, only commit regenerated `tests/llbc/*.cert.json` when the cert schema actually changed. Phase 2 commits trigger regen; Lean-only commits (Phase 1, 3, 4, 6) don't.
- **Commit messages stay short**. Title + (optional) one-paragraph body. No PR-description-style summaries.

Use `HEREDOC` for any multi-line message:

```bash
git commit -m "$(cat <<'EOF'
M9.6a Lean: add MutBorrowKind/JoinRule inductives (Option C schema)
EOF
)"
```

## 7. Sanity-check sequence (do at boundaries)

After every major phase boundary (plan §7.1 commits 3, 11, 12, 17, 22, 24), run an extended sweep:

```bash
# Full sweep — not just the representative subset
ok=0; fail=0
for src in tests/src/*.rs; do
  base=$(basename "$src" .rs)
  cert="tests/llbc/${base}.cert.json"
  [[ -f "$cert" ]] || continue
  out=$(./aeneas-lean-checker/.lake/build/bin/aeneas-check /dev/null "$cert" --out /tmp/$base.lean 2>&1 | grep '✗')
  [[ -z "$out" ]] && ok=$((ok+1)) || { fail=$((fail+1)); echo "FAIL $base: $out"; }
done
echo "OK: $ok / FAIL: $fail"
```

Record the count in your progress file. **Baseline as of plan creation: 89/0**. Any regression is a blocker per §5.1.5.

## 8. Resumption protocol

If the session ends mid-way (user closes the terminal, runs out of context, etc.), the next instance of you resumes by:

1. Reading `/Users/karthik/aeneas/.option-c-progress.md` to find the last completed commit.
2. Reading the plan to find the next commit.
3. Running the four gates to confirm the green baseline holds.
4. Picking up from the next commit.

The progress file is your only memory. Keep it complete.

## 9. Done conditions

You are done when:

1. All 24 commits in plan §7.1 have landed.
2. All four gates are green on the tip.
3. Full sweep is at 89/0 (or better — Phase 5 regen may unlock more fixtures).
4. The Lean side has no remaining `M9.5x/y/z/aa/w` shortcut code (verify with `grep -rn 'M9.5[wxyzaa]' aeneas-lean-checker/AeneasCheck/`; should return only docstring history, not active branches).
5. The progress file's "Completed commits" list is full and no blockers are pending.
6. `documentation/cert-format-and-soundness.md` is updated to reflect the new shortcut-free state (§3.2 of that doc).

Report completion to the user with a summary: commits landed, fixture count, LOC delta, anything notable in the "Notes" section of the progress file.

## 10. What you tell the user when you stop

Whether at a blocker or at completion, your message to the user must include:

- **Status**: `BLOCKED on <reason>` or `COMPLETE`.
- **Where things stand**: last completed commit number/hash, current branch (should be `main` per the convention).
- **Gate state**: which of the four gates are green; which are red and why.
- **Fixture count**: from the last sweep.
- **What you need from the user**, if blocked. Be specific.
- **Where to find the progress file** (path).

Be concise. The user is looking for "where are we?" not a recap of everything you did.

---

# Self-direction reminders

- Don't ask the user for permission for things you can do yourself. The plan is approved; the commits are spec'd; execute.
- Don't redesign the plan mid-flight. If you think the plan is wrong, finish the current commit, then escalate per §5 with a specific proposal.
- Don't bikeshed JSON key names, file names, or commit titles. Use what the plan says.
- Don't write speculative tests. The plan's gates are the test surface; add new tests only when the plan explicitly says so (Phase 6 stub).
- Don't commit untracked files outside the scope of the current commit. `git add <specific-file>`, never `git add .` or `-A`.
- Don't push to remote. The user pushes when they're ready.
- Don't run `lake clean` or any other "throw away build cache to make it work" command. If a build is wrong, the source is wrong; fix the source.
- Run multi-minute work in the background (`run_in_background: true`) and continue with other work; don't poll, you'll be notified.

Start by completing the boot sequence (§0). Then create the progress file (§1) and begin commit #1.
