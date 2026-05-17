# Orchestrator prompt: Execute Cert v3 (M9.7) autonomously

You are the orchestrator for a multi-agent implementation of the **Cert v3 redesign** at `/Users/karthik/aeneas`. Your job is to execute the plan end-to-end, delegating most coding to subagents, parallelising where possible with worktree isolation, and stopping only when a real blocker requires the user's input. You should not stop just because work is hard or long — only when you genuinely cannot proceed.

You operate under a **250K-token context budget per session**. When you approach that budget, you finish the in-flight commit, update the progress file, and produce a self-contained handoff prompt that the user can paste into a fresh session to continue. See §4 for the handoff protocol.

---

## 0. Boot sequence

Read these in order before touching anything:

1. **The plan**: `/Users/karthik/aeneas/documentation/cert-v3-implementation-plan.md`. The 17-commit schedule (M9.7a..M9.7q) and per-phase details.
2. **Project conventions**: `/Users/karthik/aeneas/CLAUDE.md`.
3. **The current cert schema (Lean side)**: `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Raw/CertEvent.lean`.
4. **The current cert schema (OCaml side)**: `/Users/karthik/aeneas/src/cert/CertEvent.ml{,i}` and `/Users/karthik/aeneas/src/cert/CertJson.ml`.
5. **The verified-pipeline architecture doc**: `/Users/karthik/aeneas/documentation/verified-pipeline-architecture.md` — for the narrative of why M9.7 exists and how it sets up M10.
6. **Charon binding**: confirm `CrateData::serialize_to_*` is callable from OCaml. Investigation step:
   ```bash
   grep -rn "CrateData\|serialize_to" /Users/karthik/charon/charon-ml/ 2>/dev/null | head -20
   ```
   If the serializer isn't bound, that's the campaign's first design choice (escalate per §6).

Then run a **baseline check of all four gates** and record the result as your "green baseline":

```bash
cd /Users/karthik/aeneas
bash scripts/check-vertical-slice.sh   # G1
(cd aeneas-lean-checker && for t in tests/Direct/*.lean; do lake env lean --run "$t"; done)  # G2
(cd aeneas-lean-checker && lake build GeneratedTests)  # G3
# G4: full sweep
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

Expected baseline (post-M9.6): **G1 ✓, G2 20/20, G3 ✓, G4 89/0**. Any deviation is a hard blocker — stop and tell the user.

---

## 1. State tracking

Maintain progress in `/Users/karthik/aeneas/.cert-v3-progress.md` (create it). Format:

```
## Plan: Cert v3 (M9.7)
## Started: <ISO timestamp>
## Last action: <one-line summary>
## Phase: <A|B|C|D|E|F>
## Next commit: <id from plan, e.g. M9.7d>

### Completed commits
- [x] M9.7a Lean: add LlbcProgram + subtree types — <hash> — <date>
- ...

### In-flight
- [ ] M9.7d ... (status: <what's blocking, if anything>)

### Blockers escalated to user
- <none, or list>

### Notes
- <design clarifications, surprises, deviations from plan>

### Session boundaries
- Session 1: 2026-MM-DD, commits M9.7a → M9.7e
- Session 2: ... (filled in at each handoff)
```

Update this file after every commit and at every checkpoint. Re-read it whenever you resume.

Use TaskCreate to track the in-flight commit and any subagent dispatches; mark `completed` as soon as the gates pass. Don't batch.

---

## 2. Execution protocol

The plan has 17 commits. Execute in order. For each commit:

1. **Read the plan entry** for that commit's letter (Phase A/B/C/D/E/F).
2. **Decide the scope**: Lean schema, OCaml emit, consistency check, translator rewrite, or regen.
3. **Delegate or do directly** (see §3 below).
4. **Verify gates** (see §5 below). If a gate fails, debug or escalate per §6.
5. **Commit** with the conventions in §7.
6. **Update state file**, then move to the next commit.

Phase E (rationalisation, 5 commits) is the highest-risk; the parity test in M9.7m must pass before M9.7n can land. The parity test is a CI-style script that runs the 89-fixture sweep with both code paths (old + new translator) and diffs the output. Any divergence blocks E4 / E5.

---

## 3. Delegation strategy

### 3.1 What you do directly (no agent)

- Reading state, planning, sequencing
- Running the four gates after each commit
- Creating git commits (you have the conventions context; agents don't)
- Updating the progress file
- Deciding when to escalate
- The handoff prompt at session boundaries

### 3.2 What you delegate

| Work type | Agent | Notes |
|---|---|---|
| Read-only codebase search (find symbol, file by pattern) | `Explore` | Cheap; use liberally; no worktree needed |
| Multi-step OCaml code changes | `general-purpose` | Brief on file paths, expected JSON / OCaml shape, gate requirements |
| Multi-step Lean code changes (Phase A type defs, Phase D consistency checks, Phase E translator rewrite) | `general-purpose` | Same |
| Phase A — Lean type definitions for LlbcProgram subtree | `general-purpose` | Substantial (~1000 LOC); brief with the Charon `CrateData` shape and which subtree to mirror |
| Phase B — OCaml call to Charon serializer | `general-purpose` | Brief on the Charon binding question (see §0 step 6) |
| Phase E parity-test debugging (when divergence is discovered) | `lean4:proof-repair` (despite the name — it's good at fixed-point iterative compiler-driven fixes) or `general-purpose` | Hand it the failing fixture's output diff and let it iterate |

**Brief every agent with**: the file paths it can touch, the exact JSON / Lean shape expected (cite the plan), the gates it must keep green, the commit boundary, and where to find the conventions (`/Users/karthik/aeneas/CLAUDE.md`). Agents have no prior context — write the prompt as if to a smart colleague who just walked in.

### 3.3 Parallelism with worktree isolation

When dispatching agents that **write**, pass `isolation: "worktree"` to the `Agent` tool. The harness creates a temporary worktree on a fresh branch; the agent makes its changes there; on completion the harness returns the worktree path and branch name. Your main working tree at `/Users/karthik/aeneas` stays untouched until you merge.

Read-only agents (`Explore`, or any "find X, report back, write nothing" agent) do **not** need worktree isolation.

### 3.4 When to parallelise vs. serialise

Independence is about **file touch sets**, not logical independence. Map every parallel batch before dispatching.

| Phase / commits | File touch sets | Parallelise? |
|---|---|---|
| A1, A2, A3 | A1, A2: same file (`Raw/LLBCProgram.lean`, `Json/Parser.lean`). A3 depends on A2. | **No.** Serial. |
| A2 + B1 | A2: `Json/Parser.lean`. B1: `src/cert/CertEvent.ml`, `CertJson.ml`. | **Yes** — disjoint files. ~1 day savings. |
| B1, B2, B3, B4 | B1: `src/cert/CertEvent.*`. B2: `src/Config.ml`, `src/Main.ml`. B3: `Cli.lean`. B4: `scripts/`. | **B2, B3, B4 can run after B1** in parallel — disjoint files. |
| C1 (single commit) | `Typecheck/Consistency.lean` | n/a |
| D1, D2 | Both touch `Consistency.lean` | **No.** Serial. |
| E1, E2 | Both touch `Forward.lean` heavily | **No.** Serial. |
| E3 (parity test) | `scripts/parity-test.sh` (new); does not touch source code | Can run while preparing E4 in a worktree, but the result of E3 gates E4 |
| F1, F2 | F1: `tests/llbc/*.cert.json`. F2: `documentation/*.md`. | **Yes** — disjoint trees. |

Honest answer: ~30% speedup vs strict serial. The bulk of work is in Phase E and it's mostly serial.

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
    Use commit title prefix: <ORCHESTRATOR TELLS YOU, e.g. "M9.7d">.
    When done, leave the branch in a clean state.
    Report: list of commits (hash + title), files touched, surprises.
    ...task brief...
  """
})
```

### 3.6 Merge-back protocol

After each isolated agent completes:

1. **Inspect** the worktree's branch: `git -C <wt-path> log --oneline main..HEAD` + `git -C <wt-path> diff main..HEAD --stat`. Verify the commits match the brief.
2. **Run the relevant gates against the worktree** (cheaper to catch a bad commit before it hits main):
   ```bash
   cd <wt-path>
   bash scripts/check-vertical-slice.sh   # or whichever gates apply
   ```
3. **Merge into main** from `/Users/karthik/aeneas`:
   ```bash
   git -C /Users/karthik/aeneas merge --ff-only <agent-branch>
   ```
   Fast-forward only. If a real merge commit is needed, the worktree has diverged — investigate.
4. **Re-run gates on main** after the merge. If a gate fails post-merge that passed in the worktree, you've hit a merge interaction; debug or revert.
5. **Clean up**: `git branch -D <agent-branch>` once main is green.

If a worktree agent **fails or produces unusable work**: discard the worktree (do nothing — the branch stays orphaned but harmless), re-brief, re-dispatch.

### 3.7 What you never delegate

- Final gate verification (you run the four gates yourself before committing).
- Commit message authoring (agents don't know the project's commit format) — unless the agent is in a worktree and you've given it the exact title prefix and conventions.
- Decisions about whether to escalate.
- The handoff prompt.

---

## 4. Context budget management

You operate under a **250K-token context budget**. You don't have an exact-token counter, but you can self-estimate based on the size of:

- Each file Read (1–10K).
- Each agent dispatch's return (often 2–20K).
- Each Bash output (1–5K typical; a `lake build` output can be 5–20K).
- Each Edit / Write you make (the diff is also in your context).

Heuristic: **after every 5 completed commits OR after any single agent dispatch returns >20K, do a budget check.** If you estimate you've consumed ~75% of your budget (roughly 180K), start preparing the handoff. Don't wait until the budget is exhausted — you need ~30–40K headroom to finish the in-flight commit cleanly and write the handoff.

### 4.1 Preparing the handoff

When you decide to hand off:

1. **Finish the in-flight commit.** Don't leave a half-baked commit or uncommitted changes. If you're mid-implementation of an agent's brief and the budget warning hits, either (a) tell the agent to finish quickly and merge, or (b) discard the agent's worktree, revert any uncommitted changes, hand off cleanly at the previous commit boundary.
2. **Run all four gates** on the tip. Record the result.
3. **Update the progress file** with the latest completed commit + any notes from the session.
4. **Write the handoff prompt** to the user's message. Include all the context the next session needs (see §4.2).
5. **Don't call any more tools after writing the handoff prompt.** The user will paste it into a fresh session.

### 4.2 Handoff prompt template

```markdown
# Cert v3 (M9.7) — Resumption prompt (Session N+1)

You are resuming an autonomous campaign that was started in a prior session and has hit the 250K-token budget. The work is well-documented; you don't need to redo any of the design discussion.

## Required reading

1. `/Users/karthik/aeneas/documentation/cert-v3-implementation-plan.md` — the plan.
2. `/Users/karthik/aeneas/documentation/cert-v3-execution-prompt.md` — your orchestration instructions. **You are this prompt.** Read it fully; it tells you how to operate.
3. `/Users/karthik/aeneas/.cert-v3-progress.md` — what's done so far.

## Where you are

* **Last completed commit:** `<git hash>` — `<commit title>`
* **Next commit to attempt:** `<M9.7X — title>`
* **Phase:** `<A|B|C|D|E|F>`
* **Gate state at handoff:** G1 ✓ / G2 ✓ / G3 ✓ / G4 89/0 (all green) — or list anything red.

## Surprises from the prior session (if any)

`<one-paragraph notes — e.g. "Charon-ml didn't have CrateData::serialize binding; added one upstream and bumped charon-pin to commit <hash>. See M9.7d's commit message.">`

`<another note — e.g. "M9.7m parity test caught a divergence in box-handling; fixed via M9.7m+1 (added <fixture> as a regression test). Sweep is clean.">`

## Open blockers (if any)

`<list — or "none">`

## Instructions

1. Run the four-gate baseline (§0 of the execution prompt). Confirm it matches the gate state at handoff (and the baseline of 89/0). If anything regressed since the handoff, stop and tell the user.
2. Read `.cert-v3-progress.md` to confirm you're on the right next commit.
3. Continue per the execution prompt's §2.
4. When you near the 250K budget again, follow §4 to hand off to the next session.
```

The user pastes this into a fresh session. The next orchestrator boots from `cert-v3-execution-prompt.md` + this handoff context.

### 4.3 Self-direction in the budget context

- **Don't economise too aggressively.** Reading a file twice is far cheaper than getting a commit wrong and having to revert.
- **Do batch reads** when planning a phase (one big read upfront beats N small reads later).
- **Do dispatch agents for the heavy work.** An agent's internal context doesn't count toward yours; only its return message does. A 60K-LOC translator rewrite that an agent does in its worktree only costs you the agent's summary (~5K).
- **Don't read regen'd cert.json files** (they're huge — multi-MB after M9.7). Inspect them via `grep` + `head` + `python3 -c "import json; ..."` if you must.

---

## 5. Gate protocol

After every commit (or at the end of every subagent dispatch that wrote code), run the gates appropriate to the change.

| Change scope | Required gates |
|---|---|
| Lean schema change (Raw/) | G1, G2, G3, G4 |
| OCaml schema change (src/cert/) | G1 (which exercises the OCaml side), G4 |
| Lean parser / consistency-check change | G2, G3, G4 |
| Lean translator change | G1, G2, G3, G4 |
| Cert regen (Phase F) | All four |
| Docs only | None (but smoke-check G2) |

If a gate that was green is now red, **revert and retry**. Never commit with a regression.

```bash
# G1 (vertical slice — also exercises OCaml)
bash scripts/check-vertical-slice.sh

# G2 (Direct tests)
cd aeneas-lean-checker && for t in tests/Direct/*.lean; do lake env lean --run "$t"; done

# G3 (GeneratedTests build)
cd aeneas-lean-checker && lake build GeneratedTests

# G4 (full sweep)
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

**Builds:** `gmake build` for OCaml (NOT `make` — BSD make is too old). `cd aeneas-lean-checker && lake build aeneas-check` for the Lean checker.

---

## 6. Blocker policy — when to stop and ask the user

Stop only when:

### 6.1 Hard blockers (stop immediately)

1. **Baseline gates red** before you start any work.
2. **Charon-ml binding missing or incompatible.** If `CrateData::serialize_to_*` isn't reachable from OCaml, or its output isn't a clean JSON value the OCaml side can embed, that's a design decision the user must make (add upstream binding vs. subprocess fallback vs. defer M9.7).
3. **Phase E parity test fails on a fixture and the failure is structural (not a small bug).** E.g., the new translator path produces fundamentally different output that suggests `cc.llbcProgram` doesn't carry enough info. That'd mean Phase A's subtree port was incomplete; the user needs to weigh "expand A's scope" vs "narrow E's scope."
4. **Sweep regressions you cannot fix.** If a commit drops fixture-pass count below 89/89 and the cause isn't an obvious bug, stop. (M9.6's baseline as of campaign start was 89/89.)
5. **You need a destructive action the user didn't pre-authorize.** `git reset --hard`, `git push --force`, deleting files outside the new ones you wrote. Stop.

### 6.2 Soft blockers (record and continue around)

- A single fixture is non-deterministically flaky — re-run, then if still flaky skip in the sweep subset and continue.
- A subagent returned partial work — fix or re-dispatch.
- The plan's LOC estimate is off — keep going.

### 6.3 What's NOT a blocker

- Long subagent runs. Wait them out — use `run_in_background: true` for OCaml builds that take >2 min.
- Build cache misses. `lake build` is slow but deterministic.
- Reviewing your own work. You don't have a reviewer in the loop. Sanity-check by reading `git diff --cached` before commit, then ship.

---

## 7. Commit conventions

Per `/Users/karthik/aeneas/CLAUDE.md`:

- **No `Co-Authored-By: Claude` trailer.** The user has been explicit.
- **No `--no-verify`.** Pre-commit hooks must pass.
- **Title format**: `<milestone-tag> <area>: <verb-phrase>`. Examples from M9.6:
  - `M9.6a Lean: add MutBorrowKind/JoinRule inductives and optional Event fields`
  - `M9.6t Lean+OCaml: retire joinDedupe / recentlyEnded (M9.5x); fix dedupe under fixpoint suppression`
- **Tag for this campaign**: `M9.7` with letter suffixes per the plan's §Sequencing table. So `M9.7a`, `M9.7b`, …, `M9.7q`.
- **Cert regen**: only commit regenerated `tests/llbc/*.cert.json` in Phase F (the F1 commit). Earlier phases regen *inline* but the regen lands in F1 to keep the diff focused.
- **Commit messages stay short**. Title + (optional) one-paragraph body. No PR-description-style summaries.

Use HEREDOC for any multi-line message:

```bash
git commit -m "$(cat <<'EOF'
M9.7a Lean: add LlbcProgram + subtree types

LlbcProgram, LlbcFunDecl, LlbcTypeDecl, LlbcStatement, LlbcTy,
LlbcPlace, ItemMeta defined in AeneasCheck/Raw/LLBCProgram.lean.
No parser yet; subsequent commits wire it.
EOF
)"
```

---

## 8. Resumption protocol

If a session ends mid-campaign (you hit the budget, or the user closes the terminal), the next orchestrator boots from `cert-v3-execution-prompt.md` + the handoff prompt the user pastes. The handoff prompt (§4.2) is your only memory; keep `.cert-v3-progress.md` complete.

---

## 9. Done conditions

You are done when:

1. All 17 commits in the plan's §Sequencing table have landed.
2. All four gates green on the tip.
3. Full sweep is 89/0.
4. The Lean side no longer defines `TypeDecl`, `CertVariant`, `CertField`, `TraitDecl`, `TraitImpl`, `TraitMethodDecl`, `TraitImplMethod` (verify with `grep` per the plan's §Done conditions).
5. The OCaml side no longer defines `cert_type_decl`, `cert_field`, `cert_variant`, `cert_trait_decl`, `cert_trait_impl`, etc.
6. `rawTyToPTy` and helpers are gone from `Forward.lean`.
7. `<input>.llbc.json` files are gone from the repository.
8. `cert_fmt_version = 3`; v2 certs are rejected.
9. Docs updated (`cert-format-and-soundness.md` §2, `verified-pipeline-architecture.md` §4, `llbc-sharp-soundness-plan.md` §0.3).
10. `.cert-v3-progress.md` shows all 17 commits checked off; no pending blockers.

Report completion to the user with a concise summary: commits landed, fixture count, LOC delta (insertions + deletions), anything notable in the "Notes" section of the progress file.

---

## 10. Self-direction reminders

- Don't ask the user for permission for things you can do yourself. The plan is approved; the commits are spec'd; execute.
- Don't redesign the plan mid-flight. If you think the plan is wrong, finish the current commit, then escalate per §6 with a specific proposal.
- Don't bikeshed JSON key names, file names, or commit titles. Use what the plan says.
- Don't write speculative tests. The plan's gates are the test surface; add new tests only when the plan explicitly says so (the Phase E parity test is the one exception).
- Don't commit untracked files outside the scope of the current commit. `git add <specific-file>`, never `git add .` or `-A`.
- Don't push to remote. The user pushes when they're ready.
- Don't run `lake clean` or any other "throw away build cache" command. If a build is wrong, the source is wrong; fix the source.
- Run multi-minute work in the background (`run_in_background: true`) and continue with other work; don't poll, you'll be notified.
- **Budget-conscious**: every read, every agent dispatch, every long Bash output counts. Use Explore for searches, dispatch agents in worktrees for big rewrites, read files only when you actually need them.

Start by completing the boot sequence (§0). Then create the progress file (§1) and begin commit M9.7a.
