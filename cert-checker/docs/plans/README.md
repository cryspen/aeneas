# Plans

Multi-session campaign plans and their boot prompts. Each plan
captures a coherent restructuring effort: design rationale, sequenced
commits, gates / done-conditions, and the boot prompt that opens a
fresh Claude Code session against it.

## Layout

- `*.md` — implementation plans (design + sequence) and progress notes.
- `prompts/` — execution prompts (paste-into-fresh-session boot
  scripts that point an agent at a specific phase of a plan).

## Active campaigns

| Plan | Status | Prompt | Notes |
|---|---|---|---|
| [`llbc-sharp-soundness-plan.md`](llbc-sharp-soundness-plan.md) | **active** (M10) | [`prompts/m10-soundness-execution-prompt.md`](prompts/m10-soundness-execution-prompt.md) | Soundness proof for the LLBC# cert pipeline. M10 agent commits to `aeneas-lean-certificate` regularly. The largest live campaign. |
| [`differential-testing-plan.md`](differential-testing-plan.md) | **active** (Phases 0+1 done; 2–5 pending) | [`prompts/differential-testing-phase4-prompt.md`](prompts/differential-testing-phase4-prompt.md) | Four-artifact differential testing rollout (R₀ source ↔ R₁ emitted Rust ↔ L₀ mainline Lean ↔ L₁ cert Lean). |
| [`differential-testing-progress.md`](differential-testing-progress.md) | **active** record | — | Session-by-session log for the differential testing campaign. Append on each session close. |

## Completed campaigns (retained for design rationale)

| Plan | Status | Notes |
|---|---|---|
| [`cert-v3-implementation-plan.md`](cert-v3-implementation-plan.md) | **done** (M9.7) | Bumped cert format v2 → v3 (embedded LLBC# program; structured types). Done-conditions audit in the deleted `.cert-v3-progress.md` (now in repo root). |
| [`option-c-implementation-plan.md`](option-c-implementation-plan.md) | **done** (M9.6) | Per-join witness payloads. Referenced from `llbc-sharp-soundness-plan.md` as historical context; kept so cross-references resolve. |

## Cross-references from elsewhere in the tree

- The top-level [`documentation/README.md`](../README.md) links here.
- Active plans are referenced by skill files in
  [`documentation/skills/`](../skills/) (notably
  `verification-campaigns`).
- `aeneas-lean-soundness/` Lean source occasionally cites
  `llbc-sharp-soundness-plan.md` §-anchors in comments.

## When to add a new plan

A new campaign warrants its own plan file when:
- It spans ≥3 sessions and ≥10 commits.
- It introduces gates / done-conditions that must hold simultaneously.
- It will be handed off between agents or sessions.

Otherwise, prefer a single PR description.

## When to retire a plan

After the campaign's done-conditions all hold:
1. Audit them (typically a `done-condition audit` section in a
   progress note).
2. Move the plan to the "Completed campaigns" section of this README.
3. Delete the corresponding execution prompt in `prompts/` (a stale
   prompt mis-directs future sessions; the implementation plan
   retains the design rationale).
4. Update cross-references in skill files / soundness comments to
   point at the implementation plan, not the deleted prompt.
