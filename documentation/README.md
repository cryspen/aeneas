# Aeneas Documentation

Aeneas translates Rust programs into pure functional programs
(primarily Lean) for formal verification.

## User-facing references

- [Getting Started](getting-started.md) — Rust → LLBC → Lean → first proof
- [Aeneas Overview](aeneas-overview.md) — How Aeneas works, translation model, workflow
- [Proof Strategies](proof-strategies.md) — Step, loops, decomposition, specs
- [Tactics Reference](tactics-reference.md) — All tactics with docstrings and examples
- [Tips, Tricks & Pitfalls](tips-and-tricks.md) — Common pitfalls and how to avoid them
- [Crypto Verification](crypto-verification.md) — Verifying cryptographic code
- [Glossary](glossary.md) — Aeneas-specific terms

## Architecture / pipeline reference

- [Cert format & soundness](cert-format-and-soundness.md) — Cert v6 format, soundness statement
- [Verified pipeline architecture](verified-pipeline-architecture.md) — End-to-end pipeline overview
- [Paper / proof comparison](PaperProofComparison.md) — Crosswalk between the paper and the Lean development

## Active campaigns

Multi-session restructuring plans, progress notes, and the boot
prompts that open a fresh agent session against them live in
[`plans/`](plans/). See [`plans/README.md`](plans/README.md) for the
index.

## AI agent instructions

Skill files for Claude Code and GitHub Copilot live in
[`skills/`](skills/). These are the source of truth and are
symlinked from `.claude/skills/` and `.github/instructions/`.
