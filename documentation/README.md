# Aeneas Documentation

Aeneas translates Rust programs into pure functional programs
(primarily Lean) for formal verification.

## Core

- [Getting Started](getting-started.md) — Rust → LLBC → Lean → first proof
- [Aeneas Overview](aeneas-overview.md) — How Aeneas works, translation model, workflow
- [Certificate-based Pipeline](certificate-pipeline.md) — Cert checker architecture, soundness theorems, how to run
- [Glossary](glossary.md)

## Proof engineering

- [Proof Strategies](proof-strategies.md)
- [Tactics Reference](tactics-reference.md)
- [Tips, Tricks & Pitfalls](tips-and-tricks.md)
- [Crypto Verification](crypto-verification.md)

## Active campaigns

Multi-session restructuring plans, progress notes, and the boot
prompts that open a fresh agent session against them live in
[`plans/`](plans/). See [`plans/README.md`](plans/README.md) for the
index.

## AI agent instructions

Skill files for Claude Code and GitHub Copilot live in
[`skills/`](skills/). These are the source of truth and are
symlinked from `.claude/skills/` and `.github/instructions/`.
