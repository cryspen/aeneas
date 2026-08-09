# Aeneas fuzzing campaign — final triage report

Fuzzer for the Aeneas Rust→Lean translation, run against **both** the cryspen
fork (`dump-pure-ir-minimal`, charon v0.1.196) and upstream AeneasVerif/aeneas
(`main` 3a8586fa, charon v0.1.225). Architecture: `fuzz/DESIGN.md`. Per-finding
repros: `fuzz/findings/<slug>/`. Machine-readable DB: `fuzz/findings/db.json`.

## New bugs found by this campaign

| ID | Bug | Oracle | Targets | Severity | Disposition |
|----|-----|--------|---------|----------|-------------|
| **N1** | two `assert!` of the same bool → `[Error] There should be no bottoms in the value` (`InterpExpressions.ml:55`) | crash | fork + upstream | MEDIUM | **filed `cryspen/aeneas#28`** |
| N3 | closure reading a captured `&mut` → `SymbolicToPureValues.ml:366` | crash | fork toolchain only | MEDIUM | **filed `cryspen/aeneas#40`** (likely version-delta / rebase) |

**N1 is the campaign's one genuinely new, cleanly-filable bug** — it is filed.
N3 crashes only on the fork *toolchain* (fork aeneas + charon 0.1.196); the
crash-site function is byte-identical to upstream and upstream `main` translated
the input fine (during campaign testing), so the differentiator is an
aeneas-or-charon *version* delta, not fork-modified code — most likely already
fixed upstream / resolved by rebasing. Filed as **cryspen/aeneas#40** with that
caveat called out in the issue; the disentanglement below decides fix-vs-rebase.

## Oracle validation — known soundness bug independently reproduced

| ID | Bug | Oracle | Provenance |
|----|-----|--------|------------|
| **N5** | `iN::MIN % -1` modeled as `0` but **panics** in Rust — unsound arithmetic model (interpreter + Lean/F*/Coq) | semantic differential (native vs Lean) | **prior manual audit; already fixed in `cryspen/aeneas` PR #21 (2026-07-22, predates this campaign)** |

N5 is **not** a campaign discovery — it was found by manual auditing and fixed
in PR #21 (branch `fix/rem-min-overflow`) before the fuzzer ran. Its value here
is as an **oracle-validation datapoint**: on a targeted `MIN % -1` test the
Phase-2 semantic differential correctly flags native PANIC (`integerOverflow`)
vs Lean `ok 0` → MISMATCH (verified firsthand), demonstrating the differential
catches this soundness class — the analogue of F4/F6 rediscovery validating the
crash oracle. It is a HIGH-severity soundness bug affecting both targets and all
three backends (fix parent is upstream `004e11fe`, so it predates the fork).

## Rediscovered known / upstream bugs (deduped, not filed)

| ID | Bug | Targets | Duplicate of |
|----|-----|---------|--------------|
| N2 | 2 sequential loops, first early-returns → "Could not match the contexts" (`InterpJoin.ml:1515/1542`) | fork + upstream | upstream **#930** (+ break variant **#1206**) |
| N4 | `match` on `char` → "Inconsistent state" / "(Failure Unexpected)" (`InterpStatements.ml:1100/1132`) | fork + upstream | upstream **#797** |
| F4 | `return` of a loop-given-back value → `PureMicroPassesLoops.ml:1818` | fork + upstream | cryspen **#22** |
| F6 | inverted `can_end` guard → `InterpAbs.ml:1671/1688` | fork + upstream | cryspen **#24** |
| — | closure returns refs via `array::from_fn` → `InterpBorrows.ml:1203` | fork only | upstream **#804** |

F4/F6 (filed earlier on cryspen `dev` as fix PRs #25/#27) still reproduce on the
current fork binary and on upstream `main`. F5 (#23) is latent (no crash
fingerprint).

## Not bugs (recorded so they dedup / don't recur)

- `InterpLoops.ml:407` "infinite loops without breaks not supported yet" — an
  intended feature-gate rejection (`-abort-on-error` promotes the craise to an
  uncaught `Failure`, which briefly looked like a crash).
- `extract/Extract.ml:2851` — a `[%warn]` (missing `Iterator::collect` model)
  that prints a `Compiler source:` marker but **exits 0** and generates Lean.
  This was a harness false positive; the oracle was fixed (crash now requires
  nonzero exit + a real backtrace/uncaught-exception, and the fingerprint
  anchors to the uncaught-exception block — commit `c30d58ec`).

## Oracle results summary

- **O1 crash / O2 wrong-reject** (both targets, ~1500+ crates across the
  campaign): 8 distinct crash sites total, all accounted for above — no
  unexplained new crash sites remain.
- **O4 semantic differential** (native vs Lean, fork): found **N5**. On the rest
  of the generated/closed corpus, native and Lean agree (MATCH), modulo
  `LEAN_INCONCLUSIVE` for range-`for` (noncomputable `Step` axioms) — the reason
  the generator uses `while`/index loops.
- **O5 stage differential** (post-s2p vs post-micro pure-IR eval, fork): **2164
  argsets AGREE, 0 DISAGREE** across `tests/src` — the ~45 micro-passes are
  semantically faithful on the reachable (~28% conclusive) subset; metamorphic
  transforms (let-split, if↔match, identity-block) also agree. No pass convicted.

## Fork-vs-upstream applicability at a glance

Every *new/rediscovered* bug except N3 reproduces on **both** targets across the
two charon versions, so none are charon-version artifacts. N3 is fork-toolchain
only. N5 predates the fork (upstream base).

## Recommended follow-ups

1. **N5**: already fixed — land cryspen/aeneas PR #21 (`fix/rem-min-overflow`);
   the fix applies upstream too. (No new action from the campaign — listed only
   because the semdiff oracle reproduces it.)
2. **N3** (filed cryspen/aeneas#40): build upstream aeneas at the fork's
   charon-0.1.196-era commit and re-test to decide fork-regression vs
   already-fixed-upstream → fix, or close as resolved-by-rebase.
3. Wire the semantic differential (`aeneas-fuzz semdiff`) into the weekly CI lane
   (it already exists behind the subcommand + `--lean-elab`/`oracle_scope`).
4. Per-pass bisection: emit one pure-IR dump per micro-pass (small OCaml change)
   so `stage-diff` can convict a single pass on any future DISAGREE.

## How to reproduce / run

See `fuzz/README.md` (build both targets via `fuzz/setup/`, run
`aeneas-fuzz run|one|minimize|semdiff`, CI via `.github/workflows/fuzz-nightly.yml`).
