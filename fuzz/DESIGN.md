# Aeneas fuzzing harness — architecture

Fuzzer for the Aeneas Rust→Lean translation, targeting both the cryspen fork
(branch `dump-pure-ir-minimal`, charon v0.1.196) and upstream AeneasVerif/aeneas
(main, charon v0.1.223-era). One harness, two target configs.

## Layout

```
fuzz/
  DESIGN.md          this file
  STATUS.md          phase-by-phase status log
  README.md          how to run (written when stable)
  targets/*.toml     per-target config: charon cmd, aeneas cmd, env, known-bug fingerprints
  harness/           Rust crate (workspace-independent; cargo run from here)
    src/
      main.rs        CLI: campaign | one-shot | minimize | triage
      config.rs      target config loading
      corpus.rs      seed loading (tests/src), function extraction, packing
      mutate.rs      source-level mutators
      gen.rs         (phase 2) grammar generator
      pipeline.rs    rustc gate → charon → aeneas; process mgmt, timeouts
      oracle.rs      crash / reject / lean-elab / differential verdicts
      bisect.rs      function-list bisection + statement reduction
      triage.rs      crash-site fingerprint, dedupe DB, repro emission
    corpus/          persisted interesting inputs (committed selectively)
    findings/        auto-generated repro dirs (one per deduped finding)
  work/              scratch (gitignored): per-run crate dirs, llbc, lean out
```

## Pipeline (phase 1)

1. **Pack**: ~100 generated/mutated functions into one crate (`lib.rs` with
   `pub fn f_<i>...`), amortizing rustc+charon cost. Each function is tracked
   with its provenance (seed file, mutation chain, or generator seed).
2. **Validity gate**: `rustc --emit=metadata --crate-type=rlib` must accept
   (warnings ok). Functions failing the gate are dropped (rustc run once per
   pack; on failure, bisect to drop offenders).
3. **charon**: per-target command, matching pinned version. charon failure on
   rustc-accepted code is recorded (charon bug — out of scope, logged only).
4. **aeneas under test**: `-backend lean -dest <out> -abort-on-error
   -type-check-pure-code` (translation mode) and separately `-borrow-check`.
5. **Oracles**:
   - O1 crash: nonzero exit + internal-error/Unreachable/backtrace on
     rustc-accepted input → bug. Fingerprint = normalized OCaml file:line of
     the raise site (from backtrace) + error class.
   - O2 wrong-rejection: aeneas rejects (clean error) code rustc accepts.
     Classify by error site: join/collapse/fixpoint/borrow machinery ≈ real
     completeness bug; explicit `Unimplemented`/unsupported-feature gates ≈
     expected, not a finding.
   - O3 lean-elab: emitted Lean must `lake build` against `backends/lean`.
     Elaboration failure on successfully-translated code → bug.
   - (phase 2) O4 semantic differential: native rust exec vs Lean eval.
   - (phase 3) O5 stage differential: post-s2p vs post-micro pure-IR eval
     (fork only, via -dump-pure-ir + rust/pure-ir evaluator).
6. **Isolation on failure**: whole-crate failure → bisect the function list
   (log₂ passes re-running charon+aeneas) to a minimal function set, then
   statement-level reduction on the culprit.
7. **Triage**: dedupe by fingerprint against `findings/db.json` (which is
   pre-seeded with known bugs F4 #22, F6 #24, F5 #23 signatures so upstream
   fuzzing auto-recognizes them); new findings get a repro dir in the
   `documentation/translation-study/upstream-repros/` format (rs file,
   repro.sh, expected-output.txt, notes.md) + db entry recording which
   target(s) reproduce.

## Mutators (phase 1, source-level, operate on syn ASTs or token-level)

- borrow flips: `&`↔`&mut` (where rustc-valid), add/remove reborrows `&mut *x`
- op swaps: `+`↔`-`↔`*` (wrapping variants), comparison flips, bound nudges
- int edge values: 0, 1, MAX, MIN, MAX-1
- stmt duplication / reordering / deletion
- wrap block in `loop { ...; break; }` / add early `return` in loops
- if↔match on bool, introduce `let`-split of compound exprs
- shared-borrow reassignment before loops (F6 family)
- return-borrowed-value-in-loop shapes (F4 family)

## Targets

Config keys per target: name, aeneas bin, charon invocation (cmd + env),
extra aeneas flags, lean backend dir (for O3), supports_dump_pure_ir (bool),
known fingerprints. Fork additionally exposes `-dump-pure-ir
post-s2p:<dir>,post-micro:<dir>,pre-extract:<dir>` for phase 3.

## CI operation (recurring, not one-shot)

The campaign must run regularly on CI:

- `fuzz/setup/` provisions targets from pins on any machine: builds the fork
  aeneas + charon v0.1.196, clones/builds upstream aeneas @ recorded commit (or
  latest main) + its pinned charon, then *generates* the target TOMLs with
  machine-local paths (the checked-in `targets/*.toml` are for this dev machine;
  the config loader supports `${ENV}` substitution).
- GitHub Actions workflow: nightly schedule + workflow_dispatch; caches opam
  switch, rustup toolchains, cargo/charon build dirs, and the Lean driver
  project; runs a time-budgeted campaign per target; uploads findings/log as
  artifacts + job summary.
- `run --ci --time-budget <mins>`: seeds derived from the CI run id (logged);
  exit nonzero ONLY on new (non-deduped) findings — known bugs (e.g. F4/F6 on
  upstream) must not fail the job. `findings/db.json` is committed and is the
  cross-run dedupe baseline; newly confirmed findings get committed back (or
  attached as artifacts for manual commit).

## Determinism & persistence

Every generated crate is reproducible from (corpus rev, rng seed, mutation
chain); the campaign log records seeds. `work/` is disposable; `corpus/` and
`findings/` persist and are committed on the fuzz branch.
