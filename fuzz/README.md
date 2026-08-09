# Aeneas translation fuzzer

A source-level fuzzer for the Aeneas Rust→Lean translator. It mutates the
`tests/src` seed corpus, packs functions into crates, drives them through
`rustc → charon → aeneas`, and classifies the outcome (crash / wrong-rejection /
elaboration failure) with dedup against a findings DB. It targets **both** the
cryspen fork (`dump-pure-ir-minimal`, charon v0.1.196) and upstream
AeneasVerif/aeneas — one harness, two config-driven targets.

- **Architecture / oracles / pipeline:** see [`DESIGN.md`](DESIGN.md).
- **Phase-by-phase status:** see [`STATUS.md`](STATUS.md).
- **Semantic-differential (Lean eval) recipe:** [`semdiff/RECIPE.md`](semdiff/RECIPE.md).

```
fuzz/
  harness/        Rust crate (the fuzzer). Standalone: cargo from harness/.
  targets/*.toml  per-target config (charon+aeneas commands, known-bug prints)
  setup/          provisioning scripts: build/locate targets, export env vars
  findings/       findings DB (db.json) + auto-emitted repro dirs
  work/           scratch (gitignored): per-run crate dirs, llbc, lean out, logs
```

## Building the two targets

The target TOMLs reference machine paths via `${VAR:-default}`; the config
loader expands these from the environment (defaults match this dev machine, so
they work as-is). The `setup/` scripts build/locate each target and **export the
contract**. Source them (they persist the vars; in CI they also append to
`$GITHUB_ENV`):

```bash
# Fork (needs opam switch `aeneas` + the v0.1.196 charon wrapper):
source fuzz/setup/build_fork.sh        # dune build src/, copy bin/aeneas, locate charon

# Upstream (clones AeneasVerif/aeneas + its pinned charon to /tmp/aeneas-upstream):
source fuzz/setup/build_upstream.sh

# Or, if targets are already built, just set/export the vars (build on demand):
source fuzz/setup/env.sh               # FUZZ_TARGET=fork|upstream|both
```

Env-var contract (all overridable; see [`setup/common.sh`](setup/common.sh)):

| var | meaning | default |
|---|---|---|
| `AENEAS_FORK_ROOT` | fork checkout root (`bin/aeneas`, `backends/lean`) | repo root |
| `CHARON_FORK_BIN` | fork charon wrapper (v0.1.196) | `$AENEAS_FORK_ROOT/charon/charon/target/release/charon` |
| `AENEAS_UPSTREAM_ROOT` | upstream aeneas checkout | `/tmp/aeneas-upstream` |
| `CHARON_UPSTREAM_BIN` | upstream charon wrapper (v0.1.225) | `$AENEAS_UPSTREAM_ROOT/charon/bin/charon` |
| `AENEAS_UPSTREAM_PIN` | upstream commit/tag to build (unset ⇒ track `main`) | — |

Pinned facts live in `setup/common.sh`: opam switch `aeneas`, fork charon
v0.1.196, upstream charon `527ea8e3` (v0.1.225), upstream aeneas recorded-good
commit `3a8586fa`. Upstream charon needs `rustup`/`cargo` on `PATH` **at run
time** (it shells out to its nightly toolchain); the upstream TOML prepends the
charon bin dir to the inherited `PATH` via `${PATH}`.

## Running a local campaign

```bash
cargo build --release --manifest-path fuzz/harness/Cargo.toml

# A fixed number of rounds against the fork:
cargo run --release --manifest-path fuzz/harness/Cargo.toml -- \
  run --target fuzz/targets/fork.toml \
      --rounds 50 --pack-size 100 --seed-dir tests/src

# Against upstream (after build_upstream.sh):
cargo run --release --manifest-path fuzz/harness/Cargo.toml -- \
  run --target fuzz/targets/upstream.toml --rounds 50 --seed-dir tests/src
```

Other subcommands: `one --input X.rs` (single crate, print verdict + dedup),
`minimize --input X.rs` (bisect + statement-reduce a failing input),
`list-findings`.

## CI mode (`run --ci`)

`--ci` makes a run reproducible and machine-scored:

- **Seed:** derived from `GITHUB_RUN_ID`/`GITHUB_RUN_ATTEMPT` when present (else
  `--seed`), and **logged prominently** so any failure is reproducible.
- **Time budget:** `--time-budget <minutes>` runs rounds until the wall-clock
  budget elapses (checked between rounds), ignoring `--rounds`.
- **Exit code:** `0` when only known/deduped fingerprints and expected rejects
  were seen; **`3`** when one or more NEW (non-deduped, non-expected-reject)
  findings were recorded. (`1` = harness error.)
- **Outputs:** a machine-readable `summary.json` (`--summary-out`, default
  `<work>/<run>/summary.json`) and a Markdown block (`--md-summary-out`,
  suitable for `$GITHUB_STEP_SUMMARY`). New findings' repro dirs land under
  `fuzz/findings/` as usual.

```bash
cargo run --release --manifest-path fuzz/harness/Cargo.toml -- \
  run --ci --time-budget 30 \
      --target fuzz/targets/fork.toml \
      --pack-size 100 --seed-dir tests/src \
      --md-summary-out /tmp/step-summary.md
# prints e.g.:
# CI RESULT: 0 new findings (24 known crashes, 10 expected rejects, 28 successes)
```

## Findings + the DB

`findings/db.json` is the **committed cross-run dedupe baseline**. Each entry is
a fingerprint `(error_class, basename(file), line)` matched with ±30-line drift
(raise sites move between builds). Pre-seeded known bugs: **F4** (#22,
`PureMicroPassesLoops.ml:1818`), **F5** (#23, latent), **F6** (#24,
`InterpAbs.ml:1671`).

- A crash whose fingerprint matches the DB → **known**, recorded (which targets
  reproduce it), does not fail CI.
- A crash with no match → **new**: bisected to a minimal function set,
  statement-reduced, and emitted as `findings/<slug>/` (`min.rs`, `repro.sh`,
  `observed-output.txt`, `notes.md`) plus a new `db.json` entry. Fails CI (exit 3).
- **Expected rejects** (feature-gate `craise`s, unsupported-feature messages)
  are classified via `harness/data/expected_reject_patterns.txt` and never fail CI.

Inspect the DB with `run … list-findings` or read `findings/db.json`. The
`summary.json` `fingerprints[]` list flags each site `known`/new with its id.

## CI wiring & reproducing a failure

The workflow is [`.github/workflows/fuzz-nightly.yml`](../.github/workflows/fuzz-nightly.yml),
built for cryspen's **self-hosted nix runners** (same as `ci.yml`):

- **Build:** `nix build .#aeneas` produces `result/bin/aeneas` **and** a
  version-matched `result/bin/charon` (the flake symlinks charon into the aeneas
  output; `flake.lock`/`charon-pin` are the pin, enforced by the flake's
  `check-charon-pin`). So there is **nothing to pin by hand** in CI. The harness
  builds and runs inside `nix develop --command` (Rust via `rustup`, elan for the
  optional Lean oracle) — the same shell `ci.yml` uses for Lean.
- **Triggers:** nightly cron (fork, fast crash/reject oracles, ~25 min) + weekly
  cron (fork, longer ~90 min campaign) + `workflow_dispatch` (`time_budget`,
  `seed`, `oracle_scope`). CI is **fork-only**: it guards the fork's own changes;
  the fork-vs-upstream differential is a local/manual activity (`build_upstream.sh`).
- **Oracle scope:** the crash/reject oracles (O1/O2) run by default; Lean
  elaboration (O3, `--lean-elab`) is opt-in via `oracle_scope=lean`. The
  native-vs-Lean semantic differential (`semdiff/`) and the Phase-3 pure-IR
  stage differential (`pure-eval/`, `stage-diff/`, which need the fork-only
  `-dump-pure-ir`) are **not** in the scheduled lanes — the pure-IR oracles live
  on the dump-pure-ir branch, and semdiff's recipe/extension point is in
  `semdiff/RECIPE.md`.
- **Job status:** green on known/expected results; **red only when the harness
  exits 3** (new findings). `fuzz/findings/`, `fuzz-summary.json`, and
  `campaign.jsonl` upload as artifacts on every run.
- Newly confirmed findings are **not** auto-committed — a maintainer triages the
  artifacts and commits `db.json` + repro dirs manually.

> Note: GitHub only fires **scheduled** workflows from the default branch, so
> this file must live on `main` for the nightly/weekly lanes to run.

**Reproduce a CI failure locally** from the seed logged in the job (search the
log for `EFFECTIVE SEED`):

```bash
source fuzz/setup/env.sh
cargo run --release --manifest-path fuzz/harness/Cargo.toml -- \
  run --target fuzz/targets/<target>.toml \
      --seed <EFFECTIVE_SEED> --rounds <n> --pack-size 100 --seed-dir tests/src
```

Same seed + same corpus revision + same target ⇒ same crates (the RNG and
mutation chain are fully determined by the seed). A single reproducer can then be
shrunk with `minimize --input <repro>/min.rs`.
