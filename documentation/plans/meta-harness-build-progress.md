# meta-harness build progress (2026-05-18)

*Closes the campaign described in
`prompts/meta-harness-build-prompt.md`. Contract:
`meta-harness-contract.md`. PoC fixture: `incr_cert`.*

## What was built

`tools/meta-harness/` — a project-agnostic differential-testing tool
for Aeneas, packaged as a Rust binary. Six phases, six commits:

| Phase | Commit subject                                                  | Coverage |
|-------|-----------------------------------------------------------------|----------|
| A     | meta-harness scaffolding: per-decl enumeration from cert        | clap CLI, `Cert` loader (fn / global / type / trait / trait_impl), JSON + Markdown skeletons |
| B     | meta-harness Phase B: per-decl G_byte gate                      | invoke mainline `aeneas -backend lean` + `aeneas-check --out`; whole-file fast-path then per-decl slicing; honors manifest overrides |
| C     | aeneas-check: --only-decl CLI flag (Phase C)                    | adds `--only-decl <Charon path>` to `aeneas-check` (Lean side only) so single-decl emit is achievable; mainline OCaml `--only-decl` deferred |
| D     | meta-harness Phase D: G_rust gate via source-tests-as-oracle    | runs `cargo test --no-fail-fast` against the source crate, maps test names to cert decls via name-stem heuristic, reports pass / mismatch / skip(no_test_coverage) |
| E     | meta-harness Phase E: report + manifest                         | `[gates]` toggle support, structural exit code 0/1/2, sample manifest at `tools/meta-harness/examples/meta-harness.toml` |
| F     | this document                                                   | PoC validation + writeup |

## How to invoke

```bash
# Build
cargo build --manifest-path tools/meta-harness/Cargo.toml --release

# Run (Phase F PoC)
./tools/meta-harness/target/release/meta-harness \
  --cert tests/llbc/incr_cert.cert.json \
  --source-crate tests/lean-checker/differential \
  --gates g_byte,g_rust \
  --report-json report.json --report-md report.md
```

CLI shape: `--crate` / `--llbc` / `--cert` (only `--cert` is fully
wired in this round; the other two `unimplemented!`); `--gates
g_byte,g_rust` (default: `g_byte`); `--source-crate <path>` for the
G_rust crate; `--manifest <path>` optional; `--aeneas` /
`--aeneas-check` overrides (auto-detected against the in-repo
build paths).

## PoC result — `tests/llbc/incr_cert.cert.json`

```
[meta-harness] decls: 2  gates: g_byte,g_rust
[meta-harness] wrote report.json and report.md
Exit: 0

## Gate aggregate
| Gate   | pass | divergent | mismatch | skip | not-run | fail |
|--------|------|-----------|----------|------|---------|------|
| g_byte |   2  |     0     |     0    |   0  |    0    |   0  |
| g_rust |   1  |     0     |     0    |   1  |    0    |   0  |

## Per-decl detail
| incr_cert::incr        | fn | g_byte | pass |                  |
| incr_cert::incr        | fn | g_rust | pass |                  |
| incr_cert::incr_local  | fn | g_byte | pass |                  |
| incr_cert::incr_local  | fn | g_rust | skip | no_test_coverage |
```

Honest result. `incr_cert::incr` matches `incr_matches_model` in
`tests/lean-checker/differential/tests/diff.rs` (line 29); `incr_local`
has no test, which the harness surfaces rather than papering over.

## Sweep-level validation — G_byte against existing baseline

Running the gate over every `tests/llbc/*.cert.json` (89 fixtures):

```
Per-decl totals:        pass=64  divergent=742  mismatch=0  skip=2337
Per-fixture aggregate:  pass=3   divergent=83   skip=3      mismatch=0
```

Per-fixture aggregate matches `scripts/compare-backends.sh --sweep`
post-Session 7 exactly:
- 3 pass: `blanket_impl`, `enums_basic`, `incr_cert`
- 3 skip: `closures`, `issue-804-closure-return-ref`, `raw_pointers`
  (mainline can't emit them)
- 83 divergent: everything else

The per-decl `skip=2337` figure reflects the Phase B slicer's
limitation — it can't reliably name-match impl methods, trait_impls,
or types between L₀ and L₁. **Phase C lands `--only-decl` on
aeneas-check** so that future work can replace the slicer with
single-decl invocations; the OCaml mainline side is still required
for an apples-to-apples L₀ comparison and is deferred.

## Multi-fixture validation (post-Phase F)

After the PoC commit, the harness was swept across every fixture
covered by a proptest in
`tests/lean-checker/differential/tests/diff.rs` (12 fixtures, 198
decls). All exit-0; **zero `mismatch` outcomes** anywhere.

| Fixture            | decls | g_byte pass/div/skip | g_rust pass/skip |
|--------------------|------:|---------------------:|-----------------:|
| `incr_cert`        |     2 |     2 /  0 /  0      |    1 /  1        |
| `constants`        |    32 |     0 / 29 /  3      |    3 / 29        |
| `bitwise`          |     5 |     3 /  2 /  0      |    5 /  0        |
| `compare_simple`   |     4 |     2 /  1 /  1      |    2 /  2        |
| `calls`            |     6 |     1 /  4 /  1      |    2 /  4        |
| `aggregates_basic` |     3 |     2 /  1 /  0      |    2 /  1        |
| `reborrows`        |     4 |     3 /  1 /  0      |    1 /  3        |
| `scalars`          |    39 |     4 / 19 / 16      |   13 / 26        |
| `demo`             |    20 |     3 / 13 /  4      |    4 / 16        |
| `enums_basic`      |     2 |     2 /  0 /  0      |    1 /  1        |
| `enums_payload`    |     4 |     3 /  1 /  0      |    3 /  1        |
| `no_nested_borrows`|    77 |    12 / 63 /  2      |    5 / 72        |

Total: 12 fixtures, 198 decls, **42 g_rust passes** matching the 42
distinct decls covered by the differential crate's 44 proptests (two
tests are variants — `_small` / `_top` — of the same decl).

### Bug found and fixed during the sweep

The initial `g_rust` stem heuristic over-matched: `demo::Counter::incr`
and `demo::{demo::Counter for usize}::incr` both claimed
`demo_incr_matches_model` even though the test actually covers
`demo::incr`. Root cause: the short-stem fallback (e.g. `incr`)
matched too aggressively when multiple decls shared a last-segment
name.

Fix: longest-stem-wins assignment. For each test, the harness now
picks the decl whose matching stem is longest (with first-decl-in-cert
as the deterministic tiebreak). Locked in by unit tests
`brace_stripped_decl_collides_with_inherent` and
`short_stem_does_not_over_prefix` in `gates/g_rust.rs`.

Demo went from 7 (3 false-positive) → 4 (correct) g_rust passes.

## What's deferred (scope cuts)

- **OCaml mainline `--only-decl`.** Phase C ships only the Lean side
  (`aeneas-check --only-decl`). The mainline `src/extract/` pipeline
  would need its own allowlist threaded through; it's a larger touch
  than the "minimal flag-plumbing" Phase C ceiling. Until it lands,
  the meta-harness's G_byte gate uses Phase B's whole-file emit +
  decl-header slicing on the L₀ side.
- **Swap-based emit-rust path** (contract §4 G_rust). The PoC reuses
  the existing model-based oracle in `tests/lean-checker/differential/`
  (`aeneas-check --rust-model`). For external crates that don't have
  a model-based test crate already, a swap-based path
  (`aeneas-check --emit-rust` producing drop-in `src/`, then
  re-running the crate's own tests) is the next step.
- **G_lean gate.** Closed by transitivity from G_rust + G_byte per
  contract §4; no separate runner needed.
- **G_rfl gate.** Doesn't exist yet (`example : L₀.foo = L₁.foo := by
  rfl` per decl); deferred per contract §4.
- **Charon front-end** (`--crate <Cargo.toml>` and `--llbc <path>`).
  Both shapes `unimplemented!()`; the harness today is `--cert`-only.
- **CI integration.** Out of campaign scope.
- **Migration of `tests/lean-checker/differential/` into per-fixture
  `tests/src/*.rs` `#[cfg(test)] mod tests` blocks.** Tracked
  separately by `fixtures-as-crate-migration.md`, gated behind the
  zero-skip campaign closing.

## Architectural surprises worth flagging back to the contract

- **`--rust-model` already exists** and gives us the R₁ model used by
  the existing differential crate. The contract §4 G_rust writeup
  describes adding `--emit-rust` as net-new infrastructure;
  `--rust-model` is the *existing* equivalent (suffixed-name flavour).
  Worth noting in the contract that the in-tree path is
  model-based-via-`--rust-model` + cargo-test-against-the-existing-
  differential-crate; the contract's swap-based `--emit-rust` is for
  external crates that don't already wrap their R₁ behind a
  `_model`-suffix indirection.
- **Decl-name matching to test names is non-uniform.** In
  `tests/lean-checker/differential/tests/diff.rs`, some test names
  drop the crate prefix (`incr_matches_model` for `incr_cert::incr`)
  while others keep it (`constants_incr_matches_model` for
  `constants::incr`). The stem heuristic in `gates/g_rust.rs` covers
  both, but the right long-term answer is to declare the mapping in
  `meta-harness.toml` (per-decl `[decls.<path>].g_rust.test = "..."`)
  rather than relying on naming conventions. Not blocking, but worth
  adding to the contract's manifest schema.
- **Per-fixture `pass` count went from 1 (Session 6 baseline) to 3
  (post-Session 7 fix) without any change to the meta-harness.** The
  harness just inherits whatever the underlying emitters produce; the
  same per-decl counts apply when those emitters get cleaner. Validates
  the contract premise that the harness should be parameterised over
  the crate, not over the emitter version.

## New blockers / follow-ups

- OCaml mainline `--only-decl` is the prerequisite for moving the
  G_byte gate from file-grained + slicing to true per-decl
  invocations. Estimate ~1 day of OCaml work in `src/extract/` to
  thread an `only_decl` allowlist; not blocking the PoC.
- `cargo test`'s machine-readable output is gated behind nightly's
  `-Z unstable-options --format json`. The Phase D parser walks
  human-readable text and ANSI-strips it; should be replaced with the
  JSON format once stabilised, or with a small custom test harness.
- For external crates without an existing differential test layout,
  Phase D's test-name stem heuristic will under-match. The contract's
  vector-spec or test-mapping section in `meta-harness.toml` is the
  right answer there; not yet wired in.

## Wall-clock time

~4 hours single session. Phases A–E built incrementally with
inline validation. Phase F is this writeup.
