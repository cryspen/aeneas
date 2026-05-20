# `cert-checker/` — the extractable cert-checker bundle

This directory bundles everything needed to read, verify, and
differentially test Aeneas-emitted certs *in Lean*. It's organised
so it can be split off into a standalone repository when desired —
nothing in this tree depends on anything else in the parent Aeneas
working copy beyond the inputs documented in §"External
dependencies" below.

## Contents

```
cert-checker/
├── README.md                        (this file)
├── aeneas-lean-checker/             — Lean cert parser / typechecker /
│                                      replayer / cert-walker / Rust-model
│                                      emitter. Lean-core only (no Mathlib).
├── aeneas-lean-soundness/           — M10 mechanised correspondence theorem.
│                                      Depends on Mathlib + the checker (sibling
│                                      relative path: `../aeneas-lean-checker`).
├── meta-harness/                    — Rust gate runner. Today: g_rust gate +
│                                      `--regen-models`. CI driver for the
│                                      differential cargo tests.
├── differential/                    — Rust differential-test crate.
│                                      Includes Rust models emitted by
│                                      `aeneas-check --rust-model` plus proptests
│                                      that compare them to the original source.
├── fixtures/                        — Smoke-test cert fixture (`incr_cert`).
├── scripts/
│   ├── check-llbc-trust.sh          — Z1 trust-audit gate. Run from repo root.
│   ├── check-vertical-slice.sh      — End-to-end vertical slice.
│   └── regen-diff-models.sh         — Regenerate Rust models from cert.
└── docs/
    ├── certificate-pipeline.md      — Architecture, theorems, gates.
    └── plans/                       — Historical campaign records +
                                       the forward-looking trust-removal plan.
```

## External dependencies (what's outside this bundle)

When prying this directory out to its own repository, these inputs
need to be brought along or referenced:

* **The OCaml cert emitter.** Lives at `../src/cert/` in the parent
  Aeneas repo (4k LOC OCaml). The cert format spec is at
  `../src/cert/cert_schema.json`. The cert emitter is invoked as
  `aeneas -emit-cert <input>.llbc`. A standalone cert-checker repo
  needs either a pinned binary or build instructions for the parent.

* **Rust source fixtures.** `../tests/src/*.rs` — referenced by
  `cert-checker/differential/tests/diff{,_auto}.rs` via
  `#[path = "../../../tests/src/<fix>.rs"]` attributes. Required for
  the differential testing harness.

* **Cert fixtures.** `../tests/llbc/*.cert.json` — referenced by the
  meta-harness's `--sweep tests/llbc`. The 89 fixtures are generated
  from `../tests/src/` via the emitter; they can be regenerated on
  demand with `cert-checker/scripts/regen-diff-models.sh`.

* **Mathlib pin.** `aeneas-lean-soundness/.mathlib-pin` and the
  `require mathlib` line in `aeneas-lean-soundness/lakefile.lean`.
  Pinned to `v4.30.0-rc2`; bumps go through deliberate Mathlib-PRs.

## Quickstart from the parent repo

Run all gates against the bundle from the parent repo root:

```bash
# Build the Lean checker (lean-core only, ~1s warm):
(cd cert-checker/aeneas-lean-checker && lake build aeneas-check)

# Build the soundness package (Mathlib, ~5min warm; check the M10 theorem):
(cd cert-checker/aeneas-lean-soundness && lake build)

# Build the meta-harness:
(cd cert-checker/meta-harness && cargo build --release)

# Run the differential property tests (today: 86 proptests):
(cd cert-checker/differential && cargo test --release --tests)

# G_rust sweep across all cert fixtures (today: 53/3143 decls pass,
# 76 fixtures skipped for lack of differential test coverage):
./cert-checker/meta-harness/target/release/meta-harness \
  --sweep tests/llbc \
  --gates g_rust \
  --source-crate cert-checker/differential

# Z1 LLBC-trust audit gate:
bash cert-checker/scripts/check-llbc-trust.sh

# End-to-end vertical slice (Rust → cert → Rust model → proptest):
bash cert-checker/scripts/check-vertical-slice.sh
```

## Trust boundary

The mechanised theorem
(`aeneas-lean-soundness/AeneasSoundness/Soundness/ReplayCrateSound.lean:158`,
`replayCrate_correspondence`) is proven against the Lean kernel only
(TCB: `{propext, Classical.choice, Quot.sound}`). What's trusted
operationally to use the theorem:

1. The Lean kernel.
2. The OCaml cert emitter (`../src/cert/`). Cross-checked by the
   differential harness; not formally proven.
3. Charon's Rust → LLBC translation (upstream of Aeneas).
4. The embedded LLBC metadata inside cert files (signatures,
   per-local types, ADT/trait decls, the LLBC body). Visible at a
   single grep-able audit surface
   (`aeneas-lean-checker/AeneasCheck/Translate/LlbcTrusted.lean`)
   enforced by `scripts/check-llbc-trust.sh`. The staged sequence to
   eliminate this entry (Z2 → Z3a → Z4a) is documented in
   `docs/plans/llbc-trust-removal-plan.md`.

What is *not* trusted: the cert events (replay validates them), the
Lean checker logic (its outputs are witnessed by the M10 proof), or
any paper-level meta-theorem.

## See also

* `docs/certificate-pipeline.md` — full pipeline architecture +
  theorems statement + gate reference.
* `docs/plans/llbc-trust-removal-plan.md` — the staged Z2/Z3a/Z4a
  trust-elimination pathway.
* `docs/plans/grust-coverage-expansion.md` — plan for increasing
  the 1.7% → ??% differential-test coverage of cert-walker outputs.
