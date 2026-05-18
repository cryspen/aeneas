# meta-harness

Project-agnostic differential-testing harness for Aeneas.

Given an Aeneas `.cert.json` and (optionally) a Cargo crate whose
tests serve as the source-of-truth oracle, the harness emits a
per-decl `report.json` + `report.md` saying which decls passed which
gate. The gates today are:

- **g_byte** — L₀ vs L₁ byte-identity. Runs mainline `aeneas -backend
  lean` and `aeneas-check --out`, then diffs at file granularity
  (fast path) and falls back to per-decl slicing of the emitted Lean.
- **g_rust** — source-tests-as-oracle. Runs `cargo test` against
  `--source-crate`, parses pass/fail, and maps test names to decls.

`g_lean` closes by transitivity (g_rust + g_byte/g_rfl), so there is
no separate runner. `g_rfl` is not implemented yet.

## Quick start

```bash
cargo build --manifest-path tools/meta-harness/Cargo.toml --release

# Single fixture
./tools/meta-harness/target/release/meta-harness \
  --cert tests/llbc/incr_cert.cert.json \
  --source-crate tests/lean-checker/differential \
  --gates g_byte,g_rust \
  --report-json report.json \
  --report-md report.md

# Fleet-wide sweep over all *.cert.json in a directory
./tools/meta-harness/target/release/meta-harness \
  --sweep tests/llbc \
  --source-crate tests/lean-checker/differential \
  --gates g_byte,g_rust \
  --report-json sweep.json \
  --report-md sweep.md
```

In sweep mode the harness:
- runs `cargo test` once and shares the result across fixtures
- resolves test ownership globally (longest matching stem wins; ties
  are reported as `ambiguous` and excluded so no decl falsely claims
  the test) — this prevents short-stem fallbacks like `incr` from
  being claimed by every fixture that happens to define an `incr` fn

Exit codes:
- `0` — all gates clean (modulo `divergent` allowlisted entries)
- `1` — at least one gate reported `mismatch` or `fail`
- `2` — structural error (cert parse failed, gate runner crashed,
  missing binary)

## CLI

| Flag                          | Meaning |
|-------------------------------|---------|
| `--cert <path>`               | A pre-built `.cert.json`. |
| `--sweep <dir>`               | Directory of `*.cert.json` files. Produces a fleet-wide report. |
| `--crate <path>`              | A Cargo crate root. **Not yet wired in.** |
| `--llbc <path>`               | A pre-built `.llbc`. **Not yet wired in.** |
| `--source-crate <path>`       | Crate whose `cargo test` is the G_rust oracle. Defaults to `--crate` if set. |
| `--gates g_byte,g_rust`       | Comma-separated. Default: `g_byte`. Use `none` to enumerate decls only. |
| `--report-json <path>`        | Default: `./report.json`. |
| `--report-md <path>`          | Default: `./report.md`. |
| `--manifest <path>`           | `meta-harness.toml` overriding gate toggles and per-decl skips. Defaults to `<crate>/meta-harness.toml` if present. |
| `--aeneas <path>`             | Override the aeneas binary. Auto-detects `src/_build/default/main.exe`. |
| `--aeneas-check <path>`       | Override the aeneas-check binary. Auto-detects `aeneas-lean-checker/.lake/build/bin/aeneas-check`. |

## Manifest

Place a `meta-harness.toml` at the crate root (or pass `--manifest`).
All fields are optional. See `examples/meta-harness.toml`.

```toml
[gates]
g_byte = "auto"        # "skip" drops the gate; "auto" runs it (default)
g_rust = "auto"

[decls."crate::path::fn"]
g_rust = { skip = "api_reshape" }              # honest skip
g_byte = { divergent = "whitespace-only" }     # allowlist divergence
```

## Design

See `documentation/plans/meta-harness-contract.md` for the contract
and `documentation/plans/meta-harness-build-progress.md` for the
build campaign writeup, the PoC validation, and the deferred-scope
list (OCaml `--only-decl`, swap-based emit-rust, charon front-end,
CI integration, the `tests/lean-checker/differential/` migration).
