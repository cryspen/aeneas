# rust/ — Pure-IR Rust consumer trees

A Cargo workspace of two crates that consume the JSON dump produced by
Aeneas's `-dump-pure-ir <stage>:<dest>` flag and turn it into something
useful. The OCaml side of Aeneas (in `../src/`) is the producer; this
tree is the *consumer side* — independently versionable, independently
testable, and not part of Aeneas's existing extraction pipeline.

```
                                                ┌──────────────────┐
                                                │  rust/pure-ir/   │
   Rust source                                  │  (parser)        │
   tests/src/*.rs ──charon──→ LLBC ──aeneas──→  │  serde-driven    │  ──→  TranslatedCrate AST
                                                │  AST consumer    │
                                                └────────┬─────────┘
                                                         │
                                                         ▼
                                                ┌──────────────────┐
                                                │ pure-ir-emit-rust │
                                                │ (Rust emitter)   │  ──→  IR-faithful .rs
                                                │ pir2rs CLI       │       (rustc-typecheckable)
                                                └──────────────────┘
```

The OCaml-side hook lives at `src/Translate.ml`'s `translate_crate`;
the dump itself is wired through `src/pure/PureJson.{ml,mli}` (the
serializer). See `documentation/pure-ir-json-export-plan.md` for the
full campaign context (Phases 1–4) and the design rationale.

## Crates

| Crate | Role | README |
|---|---|---|
| [`pure-ir`](pure-ir/README.md) | Hand-written Rust AST mirroring `src/pure/Pure.ml`. `serde`-driven parser. The sole entry point for downstream consumers. | [pure-ir/README.md](pure-ir/README.md) |
| [`pure-ir-emit-rust`](pure-ir-emit-rust/README.md) | First downstream consumer: re-emits **IR-faithful Rust source** from the parsed AST. Includes a `pir2rs` CLI, a 89-fixture compile-check sweep, and a proptest-driven differential harness against the original source. | [pure-ir-emit-rust/README.md](pure-ir-emit-rust/README.md) |

Both build under one workspace; see `Cargo.toml` at the root of `rust/`.

## Pipeline at a glance

1. **OCaml side (`src/pure/PureJson.ml`):** serializes
   `Pure.translated_crate` to JSON at any of three pipeline stages:
   - `post-s2p` — right after symbolic-to-pure, before micro passes.
   - `post-micro` — after the micro-pass loop.
   - `pre-extract` — final shape just before the OCaml backends emit
     Lean / F\* / Coq.
2. **`pure-ir` parser:** `pure_ir::parse(src) -> TranslatedCrate`. Handles
   the deeply-nested `curve25519`-style fixtures by disabling
   `serde_json`'s default recursion limit and threading the stack via
   `serde_stacker`.
3. **`pure-ir-emit-rust` emitter:** `emit_crate(&crate, &opts) -> String`
   produces a `.rs` file that `rustc --emit metadata` accepts (parses +
   typechecks). Mutable borrows lower to forward + backward function
   pairs; loops to recursive helper fns; monadic lets to `?`-style;
   `Result`-wrapped fallible primitives via `checked_*`.

The emit is **not** a recovery of the original `.rs` source. Use
`item_meta.source_text` (preserved in the JSON dump) for that.

## Quick start

```bash
# From the repo root:
cd /Users/karthik/aeneas

# Build everything (OCaml + Rust)
gmake build-bin-dir       # builds bin/aeneas
(cd rust && cargo build)  # builds the workspace

# Dump Pure IR for one fixture
rm -rf /tmp/pir && mkdir /tmp/pir
bin/aeneas -backend lean -dest /tmp/pir \
    -dump-pure-ir pre-extract:/tmp/pir \
    tests/llbc/incr_cert.llbc

# Parse and inspect
python3 -c "import json; print(json.load(open('/tmp/pir/incr_cert.pure.json'))['fun_decls'][0]['item_meta']['name'])"

# Emit Rust
cd rust
cargo run -p pure-ir-emit-rust --bin pir2rs -- /tmp/pir/incr_cert.pure.json -o /tmp/incr_cert.rs

# Type-check the emit
rustc --edition 2021 --crate-type lib --emit metadata /tmp/incr_cert.rs -o /tmp/incr_cert.rmeta
```

## Test surface

```bash
cd rust
cargo test                  # all crates, all test binaries
cargo test -p pure-ir       # parser tests: 89-fixture × 3-stage sweep + goldens
cargo test -p pure-ir-emit-rust   # emitter tests: compile-check sweep + diff harness
```

Test bundles you'll see:

| Test binary | What it does | Wall time |
|---|---|---|
| `pure-ir::parse_all_fixtures` | Sweeps 89 × 3 = 267 JSON dumps; asserts parse-cleanly + zero `"UNSUPPORTED"` substrings | ~100s |
| `pure-ir::parse_goldens` | 5 committed fixtures × 3 stages; diff-on-disk regression | <1s |
| `pure-ir::parse_spans_and_attrs` | Source-span + attribute survival end-to-end | <1s |
| `pure-ir-emit-rust::compile_check` | 89 × 3 emit attempts via the Rust emitter; each output fed to `rustc --emit metadata` | ~120s |
| `pure-ir-emit-rust::diff` (hand-written) | proptest comparison of original Rust vs the emit, 22 blocks across 9 fixtures | <1s |
| `pure-ir-emit-rust::diff_auto` (auto-generated) | proptest comparison via signature-filtered auto-generator, 40 blocks across 7 more fixtures | <1s |

`make dump-pure-ir-sweep` (from the repo root) is the same sweep wired
through the OCaml-side `gmake` target.

## Layout

```
rust/
├── Cargo.toml              # workspace
├── pure-ir/
│   ├── Cargo.toml
│   ├── src/                # parser library
│   ├── tests/              # parser tests + committed goldens
│   └── README.md
└── pure-ir-emit-rust/
    ├── Cargo.toml
    ├── src/                # emitter library + CLI binaries
    ├── scripts/            # regen-diff-models.sh
    ├── tests/              # compile-check + diff harness
    └── README.md
```

## Design notes

- **One-way export.** OCaml writes JSON; Rust reads JSON. No OCaml-side
  `fromJson`. See `documentation/pure-ir-json-export-plan.md` § Round-trip
  decision.
- **Schema versioning.** The JSON envelope carries `pure_ir_fmt_version`;
  the parser rejects mismatched versions explicitly. Bump-on-schema-change.
- **Spans and attributes always-on.** Every decl carries `item_meta` with
  span (file/begin/end), structured Charon path name, source_text, and
  the full `attr_info` set (`#[derive]` derivatives become real impls
  before the IR sees them — see `pure-ir-emit-rust/README.md` for the
  full attribute-survival table).
- **Diff harness is standalone.** No dependency on `../cert-checker/`.
  Both the cert-checker's `aeneas-check --rust-model` pipeline and the
  emitter here independently consume Aeneas's output; cross-validation
  is a future structural cleanup (a shared `rust/differential/` crate
  pulling out the patterns), not a current dep.

## Related work

- `documentation/pure-ir-json-export-plan.md` — full campaign plan and
  acceptance table.
- `documentation/pure-ir-emit-rust-option-c.md` — the next-step design
  for routing every `core::*` / `alloc::*` reference in the emit through
  `~/rust-core-models/`.
- `../cert-checker/differential/` — the cert-checker's own R₀-vs-R₁
  proptest harness; reference implementation but not depended on.
