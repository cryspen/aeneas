# pure-ir

`serde`-driven Rust parser for the JSON dump produced by Aeneas's
`-dump-pure-ir <stage>:<dest>` flag (OCaml-side serializer at
`src/pure/PureJson.{ml,mli}`).

The AST in `src/ast.rs` mirrors `src/pure/Pure.ml` one-for-one: every
constructor of `Pure.expr`, `Pure.ty`, `Pure.literal`, `Pure.qualif`,
`Pure.tpat` / `Pure.pat`, `Pure.binop` is present, plus the full decl
envelope (`FunSig`, `FunBody`, `FunDecl`, `TypeDecl`, `GlobalDecl`,
`TraitDecl`, `TraitImpl`). Tagged sums use `{"kind": "...", "payload": ...}`;
serde's `tag = "kind", content = "payload"` adapter does the lifting.

This crate is intended as the **single entry point** for any Rust
consumer of the Pure IR. Downstream code calls `pure_ir::parse(...)`
and walks the returned `TranslatedCrate`.

## API

```rust
pub fn parse(src: &str) -> Result<TranslatedCrate, ParseError>;
pub const SUPPORTED_FMT_VERSION: u32 = 2;
```

`parse` does a two-pass deserialisation:

1. Lightweight envelope check — reads `pure_ir_fmt_version` and rejects
   anything that doesn't match `SUPPORTED_FMT_VERSION`. Schema bumps on
   the OCaml side are caught here.
2. Full AST deserialisation. We **disable serde_json's 128-level
   recursion guard** and wrap with `serde_stacker` so deeply-nested
   fixtures (`curve25519`'s let/App chains) parse without blowing the
   stack.

`ParseError::UnsupportedVersion { got, supported }` is the
schema-mismatch case; `ParseError::Json(serde_json::Error)` covers
everything else.

## Usage

```rust
use pure_ir::{parse, TranslatedCrate};

let src = std::fs::read_to_string("/tmp/pir/incr_cert.pure.json")?;
let krate: TranslatedCrate = parse(&src)?;

for fn_decl in &krate.fun_decls {
    println!("{}: {} input(s), output={:?}",
        fn_decl.name,
        fn_decl.signature.inputs.len(),
        fn_decl.signature.output);
}
```

## Quick start

```bash
# From the repo root:
cd /Users/karthik/aeneas

# Build aeneas + the workspace
gmake build-bin-dir
(cd rust && cargo build -p pure-ir)

# Dump a fixture
rm -rf /tmp/pir && mkdir /tmp/pir
bin/aeneas -backend lean -dest /tmp/pir \
    -dump-pure-ir pre-extract:/tmp/pir \
    tests/llbc/incr_cert.llbc

# Spot-check JSON shape
python3 -c "import json; d = json.load(open('/tmp/pir/incr_cert.pure.json')); print(list(d.keys()))"
```

## Tests

| Binary | What it asserts | Wall time |
|---|---|---|
| `parse_incr_cert` | Smoke: aeneas dumps incr_cert, parser reads it, fn count matches expectations | <1s |
| `parse_all_fixtures` | Sweep: 89 fixtures × 3 stages = 267 dumps, each parses without `"UNSUPPORTED"` substrings | ~100s |
| `parse_goldens` | Per-stage golden snapshots for 5 representative fixtures (15 files); diff fails on schema drift | <1s |
| `parse_spans_and_attrs` | `item_meta.span.file`, line/col, source_text, and `attr_info.attributes` survive end-to-end | <1s |

Run with:

```bash
cd rust
cargo test -p pure-ir
```

Or via the OCaml-side gmake target:

```bash
gmake dump-pure-ir-sweep    # runs the 267-pair sweep
```

## Layout

```
pure-ir/
├── Cargo.toml
├── src/
│   ├── lib.rs          # crate root; pub use ast, parser
│   ├── ast.rs          # hand-written AST mirroring Pure.ml
│   └── parser.rs       # version-check + serde deserialisation
└── tests/
    ├── parse_incr_cert.rs
    ├── parse_all_fixtures.rs
    ├── parse_goldens.rs
    ├── parse_spans_and_attrs.rs
    └── golden/         # 15 committed JSON dumps (5 fixtures × 3 stages)
```

## Design notes

- **Hand-written, not generated.** We could PPX-derive these types
  from the OCaml side (`ppx_deriving_yojson_safe`-style) but Phase 1
  picked hand-writing as the lowest-risk path; trades a few hundred
  lines of mechanical translation for full control over the schema.
- **One-way only.** No `toJson` on the Rust side — this crate consumes
  but does not write back. The OCaml side is the schema source of
  truth.
- **Spans + attributes always-on.** Every decl's `item_meta` carries
  Charon's full `attr_info` plus source span (file/begin/end). See
  `../README.md` and the `parse_spans_and_attrs` test for the
  attribute-survival table.
- **Encoding compatibility.** The `{"kind": "X", "payload": …}` shape
  was picked specifically so a future PPX-derive on the OCaml side
  could be slotted in without breaking the Rust consumer.

## Related

- `../README.md` — workspace overview, full pipeline diagram.
- `../pure-ir-emit-rust/` — first downstream consumer (IR-faithful
  Rust emitter).
- `../../documentation/pure-ir-json-export-plan.md` — campaign plan.
- `../../src/pure/PureJson.ml` — OCaml-side serializer (the producer).
