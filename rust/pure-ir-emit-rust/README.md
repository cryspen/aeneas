# pure-ir-emit-rust

Phase 4 MVP of the Aeneas Pure-IR JSON export campaign. Reads the JSON
produced by `bin/aeneas -dump-pure-ir <stage>:<dest>` (via the
`pure-ir` crate next door), and emits **IR-faithful Rust source**
that `rustc` accepts.

## What "IR-faithful" means

The output is **not** a byte-for-byte recovery of the original
`.rs` — symbolic-to-pure has functionalised mutable borrows, fused
loops into recursive helpers, and threaded `Result` through fallible
operations. Use `item_meta.source_text` if you want the original
verbatim Rust.

Instead, the emitter targets:

1. **Syntactically valid Rust** (`rustc --edition 2021` parses it).
2. **Type-correct** (passes `rustc --crate-type lib --emit metadata`).
3. **Structurally faithful to the Pure IR** — one Rust construct per
   AST node, no folding back into idiomatic Rust:
   - Mutable borrows → forward + backward functions threading
     ownership.
   - Loops → separate recursive `_loop0` helper fns.
   - Monadic `Let` → `let x = e?;`.
   - `Match` → Rust `match`.

For example, `pub fn incr(x: &mut u32) { *x += 1; }` from
`tests/src/incr_cert.rs` becomes:

```rust
pub fn incr(x: u32) -> Result<u32> {
    let v0: u32 = x;
    let v1: u32 = (v0.checked_add(1u32).ok_or(()))?;
    let v2: () = Ok(())?;
    let v3: u32 = { let x: u32 = v1; x };
    Ok(v3)
}
```

— note the explicit ownership thread, `?`-propagated overflow check,
and identity rebind from the s2p pipeline.

## Usage

```bash
# Build the crate (uses the workspace at rust/Cargo.toml)
cargo build -p pure-ir-emit-rust

# Emit Rust for a single JSON dump
cargo run -p pure-ir-emit-rust --bin pir2rs --quiet -- \
    pure-ir/tests/golden/incr_cert.post-s2p.pure.json \
    -o /tmp/incr_cert.rs

# Verify it typechecks
rustc --edition 2021 --crate-type lib /tmp/incr_cert.rs \
    --emit metadata -o /tmp/incr_cert.rmeta

# Run the bundled integration tests
cargo test -p pure-ir-emit-rust
```

## Coverage

The MVP targets a small representative whitelist (see
`tests/compile_check.rs`):

- `incr_cert` — mut-borrow forward+backward; the canonical example.
- `enums_basic` — enum + match.
- `traits_basic` — trait + impl + direct method call.
- `loops_simple` — loop → recursive helper + `LoopOp` combinator.

Each is tested at all three pipeline stages (`post-s2p`,
`post-micro`, `pre-extract`). Spot-checks pass for `compare_simple`,
`aggregates_basic`, and `bitwise` too.

Unhandled IR variants degrade to `unimplemented!(<msg>)` with a
`// TODO:` comment; the output stays rustc-parseable.

## Layout

```
pure-ir-emit-rust/
├── Cargo.toml
├── src/
│   ├── lib.rs          # crate root; pub fn emit_crate(...)
│   ├── emit.rs         # the emitter (one helper per AST node type)
│   └── bin/pir2rs.rs   # CLI entrypoint
└── tests/
    ├── emit_incr_cert.rs   # focused incr_cert tests
    └── compile_check.rs    # whitelist sweep + rustc shell-out
```

See `documentation/pure-ir-json-export-plan.md` § Phase 4 for the
broader campaign context.
