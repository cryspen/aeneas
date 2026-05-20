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

The sweep test (`tests/compile_check.rs`) emits Rust for every
`tests/llbc/*.llbc` fixture at every Pure-IR pipeline stage
(`post-s2p`, `post-micro`, `pre-extract`) — **89 fixtures × 3 stages
= 267 emits** — and verifies each one parses + typechecks with
`rustc --emit metadata`.

Current sweep result:

| | count |
|--|--|
| Emits that pass rustc | **175 / 267 (≈ 66 %)** |
| Fixtures with all three stages green | **50 / 89 (≈ 56 %)** |
| Pairs in `KNOWN_GAPS` (logged, skipped) | 92 |
| Unexpected failures (test panics) | 0 |

The 92 `KNOWN_GAPS` entries cluster into a small set of structural
limitations the emitter can't yet bridge without an extra resolution
pass:

| Class | ≈ count | Description |
|--|--|--|
| `move-of-FnOnce-backward-fn` | ~25 | Aeneas re-uses backward fns across branches; `Box<dyn FnOnce>` is consumed on first call. |
| `loop_op-positional-arg-mismatch` | ~25 | `LoopOp` shim has a fixed shape (`F: FnOnce(T) -> Result<T>`) but IR sites pass diverse arities. |
| `trait-method-* placeholder` | ~20 | `Qualif::FunOrOp(_, TraitMethod(_))` collapses to `unimplemented!()` — many fixtures call stdlib traits. |
| `destructure-Box-{LCell,multi-binder}` | ~10 | Stable Rust has no `box` patterns; recursive ADT field destructure can't pierce a `Box<Self>`. |
| `type-changing-struct-update` | ~3 | Aeneas `..init` can change generic args; Rust struct-update requires identical types. |
| Miscellaneous (curve25519 size, FFI `fmt::Arguments` shape, etc.) | ~10 | One-offs. |

Unhandled IR variants degrade to `unimplemented!(<msg>)` /
`Default::default()` / typed `Err::<_,()>(())` placeholders so the
output stays rustc-parseable even when downstream operations can't
recover the IR's intent.

### What "IR-faithful" still means

The emitter does **not** try to recover original Rust source — the
goal is rustc-parseable / type-correct output that mirrors the
Pure-IR JSON's structure (one Rust construct per AST node).
Closures arrive as `Box<dyn FnOnce(_) -> _>`; backward fns as
ordinary `Box<dyn FnOnce>` values; recursive ADTs as
`Box<Self>`-wrapped variants; etc.

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
