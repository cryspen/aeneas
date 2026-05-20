//! Phase 4 MVP: emit IR-faithful Rust source from a Pure-IR JSON dump.
//!
//! This crate does **not** try to recover the byte-for-byte original
//! Rust source (use `item_meta.source_text` for that). Instead, it
//! demonstrates that the Pure-IR JSON carries enough structure to
//! re-emit syntactically valid, type-correct Rust source whose shape
//! mirrors the post-symbolic-to-pure IR.
//!
//! Entry point: [`emit_crate`] turns a parsed [`pure_ir::TranslatedCrate`]
//! into a single Rust source string. The companion CLI binary
//! `pir2rs` (under `src/bin/`) reads a JSON file from disk, parses it
//! with the `pure-ir` crate, and prints the emitted Rust to stdout.

pub mod emit;

/// Hand-curated table mapping Pure-IR Charon paths to their
/// `core_models::*` / `rust_primitives::*` Rust equivalents.
/// Consumed by the `route-shims` post-processor binary; **not used
/// by `emit::emit_crate`** — that's deliberate (Option A boundary).
/// A future Option C campaign will graduate this into the emitter
/// itself.
pub mod core_models_map;

pub use emit::{emit_crate, EmitOptions};
