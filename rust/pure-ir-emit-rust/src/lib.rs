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

pub use emit::{emit_crate, EmitOptions};
