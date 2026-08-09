//! Phase-1 fuzzing harness for the Aeneas Rust->Lean translator.
//!
//! Modules:
//!   * [`config`]   — target configuration loading (config-driven commands)
//!   * [`corpus`]   — seed loading, function extraction, crate packing
//!   * [`mutate`]   — source-level mutators
//!   * [`pipeline`] — rustc gate -> charon -> aeneas, with timeouts
//!   * [`oracle`]   — crash / reject classification and fingerprinting
//!   * [`bisect`]   — function-list bisection + statement reduction
//!   * [`triage`]   — fingerprint dedup DB + repro emission
//!
//! See `fuzz/DESIGN.md` for the architecture and `fuzz/targets/example.toml`
//! for the config schema.

pub mod bisect;
pub mod config;
pub mod corpus;
pub mod gen;
pub mod mutate;
pub mod oracle;
pub mod pipeline;
pub mod semdiff;
pub mod triage;
