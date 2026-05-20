//! Phase 1 Rust parser for Aeneas's Pure-IR JSON export.
//!
//! Consumes the JSON produced by `bin/aeneas -dump-pure-ir
//! post-s2p:<dest>` (see `src/pure/PureJson.ml`). The AST is hand-
//! written and mirrors the Phase-1 subset of `Pure.ml`. Everything
//! that Phase 1 does not yet model is surfaced as
//! [`Expr::Unsupported`] / [`Ty::Unsupported`] / a `_unsupported`
//! flag on decl stubs.

pub mod ast;
pub mod parser;

pub use ast::*;
pub use parser::{parse, ParseError};

/// The schema version this parser accepts. Bump on the OCaml side
/// when the on-disk shape changes; the parser will reject mismatched
/// versions explicitly via [`ParseError::UnsupportedVersion`].
pub const SUPPORTED_FMT_VERSION: u32 = 1;
