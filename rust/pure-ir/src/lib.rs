//! Rust parser for Aeneas's Pure-IR JSON export.
//!
//! Consumes the JSON produced by `bin/aeneas -dump-pure-ir
//! post-s2p:<dest>` (see `src/pure/PureJson.ml`). The AST is hand-
//! written and mirrors `Pure.ml` end-to-end. Starting at
//! [`SUPPORTED_FMT_VERSION`] = 2 the schema carries source spans +
//! Charon attribute info on every decl, loop, and `Meta` expression.

pub mod ast;
pub mod parser;

pub use ast::*;
pub use parser::{parse, ParseError};

/// The schema version this parser accepts. Bump on the OCaml side
/// when the on-disk shape changes; the parser will reject mismatched
/// versions explicitly via [`ParseError::UnsupportedVersion`].
pub const SUPPORTED_FMT_VERSION: u32 = 2;
