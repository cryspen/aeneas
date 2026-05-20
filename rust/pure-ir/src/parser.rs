use crate::ast::TranslatedCrate;
use crate::SUPPORTED_FMT_VERSION;
use serde::Deserialize;

#[derive(Debug, thiserror::Error)]
pub enum ParseError {
    #[error("JSON parse: {0}")]
    Json(#[from] serde_json::Error),
    #[error("unsupported pure_ir_fmt_version: got {got}, supported {supported}")]
    UnsupportedVersion { got: u32, supported: u32 },
}

/// Lightweight envelope check: read just `pure_ir_fmt_version` from
/// the top of the JSON without parsing the full AST. We use a small
/// shim struct + `serde_json::from_str` truncated via
/// `#[serde(deny_unknown_fields = false)]` semantics (the default).
#[derive(Deserialize)]
struct VersionProbe {
    pure_ir_fmt_version: u32,
}

/// Parse a Pure-IR JSON dump. Verifies `pure_ir_fmt_version` matches
/// [`SUPPORTED_FMT_VERSION`] before deserializing the rest of the
/// envelope.
///
/// Some Aeneas fixtures (notably `curve25519`) produce deeply-nested
/// `App` / `Let` chains. We disable `serde_json`'s default 128-level
/// recursion guard and use `serde_stacker` to grow the stack on
/// demand, so the deep nesting deserialises without overflow.
pub fn parse(src: &str) -> Result<TranslatedCrate, ParseError> {
    // First pass: validate the schema version cheaply.
    let probe: VersionProbe = serde_json::from_str(src)?;
    if probe.pure_ir_fmt_version != SUPPORTED_FMT_VERSION {
        return Err(ParseError::UnsupportedVersion {
            got: probe.pure_ir_fmt_version,
            supported: SUPPORTED_FMT_VERSION,
        });
    }
    // Second pass: deserialise the full AST with the recursion limit
    // disabled and a growable stack.
    let mut de = serde_json::Deserializer::from_str(src);
    de.disable_recursion_limit();
    let de = serde_stacker::Deserializer::new(&mut de);
    Ok(TranslatedCrate::deserialize(de)?)
}
