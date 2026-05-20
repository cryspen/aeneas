use crate::ast::TranslatedCrate;
use crate::SUPPORTED_FMT_VERSION;

#[derive(Debug, thiserror::Error)]
pub enum ParseError {
    #[error("JSON parse: {0}")]
    Json(#[from] serde_json::Error),
    #[error("unsupported pure_ir_fmt_version: got {got}, supported {supported}")]
    UnsupportedVersion { got: u32, supported: u32 },
}

/// Parse a Pure-IR JSON dump. Verifies `pure_ir_fmt_version` matches
/// [`SUPPORTED_FMT_VERSION`] before deserializing the rest of the
/// envelope.
pub fn parse(src: &str) -> Result<TranslatedCrate, ParseError> {
    let v: serde_json::Value = serde_json::from_str(src)?;
    let version = v
        .get("pure_ir_fmt_version")
        .and_then(|x| x.as_u64())
        .unwrap_or(0) as u32;
    if version != SUPPORTED_FMT_VERSION {
        return Err(ParseError::UnsupportedVersion {
            got: version,
            supported: SUPPORTED_FMT_VERSION,
        });
    }
    Ok(serde_json::from_value(v)?)
}
