//! `meta-harness.toml` manifest parser. Phase E will flesh this out;
//! Phase A only needs the loader + lookups.

use anyhow::{Context, Result};
use serde::Deserialize;
use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

#[derive(Debug, Clone, Default, Deserialize)]
pub struct Manifest {
    #[serde(default)]
    pub gates: GateToggles,
    #[serde(default)]
    pub decls: BTreeMap<String, DeclOverride>,
}

#[derive(Debug, Clone, Default, Deserialize)]
pub struct GateToggles {
    #[serde(default)]
    pub g_byte: Option<String>,
    #[serde(default)]
    pub g_rust: Option<String>,
    #[serde(default)]
    pub g_lean: Option<String>,
    #[serde(default)]
    pub g_rfl: Option<String>,
}

#[derive(Debug, Clone, Default, Deserialize)]
pub struct DeclOverride {
    /// G_byte override. e.g. `{ skip = "wrapping_add shim" }` or
    /// `{ divergent = "<reason>" }`.
    #[serde(default)]
    pub g_byte: Option<DeclVerdict>,
    #[serde(default)]
    pub g_rust: Option<DeclVerdict>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
pub enum DeclVerdict {
    Skip { skip: String },
    Divergent { divergent: String },
    Vectors { vectors: String },
}

impl DeclVerdict {
    pub fn reason(&self) -> &str {
        match self {
            DeclVerdict::Skip { skip } => skip,
            DeclVerdict::Divergent { divergent } => divergent,
            DeclVerdict::Vectors { vectors } => vectors,
        }
    }
}

pub fn load(explicit: Option<&Path>, crate_root: Option<&Path>) -> Result<Manifest> {
    let path = if let Some(p) = explicit {
        Some(p.to_path_buf())
    } else if let Some(root) = crate_root {
        let candidate = root.join("meta-harness.toml");
        if candidate.exists() { Some(candidate) } else { None }
    } else {
        None
    };

    let Some(path) = path else {
        return Ok(Manifest::default());
    };
    let text = fs::read_to_string(&path)
        .with_context(|| format!("reading manifest {}", path.display()))?;
    let manifest: Manifest = toml::from_str(&text)
        .with_context(|| format!("parsing manifest {}", path.display()))?;
    Ok(manifest)
}
