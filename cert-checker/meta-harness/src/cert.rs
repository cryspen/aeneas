//! Cert (`.cert.json`) loader + decl enumeration.
//!
//! The cert carries the authoritative decl list for a crate: every
//! function, global, type, trait, and trait-impl decl that aeneas's
//! cert pipeline knows about, keyed by Charon's stable name path.

use anyhow::{Context, Result};
use serde::Deserialize;
use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize)]
pub enum DeclKind {
    Function,
    Global,
    Type,
    Trait,
    TraitImpl,
}

impl DeclKind {
    pub fn as_str(self) -> &'static str {
        match self {
            DeclKind::Function => "fn",
            DeclKind::Global => "global",
            DeclKind::Type => "type",
            DeclKind::Trait => "trait",
            DeclKind::TraitImpl => "trait_impl",
        }
    }
}

#[derive(Debug, Clone, serde::Serialize)]
pub struct Decl {
    pub path: String,
    pub kind: DeclKind,
    pub id: u64,
}

#[derive(Debug, Clone)]
pub struct Cert {
    pub crate_hash: String,
    pub decls: Vec<Decl>,
    /// Names that have at least one event in the top-level `functions`
    /// trace — i.e. functions for which a cert proof was emitted.
    pub functions_with_events: BTreeSet<String>,
}

impl Cert {
    pub fn load(path: &Path) -> Result<Self> {
        let text = fs::read_to_string(path)
            .with_context(|| format!("reading {}", path.display()))?;
        let raw: RawCert = serde_json::from_str(&text)
            .with_context(|| format!("parsing {} as cert.json", path.display()))?;

        let mut decls = Vec::new();
        let prog = raw.llbc_program;
        push_decls(&prog.type_decls, DeclKind::Type, &mut decls);
        push_decls(&prog.fun_decls, DeclKind::Function, &mut decls);
        push_decls(&prog.global_decls, DeclKind::Global, &mut decls);
        push_decls(&prog.trait_decls, DeclKind::Trait, &mut decls);
        push_decls(&prog.trait_impls, DeclKind::TraitImpl, &mut decls);

        let functions_with_events = raw
            .functions
            .into_iter()
            .map(|f| f.fn_name)
            .collect();

        Ok(Cert {
            crate_hash: raw.crate_hash,
            decls,
            functions_with_events,
        })
    }

    /// Best-effort crate name guess from the first decl path's first
    /// segment. Returns "unknown" if no decls exist.
    pub fn crate_name(&self) -> String {
        self.decls
            .first()
            .and_then(|d| d.path.split("::").next())
            .unwrap_or("unknown")
            .to_string()
    }
}

fn push_decls(items: &Option<Vec<RawDecl>>, kind: DeclKind, out: &mut Vec<Decl>) {
    let Some(items) = items else { return };
    for item in items {
        out.push(Decl {
            path: item.item_meta.name.clone(),
            kind,
            id: item.id,
        });
    }
}

#[derive(Deserialize)]
struct RawCert {
    crate_hash: String,
    functions: Vec<RawFnEvents>,
    llbc_program: RawProgram,
}

#[derive(Deserialize)]
struct RawFnEvents {
    fn_name: String,
    #[serde(default)]
    #[allow(dead_code)]
    fn_id: u64,
}

#[derive(Deserialize)]
struct RawProgram {
    #[serde(default)]
    type_decls: Option<Vec<RawDecl>>,
    #[serde(default)]
    fun_decls: Option<Vec<RawDecl>>,
    #[serde(default)]
    global_decls: Option<Vec<RawDecl>>,
    #[serde(default)]
    trait_decls: Option<Vec<RawDecl>>,
    #[serde(default)]
    trait_impls: Option<Vec<RawDecl>>,
}

#[derive(Deserialize)]
struct RawDecl {
    id: u64,
    item_meta: RawItemMeta,
}

#[derive(Deserialize)]
struct RawItemMeta {
    name: String,
}
