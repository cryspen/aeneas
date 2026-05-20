//! Report structures + JSON/Markdown rendering.

use anyhow::Result;
use serde::Serialize;
use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use crate::cert::{Cert, Decl, DeclKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Status {
    Pass,
    Divergent,
    Mismatch,
    Skip,
    NotRun,
    Fail,
}

impl Status {
    pub fn as_str(self) -> &'static str {
        match self {
            Status::Pass => "pass",
            Status::Divergent => "divergent",
            Status::Mismatch => "mismatch",
            Status::Skip => "skip",
            Status::NotRun => "not-run",
            Status::Fail => "fail",
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct GateOutcome {
    pub status: Status,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub evidence: Option<String>,
}

impl GateOutcome {
    pub fn pass() -> Self {
        Self { status: Status::Pass, reason: None, evidence: None }
    }
    pub fn skip(reason: impl Into<String>) -> Self {
        Self { status: Status::Skip, reason: Some(reason.into()), evidence: None }
    }
    pub fn divergent(reason: impl Into<String>) -> Self {
        Self { status: Status::Divergent, reason: Some(reason.into()), evidence: None }
    }
    pub fn mismatch(reason: impl Into<String>) -> Self {
        Self { status: Status::Mismatch, reason: Some(reason.into()), evidence: None }
    }
    pub fn fail(reason: impl Into<String>) -> Self {
        Self { status: Status::Fail, reason: Some(reason.into()), evidence: None }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct DeclEntry {
    pub path: String,
    pub kind: &'static str,
    pub id: u64,
    pub gates: BTreeMap<String, GateOutcome>,
}

impl DeclEntry {
    fn from_decl(d: &Decl) -> Self {
        Self {
            path: d.path.clone(),
            kind: d.kind.as_str(),
            id: d.id,
            gates: BTreeMap::new(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Default)]
pub struct Aggregate {
    pub decls: usize,
    pub by_kind: BTreeMap<String, usize>,
    pub by_gate: BTreeMap<String, GateAggregate>,
}

#[derive(Debug, Clone, Serialize, Default)]
pub struct GateAggregate {
    pub pass: usize,
    pub divergent: usize,
    pub mismatch: usize,
    pub skip: usize,
    pub not_run: usize,
    pub fail: usize,
}

impl GateAggregate {
    fn tally(&mut self, status: Status) {
        match status {
            Status::Pass => self.pass += 1,
            Status::Divergent => self.divergent += 1,
            Status::Mismatch => self.mismatch += 1,
            Status::Skip => self.skip += 1,
            Status::NotRun => self.not_run += 1,
            Status::Fail => self.fail += 1,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct Report {
    pub crate_name: String,
    pub crate_hash: String,
    pub aggregate: Aggregate,
    pub decls: Vec<DeclEntry>,
}

impl Report {
    pub fn new(cert: &Cert) -> Self {
        let mut aggregate = Aggregate::default();
        aggregate.decls = cert.decls.len();
        for d in &cert.decls {
            *aggregate.by_kind.entry(d.kind.as_str().to_string()).or_default() += 1;
        }
        let decls = cert.decls.iter().map(DeclEntry::from_decl).collect();
        Self {
            crate_name: cert.crate_name(),
            crate_hash: cert.crate_hash.clone(),
            aggregate,
            decls,
        }
    }

    pub fn record(&mut self, decl_path: &str, gate: &str, outcome: GateOutcome) {
        let status = outcome.status;
        if let Some(entry) = self.decls.iter_mut().find(|d| d.path == decl_path) {
            entry.gates.insert(gate.to_string(), outcome);
        }
        self.aggregate
            .by_gate
            .entry(gate.to_string())
            .or_default()
            .tally(status);
    }

    pub fn write_json(&self, path: &Path) -> Result<()> {
        let text = serde_json::to_string_pretty(self)?;
        fs::write(path, text)?;
        Ok(())
    }

    pub fn write_markdown(&self, path: &Path) -> Result<()> {
        let mut s = String::new();
        s.push_str(&format!("# meta-harness report — `{}`\n\n", self.crate_name));
        s.push_str(&format!("- Crate hash: `{}`\n", self.crate_hash));
        s.push_str(&format!("- Total decls: **{}**\n", self.aggregate.decls));
        for kind in [
            DeclKind::Function.as_str(),
            DeclKind::Global.as_str(),
            DeclKind::Type.as_str(),
            DeclKind::Trait.as_str(),
            DeclKind::TraitImpl.as_str(),
        ] {
            if let Some(n) = self.aggregate.by_kind.get(kind) {
                s.push_str(&format!("  - {kind}: {n}\n"));
            }
        }
        s.push('\n');

        if !self.aggregate.by_gate.is_empty() {
            s.push_str("## Gate aggregate\n\n");
            s.push_str("| Gate | pass | divergent | mismatch | skip | not-run | fail |\n");
            s.push_str("|---|---|---|---|---|---|---|\n");
            for (gate, agg) in &self.aggregate.by_gate {
                s.push_str(&format!(
                    "| {gate} | {} | {} | {} | {} | {} | {} |\n",
                    agg.pass, agg.divergent, agg.mismatch, agg.skip, agg.not_run, agg.fail
                ));
            }
            s.push('\n');
        }

        s.push_str("## Per-decl detail\n\n");
        s.push_str("<details><summary>Click to expand</summary>\n\n");
        s.push_str("| Decl | Kind | Gate | Status | Reason |\n");
        s.push_str("|---|---|---|---|---|\n");
        for d in &self.decls {
            if d.gates.is_empty() {
                s.push_str(&format!("| `{}` | {} | — | not-run | — |\n", d.path, d.kind));
            } else {
                for (gate, outcome) in &d.gates {
                    s.push_str(&format!(
                        "| `{}` | {} | {} | {} | {} |\n",
                        d.path,
                        d.kind,
                        gate,
                        outcome.status.as_str(),
                        outcome.reason.as_deref().unwrap_or("")
                    ));
                }
            }
        }
        s.push_str("\n</details>\n");

        fs::write(path, s)?;
        Ok(())
    }

    pub fn exit_code(&self) -> i32 {
        for agg in self.aggregate.by_gate.values() {
            if agg.mismatch > 0 || agg.fail > 0 {
                return 1;
            }
        }
        0
    }
}
