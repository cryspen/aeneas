//! G_rust gate: source-tests-as-oracle. Stub for Phase A; implemented
//! in Phase D.

use anyhow::Result;
use std::path::Path;

use crate::cert::Cert;
use crate::manifest::Manifest;
use crate::report::{GateOutcome, Report};

const GATE: &str = "g_rust";

pub fn run(
    cert: &Cert,
    _cert_path: &Path,
    _aeneas_check: &Path,
    _source_crate: &Path,
    _manifest: &Manifest,
    report: &mut Report,
) -> Result<()> {
    for decl in &cert.decls {
        report.record(&decl.path, GATE, GateOutcome::skip("g_rust not yet implemented (Phase D)"));
    }
    Ok(())
}
