//! Sweep mode: run the harness over every `.cert.json` in a
//! directory, share `cargo test` output across fixtures, aggregate
//! into one fleet-wide report.

use anyhow::{Context, Result};
use serde::Serialize;
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use crate::cert::Cert;
use crate::gates;
use crate::manifest::Manifest;
use crate::report::{GateAggregate, Report, Status};

#[derive(Debug, Serialize)]
pub struct SweepReport {
    pub sweep_dir: String,
    pub fixtures: Vec<FixtureSummary>,
    pub aggregate: SweepAggregate,
}

#[derive(Debug, Serialize)]
pub struct FixtureSummary {
    pub fixture: String,
    pub crate_name: String,
    pub decls: usize,
    /// Per-gate per-decl tally (`pass=N, divergent=N, ...`).
    pub by_gate: BTreeMap<String, GateAggregate>,
    /// Per-gate fixture-level verdict — reduces decls down to a
    /// single "fixture passes / diverges / mismatches / skips" label.
    pub fixture_status: BTreeMap<String, String>,
    /// Full per-decl report. Surfaced in the JSON for tools that
    /// want the detail; omitted from the Markdown's top-level table.
    pub full: Report,
}

#[derive(Debug, Serialize, Default)]
pub struct SweepAggregate {
    pub fixtures: usize,
    pub total_decls: usize,
    /// Per-gate per-decl totals across the entire sweep.
    pub per_decl_by_gate: BTreeMap<String, GateAggregate>,
    /// Per-gate fixture-level totals (a fixture is counted once per gate).
    pub per_fixture_by_gate: BTreeMap<String, FixtureLevelTally>,
}

#[derive(Debug, Serialize, Default, Clone)]
pub struct FixtureLevelTally {
    pub pass: usize,
    pub divergent: usize,
    pub mismatch: usize,
    pub skip: usize,
    pub mixed: usize,
}

pub fn run_sweep(
    sweep_dir: &Path,
    gates: &[String],
    manifest: &Manifest,
    aeneas: &Path,
    aeneas_check: &Path,
    source_crate: Option<&Path>,
) -> Result<SweepReport> {
    let cert_paths = enumerate_certs(sweep_dir)?;
    eprintln!(
        "[meta-harness] sweep: {} fixtures under {}",
        cert_paths.len(),
        sweep_dir.display()
    );

    // Share `cargo test` across fixtures if g_rust is active.
    let test_run = if gates.iter().any(|g| g == "g_rust") {
        let src = source_crate.ok_or_else(|| {
            anyhow::anyhow!("--sweep with g_rust requires --source-crate")
        })?;
        eprintln!("[meta-harness] sweep: running cargo test once for g_rust...");
        let run = gates::g_rust::run_cargo_test(src)?;
        eprintln!(
            "[meta-harness] sweep: cargo test parsed {} test results{}",
            run.results.len(),
            run.failure.as_deref().map(|f| format!(" ({f})")).unwrap_or_default()
        );
        Some(run)
    } else {
        None
    };

    // Two-pass to compute global test ownership: first load every
    // cert, then for each test find the (fixture, decl) pair whose
    // matching stem is longest across the entire fleet. Without this,
    // a short-stem fallback like `incr` would let `arrays::incr` and
    // `incr_cert::incr` (in different certs) each claim the same
    // `incr_matches_model`, inflating the g_rust pass count.
    let certs: Vec<Cert> = cert_paths
        .iter()
        .map(|p| {
            Cert::load(p).with_context(|| format!("loading {}", p.display()))
        })
        .collect::<Result<Vec<_>>>()?;

    let fixture_names: Vec<String> = cert_paths
        .iter()
        .map(|p| fixture_name_from_path(p))
        .collect();
    let excluded_per_fixture: Vec<std::collections::HashSet<usize>> =
        if let Some(run) = &test_run {
            compute_per_fixture_exclusions(&certs, &fixture_names, run)
        } else {
            vec![std::collections::HashSet::new(); certs.len()]
        };

    let mut fixtures = Vec::with_capacity(cert_paths.len());
    let mut aggregate = SweepAggregate::default();

    for (idx, cert_path) in cert_paths.iter().enumerate() {
        let fixture_name = fixture_name_from_path(cert_path);
        eprintln!(
            "[meta-harness] [{:>3}/{}] {}",
            idx + 1,
            cert_paths.len(),
            fixture_name
        );
        let cert = &certs[idx];
        let mut report = Report::new(cert);

        for gate in gates {
            match gate.as_str() {
                "" | "none" => continue,
                "g_byte" => gates::g_byte::run(
                    cert,
                    cert_path,
                    aeneas,
                    aeneas_check,
                    manifest,
                    &mut report,
                )?,
                "g_rust" => {
                    let run = test_run.as_ref().expect("g_rust active → test_run computed");
                    gates::g_rust::run_with_test_run_filtered(
                        cert,
                        run,
                        &excluded_per_fixture[idx],
                        manifest,
                        &mut report,
                    )?;
                }
                other => anyhow::bail!("unknown gate: {other}"),
            }
        }

        let summary = summarise(&fixture_name, &report);

        // Roll the summary into the aggregate.
        aggregate.fixtures += 1;
        aggregate.total_decls += summary.decls;
        for (g, ga) in &summary.by_gate {
            let entry = aggregate.per_decl_by_gate.entry(g.clone()).or_default();
            entry.pass += ga.pass;
            entry.divergent += ga.divergent;
            entry.mismatch += ga.mismatch;
            entry.skip += ga.skip;
            entry.not_run += ga.not_run;
            entry.fail += ga.fail;
        }
        for (g, verdict) in &summary.fixture_status {
            let fl = aggregate.per_fixture_by_gate.entry(g.clone()).or_default();
            match verdict.as_str() {
                "pass" => fl.pass += 1,
                "divergent" => fl.divergent += 1,
                "mismatch" => fl.mismatch += 1,
                "skip" => fl.skip += 1,
                "mixed" => fl.mixed += 1,
                _ => {}
            }
        }

        fixtures.push(summary);
    }

    Ok(SweepReport {
        sweep_dir: sweep_dir.display().to_string(),
        fixtures,
        aggregate,
    })
}

/// Resolve test→fixture ownership globally: for each test, find the
/// (fixture, decl) whose matching stem is longest. Return, per
/// fixture, the set of test indices NOT owned by that fixture — those
/// are skipped during the local g_rust run.
fn compute_per_fixture_exclusions(
    certs: &[Cert],
    fixture_names: &[String],
    test_run: &gates::g_rust::CargoTestRun,
) -> Vec<std::collections::HashSet<usize>> {
    let n = certs.len();
    let mut excluded: Vec<std::collections::HashSet<usize>> =
        vec![std::collections::HashSet::new(); n];
    if test_run.failure.is_some() {
        return excluded;
    }
    // Pre-compute stems per fixture.
    let fixture_stems: Vec<Vec<Vec<String>>> = certs
        .iter()
        .map(|c| c.decls.iter().map(|d| gates::g_rust::test_stems_for_decl(&d.path)).collect())
        .collect();

    for (test_idx, tr) in test_run.results.iter().enumerate() {
        // Collect ALL (fixture, stem-len) matches, then resolve:
        // - unique longest → that fixture owns the test
        // - tied longest → ambiguous (no fixture owns; every fixture
        //   excludes the test so all candidate decls fall to
        //   skip(no_test_coverage)). Avoid silent wrong attribution.
        let mut best_len: usize = 0;
        let mut owners: Vec<usize> = Vec::new();
        for (fx_idx, decl_stems) in fixture_stems.iter().enumerate() {
            let mut fixture_best: Option<usize> = None;
            for stems in decl_stems {
                for s in stems {
                    if gates::g_rust::test_matches_stem(&tr.name, s) {
                        let len = s.len();
                        if fixture_best.map(|l| len > l).unwrap_or(true) {
                            fixture_best = Some(len);
                        }
                        break;
                    }
                }
            }
            if let Some(len) = fixture_best {
                use std::cmp::Ordering::*;
                match len.cmp(&best_len) {
                    Greater => {
                        best_len = len;
                        owners.clear();
                        owners.push(fx_idx);
                    }
                    Equal if best_len > 0 => owners.push(fx_idx),
                    _ => {}
                }
            }
        }
        match owners.len() {
            1 => {
                let owner_fx = owners[0];
                for (i, set) in excluded.iter_mut().enumerate() {
                    if i != owner_fx {
                        set.insert(test_idx);
                    }
                }
            }
            _ => {
                // Ambiguous (or no match): exclude from every fixture.
                for set in excluded.iter_mut() {
                    set.insert(test_idx);
                }
                if owners.len() > 1 {
                    let fx_names: Vec<&str> =
                        owners.iter().map(|i| fixture_names[*i].as_str()).collect();
                    eprintln!(
                        "[meta-harness] sweep: ambiguous test `{}` — tied stem length across fixtures: {} (excluded; add manifest mapping to resolve)",
                        tr.name,
                        fx_names.join(", ")
                    );
                }
            }
        }
    }
    excluded
}

/// Sort certs alphabetically so the sweep output is deterministic.
fn enumerate_certs(dir: &Path) -> Result<Vec<PathBuf>> {
    let mut out = Vec::new();
    for entry in fs::read_dir(dir)
        .with_context(|| format!("reading sweep dir {}", dir.display()))?
    {
        let entry = entry?;
        let p = entry.path();
        if p.is_file() && p.to_string_lossy().ends_with(".cert.json") {
            out.push(p);
        }
    }
    out.sort();
    if out.is_empty() {
        anyhow::bail!("no *.cert.json files under {}", dir.display());
    }
    Ok(out)
}

fn fixture_name_from_path(p: &Path) -> String {
    p.file_name()
        .and_then(|f| f.to_str())
        .map(|s| s.trim_end_matches(".cert.json").to_string())
        .unwrap_or_else(|| p.display().to_string())
}

fn summarise(fixture: &str, report: &Report) -> FixtureSummary {
    let mut by_gate: BTreeMap<String, GateAggregate> = BTreeMap::new();
    for d in &report.decls {
        for (g, outcome) in &d.gates {
            let agg = by_gate.entry(g.clone()).or_default();
            match outcome.status {
                Status::Pass => agg.pass += 1,
                Status::Divergent => agg.divergent += 1,
                Status::Mismatch => agg.mismatch += 1,
                Status::Skip => agg.skip += 1,
                Status::NotRun => agg.not_run += 1,
                Status::Fail => agg.fail += 1,
            }
        }
    }
    let mut fixture_status = BTreeMap::new();
    for (g, agg) in &by_gate {
        fixture_status.insert(g.clone(), fixture_verdict(agg));
    }
    FixtureSummary {
        fixture: fixture.to_string(),
        crate_name: report.crate_name.clone(),
        decls: report.aggregate.decls,
        by_gate,
        fixture_status,
        full: report.clone(),
    }
}

/// Reduce a per-decl gate aggregate to one of:
/// - `pass`      — every decl pass
/// - `mismatch`  — at least one mismatch / fail
/// - `divergent` — at least one divergent, no mismatch
/// - `skip`      — every decl skipped (e.g. emit failed)
/// - `mixed`     — some pass, some skip, none divergent or mismatch
fn fixture_verdict(agg: &GateAggregate) -> String {
    if agg.mismatch > 0 || agg.fail > 0 {
        return "mismatch".to_string();
    }
    if agg.divergent > 0 {
        return "divergent".to_string();
    }
    let total = agg.pass + agg.skip + agg.not_run;
    if total == 0 {
        return "skip".to_string();
    }
    if agg.pass == 0 {
        return "skip".to_string();
    }
    if agg.skip == 0 && agg.not_run == 0 {
        return "pass".to_string();
    }
    "mixed".to_string()
}

impl SweepReport {
    pub fn write_json(&self, path: &Path) -> Result<()> {
        let text = serde_json::to_string_pretty(self)?;
        fs::write(path, text)?;
        Ok(())
    }

    pub fn write_markdown(&self, path: &Path) -> Result<()> {
        let mut s = String::new();
        s.push_str(&format!("# meta-harness sweep — `{}`\n\n", self.sweep_dir));
        s.push_str(&format!(
            "- Fixtures: **{}**\n- Total decls: **{}**\n\n",
            self.aggregate.fixtures, self.aggregate.total_decls
        ));

        // Fleet-wide per-decl tally per gate.
        if !self.aggregate.per_decl_by_gate.is_empty() {
            s.push_str("## Fleet aggregate (per decl)\n\n");
            s.push_str("| Gate | pass | divergent | mismatch | skip | not-run | fail |\n");
            s.push_str("|---|---|---|---|---|---|---|\n");
            for (gate, agg) in &self.aggregate.per_decl_by_gate {
                s.push_str(&format!(
                    "| {gate} | {} | {} | {} | {} | {} | {} |\n",
                    agg.pass, agg.divergent, agg.mismatch, agg.skip, agg.not_run, agg.fail
                ));
            }
            s.push('\n');
        }

        // Fleet-wide per-fixture tally per gate.
        if !self.aggregate.per_fixture_by_gate.is_empty() {
            s.push_str("## Fleet aggregate (per fixture)\n\n");
            s.push_str("| Gate | pass | divergent | mismatch | skip | mixed |\n");
            s.push_str("|---|---|---|---|---|---|\n");
            for (gate, fl) in &self.aggregate.per_fixture_by_gate {
                s.push_str(&format!(
                    "| {gate} | {} | {} | {} | {} | {} |\n",
                    fl.pass, fl.divergent, fl.mismatch, fl.skip, fl.mixed
                ));
            }
            s.push('\n');
        }

        // Per-fixture status grid.
        let gate_names: Vec<&String> = self.aggregate.per_decl_by_gate.keys().collect();
        s.push_str("## Per-fixture status\n\n");
        s.push_str(&format!(
            "| Fixture | Decls | {} |\n",
            gate_names
                .iter()
                .map(|g| format!("{g} (status / pass / div / mis / skip)"))
                .collect::<Vec<_>>()
                .join(" | ")
        ));
        s.push_str("|---|---|");
        for _ in &gate_names {
            s.push_str("---|");
        }
        s.push('\n');
        for fx in &self.fixtures {
            let cells: Vec<String> = gate_names
                .iter()
                .map(|g| {
                    let status = fx.fixture_status.get(*g).cloned().unwrap_or_else(|| "-".into());
                    let a = fx.by_gate.get(*g).cloned().unwrap_or_default();
                    format!("{} / {} / {} / {} / {}", status, a.pass, a.divergent, a.mismatch, a.skip)
                })
                .collect();
            s.push_str(&format!(
                "| `{}` | {} | {} |\n",
                fx.fixture,
                fx.decls,
                cells.join(" | ")
            ));
        }

        fs::write(path, s)?;
        Ok(())
    }

    pub fn exit_code(&self) -> i32 {
        for agg in self.aggregate.per_decl_by_gate.values() {
            if agg.mismatch > 0 || agg.fail > 0 {
                return 1;
            }
        }
        0
    }
}
