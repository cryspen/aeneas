//! Aeneas meta-harness: project-agnostic differential-testing tool.
//!
//! Reads one of {Cargo crate, .llbc file, .cert.json} and produces a
//! per-decl differential-testing report. See
//! `documentation/plans/meta-harness-contract.md` for the design.

use anyhow::{Context, Result, bail};
use clap::Parser;
use std::path::PathBuf;

mod cert;
mod gates;
mod manifest;
mod report;

use cert::Cert;
use report::Report;

#[derive(Parser, Debug)]
#[command(name = "meta-harness", version, about)]
struct Cli {
    /// Path to a Cargo crate root (containing Cargo.toml). Runs the
    /// full pipeline: charon → aeneas -emit-cert → gates.
    #[arg(long = "crate", value_name = "PATH", conflicts_with_all = ["llbc", "cert"])]
    krate: Option<PathBuf>,

    /// Path to a pre-built .llbc file. Skips charon.
    #[arg(long, conflicts_with_all = ["krate", "cert"])]
    llbc: Option<PathBuf>,

    /// Path to a pre-built .cert.json. Skips charon + emit-cert.
    #[arg(long, conflicts_with_all = ["krate", "llbc"])]
    cert: Option<PathBuf>,

    /// Optional source crate for the G_rust gate.
    #[arg(long)]
    source_crate: Option<PathBuf>,

    /// Gates to run. Comma-separated. Default: g_byte.
    #[arg(long, value_delimiter = ',')]
    gates: Option<Vec<String>>,

    /// Where to write the JSON report.
    #[arg(long, default_value = "report.json")]
    report_json: PathBuf,

    /// Where to write the Markdown report.
    #[arg(long, default_value = "report.md")]
    report_md: PathBuf,

    /// Path to a meta-harness.toml manifest. Default: look in crate root.
    #[arg(long)]
    manifest: Option<PathBuf>,

    /// Path to the aeneas binary (mainline).
    #[arg(long, env = "AENEAS")]
    aeneas: Option<PathBuf>,

    /// Path to the aeneas-check binary.
    #[arg(long, env = "AENEAS_CHECK")]
    aeneas_check: Option<PathBuf>,
}

fn main() {
    match run() {
        Ok(code) => std::process::exit(code),
        Err(e) => {
            eprintln!("[meta-harness] structural error: {e:#}");
            std::process::exit(2);
        }
    }
}

fn run() -> Result<i32> {
    let cli = Cli::parse();
    let cert_path = resolve_cert_input(&cli)?;
    let cert = Cert::load(&cert_path)
        .with_context(|| format!("loading cert {}", cert_path.display()))?;
    let manifest = manifest::load(cli.manifest.as_deref(), cli.krate.as_deref())?;

    let aeneas = resolve_aeneas(&cli)?;
    let aeneas_check = resolve_aeneas_check(&cli)?;

    let mut report = Report::new(&cert);

    let mut active_gates = cli.gates.clone().unwrap_or_else(default_gates);
    // Manifest toggle: a gate marked `"skip"` in `[gates]` is dropped.
    active_gates.retain(|g| match g.as_str() {
        "g_byte" => manifest.gates.g_byte.as_deref() != Some("skip"),
        "g_rust" => manifest.gates.g_rust.as_deref() != Some("skip"),
        "g_lean" => manifest.gates.g_lean.as_deref() != Some("skip"),
        "g_rfl" => manifest.gates.g_rfl.as_deref() != Some("skip"),
        _ => true,
    });
    eprintln!("[meta-harness] decls: {}  gates: {}", cert.decls.len(), active_gates.join(","));

    for gate in &active_gates {
        match gate.as_str() {
            "" | "none" => continue,
            "g_byte" => gates::g_byte::run(
                &cert,
                &cert_path,
                &aeneas,
                &aeneas_check,
                &manifest,
                &mut report,
            )?,
            "g_rust" => {
                let src = cli.source_crate.as_deref().or(cli.krate.as_deref()).ok_or_else(|| {
                    anyhow::anyhow!("g_rust requires --source-crate or --crate")
                })?;
                gates::g_rust::run(
                    &cert,
                    &cert_path,
                    &aeneas_check,
                    src,
                    &manifest,
                    &mut report,
                )?
            }
            other => bail!("unknown gate: {other}"),
        }
    }

    report.write_json(&cli.report_json)?;
    report.write_markdown(&cli.report_md)?;
    eprintln!(
        "[meta-harness] wrote {} and {}",
        cli.report_json.display(),
        cli.report_md.display()
    );

    Ok(report.exit_code())
}

fn default_gates() -> Vec<String> {
    vec!["g_byte".into()]
}

fn resolve_cert_input(cli: &Cli) -> Result<PathBuf> {
    if let Some(p) = &cli.cert {
        return Ok(p.clone());
    }
    if cli.llbc.is_some() {
        bail!(
            "--llbc is not yet wired in. Run `aeneas -emit-cert <llbc>` to \
             produce a `.cert.json`, then pass it with `--cert`."
        );
    }
    if cli.krate.is_some() {
        bail!(
            "--crate is not yet wired in (would drive `charon rustc \
             --preset=aeneas` + `aeneas -emit-cert`). For now, build the \
             cert manually and pass it with `--cert`."
        );
    }
    bail!("one of --crate, --llbc, --cert is required")
}

fn resolve_aeneas(cli: &Cli) -> Result<PathBuf> {
    if let Some(p) = &cli.aeneas {
        return Ok(p.clone());
    }
    let candidates = [
        repo_relative("src/_build/default/main.exe"),
        repo_relative("bin/aeneas"),
    ];
    candidates
        .iter()
        .find(|p| p.is_file())
        .cloned()
        .ok_or_else(|| anyhow::anyhow!("no aeneas binary found; pass --aeneas or set $AENEAS"))
}

fn resolve_aeneas_check(cli: &Cli) -> Result<PathBuf> {
    if let Some(p) = &cli.aeneas_check {
        return Ok(p.clone());
    }
    let cand = repo_relative("aeneas-lean-checker/.lake/build/bin/aeneas-check");
    if cand.is_file() {
        Ok(cand)
    } else {
        bail!(
            "no aeneas-check binary found at {}; pass --aeneas-check or set $AENEAS_CHECK",
            cand.display()
        )
    }
}

/// Best-effort repo root: walk up from cwd looking for `aeneas-lean-checker/`.
fn repo_relative(rel: &str) -> PathBuf {
    let mut cur = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    loop {
        if cur.join("aeneas-lean-checker").is_dir() {
            return cur.join(rel);
        }
        if !cur.pop() {
            return PathBuf::from(rel);
        }
    }
}
