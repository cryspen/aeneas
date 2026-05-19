//! Aeneas meta-harness: project-agnostic differential-testing tool.
//!
//! Reads one of {Cargo crate, .llbc file, .cert.json} and produces a
//! per-decl differential-testing report. See
//! `documentation/plans/meta-harness-contract.md` for the design.

use anyhow::{Context, Result, bail};
use clap::Parser;
use std::path::{Path, PathBuf};

mod cert;
mod gates;
mod generate;
mod manifest;
mod prepare;
mod regen;
mod report;
mod sweep;

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
    #[arg(long, conflicts_with_all = ["krate", "llbc", "sweep"])]
    cert: Option<PathBuf>,

    /// Sweep mode: directory of `*.cert.json` to run gates against.
    /// Produces a fleet-wide report. With g_rust active, `cargo test`
    /// against `--source-crate` runs once and is shared across
    /// fixtures.
    #[arg(long, value_name = "DIR", conflicts_with_all = ["krate", "llbc", "cert"])]
    sweep: Option<PathBuf>,

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

    /// Path to the charon binary. Defaults to $CHARON, then the
    /// project-pinned `/Users/karthik/charon/charon/target/release/charon`,
    /// then PATH-resolved `charon` if neither is set.
    #[arg(long, env = "CHARON")]
    charon: Option<PathBuf>,

    /// Where to land intermediate artefacts when `--crate` runs the
    /// full pipeline. Defaults to a fresh tempdir (auto-cleaned).
    #[arg(long, value_name = "DIR")]
    work_dir: Option<PathBuf>,

    /// Generate-tests mode: walk every `.cert.json` under `--sweep
    /// <dir>` and emit a Rust file with `proptest!` blocks for every
    /// decl whose signature is simple enough (all-scalar args, no
    /// generics, no refs). Skips gate execution.
    #[arg(long, conflicts_with_all = ["gates"])]
    generate_tests: bool,

    /// For --generate-tests: directory holding the fixture sources
    /// (e.g. `tests/src/`). Each `<fixture>.rs` is `#[path]`-imported
    /// by the generated test file.
    #[arg(long, value_name = "DIR")]
    tests_src_dir: Option<PathBuf>,

    /// For --generate-tests: where to write the generated test file.
    #[arg(long, value_name = "PATH", default_value = "diff_auto.rs")]
    tests_out: PathBuf,

    /// For --generate-tests: path to the existing `model.rs`. The
    /// generator emits `// SKIPPED` comments for decls whose model
    /// fn is missing so the user can regen.
    #[arg(long, value_name = "PATH")]
    tests_model_path: Option<PathBuf>,

    /// Regen-models mode: walk every `.cert.json` under `--sweep`,
    /// invoke aeneas-check --rust-model on each, filter the emitted
    /// fns through the same signature filter the test generator
    /// uses, rename `<name>_model` → `<fixture>_<name>_model`, drop
    /// duplicates of `--tests-model-path`'s contents, and append to
    /// the path passed here. After each fixture, runs `cargo check`
    /// against the differential crate; rolls back any fn whose
    /// addition breaks the build.
    #[arg(long, value_name = "PATH", conflicts_with_all = ["gates", "generate_tests"])]
    regen_models: Option<PathBuf>,

    /// For --regen-models: path to the differential crate root (the
    /// directory containing `Cargo.toml`). Defaults to
    /// `tests/lean-checker/differential`.
    #[arg(long, value_name = "PATH")]
    diff_crate: Option<PathBuf>,
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

    if let Some(out_path) = cli.regen_models.as_deref() {
        let dir = cli.sweep.as_deref().ok_or_else(|| {
            anyhow::anyhow!("--regen-models requires --sweep <cert-dir>")
        })?;
        let aeneas_check = resolve_aeneas_check(&cli)?;
        let default_diff = PathBuf::from("tests/lean-checker/differential");
        let diff_crate = cli.diff_crate.as_deref().unwrap_or(&default_diff);
        let default_model = PathBuf::from("tests/lean-checker/differential/src/model.rs");
        let model_path = cli
            .tests_model_path
            .as_deref()
            .unwrap_or(&default_model);
        let summary = regen::run(dir, out_path, &aeneas_check, diff_crate, model_path)?;
        eprintln!(
            "[meta-harness] regen-models: wrote {} ({} kept of {} fns; \
             skipped: sig={} body={} dup={} compile={})",
            out_path.display(),
            summary.fns_kept,
            summary.fns_total,
            summary.skipped_sig,
            summary.skipped_body,
            summary.skipped_duplicate,
            summary.fns_dropped_compile,
        );
        eprintln!(
            "[meta-harness] regen-models: fixtures processed={} failed={}",
            summary.fixtures_processed, summary.fixtures_failed,
        );
        return Ok(0);
    }

    if cli.generate_tests {
        let dir = cli.sweep.as_deref().ok_or_else(|| {
            anyhow::anyhow!("--generate-tests requires --sweep <cert-dir>")
        })?;
        let src = cli.tests_src_dir.as_deref().ok_or_else(|| {
            anyhow::anyhow!("--generate-tests requires --tests-src-dir <fixture-source-dir>")
        })?;
        let default_model = PathBuf::from("tests/lean-checker/differential/src/model.rs");
        let model_path = cli.tests_model_path.as_deref().unwrap_or(&default_model);
        let summary = generate::generate_for_cert_dir(dir, src, model_path, &cli.tests_out)?;
        eprintln!(
            "[meta-harness] generate-tests: wrote {} ({} proptest blocks emitted)",
            cli.tests_out.display(),
            summary.emitted
        );
        eprintln!(
            "[meta-harness] skips: non-public={}  no-body={}  non-simple-sig={}  missing-model={}  missing-source={}",
            summary.skipped_non_public,
            summary.skipped_no_body,
            summary.skipped_signature,
            summary.skipped_missing_model,
            summary.skipped_missing_source,
        );
        return Ok(0);
    }

    let manifest = manifest::load(cli.manifest.as_deref(), cli.krate.as_deref())?;
    let aeneas = resolve_aeneas(&cli)?;
    let aeneas_check = resolve_aeneas_check(&cli)?;

    let mut active_gates = cli.gates.clone().unwrap_or_else(default_gates);
    active_gates.retain(|g| match g.as_str() {
        "g_byte" => manifest.gates.g_byte.as_deref() != Some("skip"),
        "g_rust" => manifest.gates.g_rust.as_deref() != Some("skip"),
        "g_lean" => manifest.gates.g_lean.as_deref() != Some("skip"),
        "g_rfl" => manifest.gates.g_rfl.as_deref() != Some("skip"),
        _ => true,
    });

    // Sweep mode short-circuits the single-cert pipeline.
    if let Some(dir) = &cli.sweep {
        let source = cli.source_crate.as_deref().or(cli.krate.as_deref());
        let sweep_report = sweep::run_sweep(
            dir,
            &active_gates,
            &manifest,
            &aeneas,
            &aeneas_check,
            source,
        )?;
        sweep_report.write_json(&cli.report_json)?;
        sweep_report.write_markdown(&cli.report_md)?;
        eprintln!(
            "[meta-harness] wrote {} and {}",
            cli.report_json.display(),
            cli.report_md.display()
        );
        return Ok(sweep_report.exit_code());
    }

    let prepared = resolve_cert_input(&cli, &aeneas)?;
    let cert_path = prepared.cert_path.clone();
    let cert = Cert::load(&cert_path)
        .with_context(|| format!("loading cert {}", cert_path.display()))?;
    let mut report = Report::new(&cert);

    eprintln!("[meta-harness] decls: {}  gates: {}", cert.decls.len(), active_gates.join(","));

    for gate in &active_gates {
        match gate.as_str() {
            "" | "none" => continue,
            "g_byte" => gates::g_byte::run_with_llbc(
                &cert,
                &cert_path,
                prepared.llbc_path.as_deref(),
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
            "c_lean" => {
                let lean_diff_dir = gates::c_lean::default_lean_diff_dir();
                gates::c_lean::run(
                    &cert,
                    &cert_path,
                    &aeneas_check,
                    &lean_diff_dir,
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

    drop(prepared); // explicit; the TempDir cleans up here.
    Ok(report.exit_code())
}

fn default_gates() -> Vec<String> {
    vec!["g_byte".into()]
}

fn resolve_cert_input(cli: &Cli, aeneas: &Path) -> Result<prepare::Prepared> {
    if let Some(p) = &cli.cert {
        return Ok(prepare::Prepared {
            cert_path: p.clone(),
            llbc_path: None,
            _tmp: None,
        });
    }
    if let Some(p) = &cli.llbc {
        return prepare::from_llbc(p, aeneas, cli.work_dir.as_deref());
    }
    if let Some(p) = &cli.krate {
        let charon = resolve_charon(cli)?;
        return prepare::from_crate(p, &charon, aeneas, cli.work_dir.as_deref());
    }
    bail!("one of --crate, --llbc, --cert is required")
}

fn resolve_charon(cli: &Cli) -> Result<PathBuf> {
    if let Some(p) = &cli.charon {
        return Ok(p.clone());
    }
    let pinned = PathBuf::from("/Users/karthik/charon/charon/target/release/charon");
    if pinned.is_file() {
        return Ok(pinned);
    }
    // Last resort: PATH-resolved `charon`. Likely the wrong version,
    // so warn.
    eprintln!(
        "[meta-harness] warning: no project-pinned charon found at {}; \
         falling back to PATH-resolved `charon`, which may not match \
         aeneas's expected version.",
        pinned.display()
    );
    Ok(PathBuf::from("charon"))
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
