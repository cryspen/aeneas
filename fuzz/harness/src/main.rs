//! CLI entry point for the Aeneas fuzzing harness.
//!
//! Subcommands:
//!   * `run`          — full campaign: sample -> mutate -> pack -> pipeline ->
//!                      oracles -> auto-bisect failures -> triage/dedupe -> log
//!   * `one`          — single crate through the pipeline, print the verdict
//!   * `minimize`     — bisect + statement-reduce a failing input
//!   * `list-findings`— print the findings DB
//!
//! Progress goes to stderr; structured results go to the JSONL campaign log.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use serde::Serialize;

use aeneas_fuzz::bisect;
use aeneas_fuzz::config::TargetConfig;
use aeneas_fuzz::corpus::{self, Corpus, PackInput, Provenance};
use aeneas_fuzz::gen;
use aeneas_fuzz::mutate;
use aeneas_fuzz::oracle::{RejectClass, Verdict};
use aeneas_fuzz::pipeline::{CrateResult, Pipeline, PipelineOpts};
use aeneas_fuzz::semdiff::{self, SemdiffOpts};
use aeneas_fuzz::triage::{self, FindingsDb, TriageInput, TriageOutcome, DEFAULT_TOLERANCE};

#[derive(Parser)]
#[command(name = "aeneas-fuzz", about = "Phase-1 fuzzer for the Aeneas translator")]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Run a full fuzzing campaign.
    Run(RunArgs),
    /// Run a single `.rs` file through the pipeline and print the verdict.
    One(OneArgs),
    /// Bisect + statement-reduce a failing `.rs` file.
    Minimize(MinimizeArgs),
    /// List the findings DB.
    ListFindings(ListArgs),
    /// Generate borrow-weighted functions (open or closed) and print/write them.
    Gen(GenArgs),
    /// Run the phase-2 semantic-differential oracle (native vs Lean) on a closed
    /// `test_*` crate (generated or given). FORK-ONLY, slow: gated behind this
    /// subcommand, never in the default campaign.
    Semdiff(SemdiffArgs),
}

#[derive(Parser)]
struct RunArgs {
    #[arg(long)]
    target: PathBuf,
    #[arg(long, default_value_t = 10)]
    rounds: usize,
    #[arg(long, default_value_t = 100)]
    pack_size: usize,
    #[arg(long, default_value_t = 0)]
    seed: u64,
    #[arg(long, default_value_t = 3)]
    mutate_depth: usize,
    /// Run the O3 lean-elab oracle (slow; requires lean_backend_dir).
    #[arg(long)]
    lean_elab: bool,
    /// Also run standalone borrow-check.
    #[arg(long)]
    borrowck: bool,
    /// Seed corpus dirs (repeatable). Default: tests/src.
    #[arg(long = "seed-dir")]
    seed_dirs: Vec<PathBuf>,
    /// Add N generator-produced borrow-heavy "open" functions to the corpus pool
    /// (deterministic from --seed). 0 = disabled.
    #[arg(long, default_value_t = 0)]
    gen_count: usize,
    /// Use ONLY generated functions (skip the seed corpus). Requires --gen-count.
    #[arg(long)]
    gen_only: bool,
    #[arg(long, default_value = "work")]
    work: PathBuf,
    #[arg(long, default_value = "findings")]
    findings: PathBuf,
    #[arg(long)]
    run_id: Option<String>,
    /// Statement-reduction budget per finding.
    #[arg(long, default_value_t = 60)]
    reduce_budget: usize,
    /// CI mode: derive the seed from GITHUB_RUN_ID/ATTEMPT (logged), write a run
    /// summary, and exit with code 3 iff NEW findings were recorded this run.
    #[arg(long)]
    ci: bool,
    /// Wall-clock budget in minutes. When set, rounds run until the budget
    /// elapses (checked between rounds), ignoring --rounds.
    #[arg(long)]
    time_budget: Option<u64>,
    /// Where to write the machine-readable run summary JSON.
    /// Default: <work>/<run-id>/summary.json.
    #[arg(long)]
    summary_out: Option<PathBuf>,
    /// Where to write a short Markdown summary (for $GITHUB_STEP_SUMMARY).
    #[arg(long)]
    md_summary_out: Option<PathBuf>,
}

#[derive(Parser)]
struct OneArgs {
    #[arg(long)]
    target: PathBuf,
    #[arg(long)]
    input: PathBuf,
    #[arg(long, default_value = "work")]
    work: PathBuf,
    #[arg(long, default_value = "findings")]
    findings: PathBuf,
    /// Use the slow `checks_flags` instead of `translate_flags`.
    #[arg(long)]
    checks: bool,
    #[arg(long)]
    borrowck: bool,
}

#[derive(Parser)]
struct MinimizeArgs {
    #[arg(long)]
    target: PathBuf,
    #[arg(long)]
    input: PathBuf,
    #[arg(long, default_value = "work")]
    work: PathBuf,
    #[arg(long, default_value = "findings")]
    findings: PathBuf,
    #[arg(long, default_value_t = 120)]
    budget: usize,
}

#[derive(Parser)]
struct ListArgs {
    #[arg(long, default_value = "findings")]
    findings: PathBuf,
}

#[derive(Parser)]
struct GenArgs {
    /// "open" (borrow-param functions) or "closed" (niladic test_* fns).
    #[arg(long, default_value = "closed")]
    mode: String,
    #[arg(long, default_value_t = 100)]
    count: usize,
    #[arg(long, default_value_t = 0)]
    seed: u64,
    /// Write the generated crate here (default: stdout).
    #[arg(long)]
    out: Option<PathBuf>,
    /// Also run the rustc validity gate and report the yield fraction.
    #[arg(long)]
    check: bool,
}

#[derive(Parser)]
struct SemdiffArgs {
    /// Target config (FORK: supplies charon + aeneas commands + env).
    #[arg(long)]
    target: PathBuf,
    /// A closed `test_*` crate to run. Mutually exclusive with --gen-count.
    #[arg(long)]
    input: Option<PathBuf>,
    /// Generate a closed crate of N test_* fns instead of reading --input.
    #[arg(long, default_value_t = 0)]
    gen_count: usize,
    #[arg(long, default_value_t = 0)]
    seed: u64,
    /// Where to write the generated crate (default: <work>/semdiff/gen.rs).
    #[arg(long)]
    gen_out: Option<PathBuf>,
    /// The fuzz/semdiff dir (auto-detected among fuzz/semdiff, ../semdiff, semdiff).
    #[arg(long)]
    semdiff_dir: Option<PathBuf>,
    #[arg(long, default_value = "work")]
    work: PathBuf,
    /// Findings dir for MISMATCH repros (auto-detected like semdiff_dir).
    #[arg(long)]
    findings: Option<PathBuf>,
    /// Also flag error-kind disagreements (MISMATCH_KIND).
    #[arg(long)]
    strict: bool,
    /// Per-stage timeout in seconds (lean step gets max(this, 300)).
    #[arg(long, default_value_t = 300)]
    stage_timeout: u64,
}

fn main() {
    match real_main() {
        Ok(code) => std::process::exit(code),
        Err(e) => {
            eprintln!("error: {e:#}");
            std::process::exit(1);
        }
    }
}

/// Returns the process exit code. `run --ci` returns 3 when NEW findings were
/// recorded; every other path returns 0 on success (errors surface as `Err`,
/// mapped to exit 1 by `main`).
fn real_main() -> Result<i32> {
    let cli = Cli::parse();
    match cli.cmd {
        Cmd::Run(a) => cmd_run(a),
        Cmd::One(a) => cmd_one(a).map(|_| 0),
        Cmd::Minimize(a) => cmd_minimize(a).map(|_| 0),
        Cmd::ListFindings(a) => cmd_list(a).map(|_| 0),
        Cmd::Gen(a) => cmd_gen(a),
        Cmd::Semdiff(a) => cmd_semdiff(a),
    }
}

/// Resolve a directory by trying candidate locations relative to the cwd; return
/// the first that exists, else the first candidate (so a clear error surfaces).
fn resolve_dir(explicit: Option<PathBuf>, candidates: &[&str]) -> PathBuf {
    if let Some(p) = explicit {
        return p;
    }
    for c in candidates {
        let p = PathBuf::from(c);
        if p.exists() {
            return p;
        }
    }
    PathBuf::from(candidates[0])
}

// ---------------------------------------------------------------------------
// gen
// ---------------------------------------------------------------------------

fn cmd_gen(a: GenArgs) -> Result<i32> {
    let source = match a.mode.as_str() {
        "closed" => {
            let c = gen::gen_closed_crate(a.seed, a.count);
            eprintln!("[gen] closed crate: {} test_* fns (seed {})", c.test_names.len(), a.seed);
            c.source
        }
        "open" => {
            // One crate holding all N open functions (each with its own support).
            let units = gen::gen_open_units(a.seed, a.count);
            eprintln!("[gen] open: {} extractable functions (seed {})", units.len(), a.seed);
            let inputs: Vec<PackInput> = units
                .into_iter()
                .map(|u| {
                    let provenance = u.provenance();
                    PackInput { unit: u, provenance }
                })
                .collect();
            corpus::pack(&inputs, "gen").source
        }
        other => anyhow::bail!("unknown --mode {other:?} (use open|closed)"),
    };

    if a.check {
        // Measure per-function yield for open mode; whole-crate gate for closed.
        match a.mode.as_str() {
            "open" => {
                let y = gen::measure_open_yield(a.seed, a.count);
                eprintln!(
                    "[gen] rustc-yield (open, per-fn): {}/{} = {:.1}%",
                    y.accepted,
                    y.generated,
                    y.fraction() * 100.0
                );
            }
            _ => {
                let ok = gen::rustc_accepts(&source);
                eprintln!("[gen] rustc-gate (closed crate): {}", if ok { "ACCEPT" } else { "REJECT" });
            }
        }
    }

    match a.out {
        Some(p) => {
            if let Some(parent) = p.parent() {
                std::fs::create_dir_all(parent)?;
            }
            std::fs::write(&p, &source)?;
            eprintln!("[gen] wrote {}", p.display());
        }
        None => print!("{source}"),
    }
    Ok(0)
}

// ---------------------------------------------------------------------------
// semdiff
// ---------------------------------------------------------------------------

fn cmd_semdiff(a: SemdiffArgs) -> Result<i32> {
    let cfg = TargetConfig::load(&a.target)?;
    let semdiff_dir = resolve_dir(a.semdiff_dir, &["fuzz/semdiff", "../semdiff", "semdiff"]);
    let findings_dir = resolve_dir(a.findings, &["fuzz/findings", "../findings", "findings"]);
    anyhow::ensure!(
        semdiff_dir.join("check.sh").exists(),
        "semdiff dir {} has no check.sh (pass --semdiff-dir)",
        semdiff_dir.display()
    );

    // Resolve the source crate: --input or generate one.
    let work = a.work.join("semdiff");
    std::fs::create_dir_all(&work)?;
    let src_path = match (&a.input, a.gen_count) {
        (Some(p), 0) => p.clone(),
        (None, n) if n > 0 => {
            let c = gen::gen_closed_crate(a.seed, n);
            let out = a
                .gen_out
                .clone()
                .unwrap_or_else(|| work.join(format!("gen-s{}-n{}.rs", a.seed, n)));
            if let Some(parent) = out.parent() {
                std::fs::create_dir_all(parent)?;
            }
            std::fs::write(&out, &c.source)?;
            eprintln!(
                "[semdiff] generated closed crate: {} test_* fns -> {}",
                c.test_names.len(),
                out.display()
            );
            out
        }
        (Some(_), _) => anyhow::bail!("pass either --input or --gen-count, not both"),
        (None, _) => anyhow::bail!("pass --input <crate.rs> or --gen-count N"),
    };

    let opts = SemdiffOpts {
        semdiff_dir: semdiff_dir.clone(),
        work_dir: work.clone(),
        findings_dir: findings_dir.clone(),
        strict: a.strict,
        stage_timeout_secs: a.stage_timeout,
    };
    eprintln!(
        "[semdiff] target={} src={} strict={}",
        cfg.name,
        src_path.display(),
        a.strict
    );
    eprintln!("[semdiff] semdiff-dir={} findings={}", semdiff_dir.display(), findings_dir.display());

    let report = semdiff::run_crate(&src_path, &cfg, &opts)?;

    // --- report ---
    println!("=== semdiff report (target {}) ===", cfg.name);
    println!("timings_ms: {:?}", report.timings_ms);
    if !report.complete {
        println!("INCOMPLETE: {}", report.note);
        eprintln!("[semdiff] incomplete: {}", report.note);
        return Ok(0);
    }
    println!("verdicts: {}", report.summary());
    let match_ = report.count("MATCH");
    let mismatch = report.count("MISMATCH");
    let mismatch_kind = report.count("MISMATCH_KIND");
    let inconclusive = report.count("LEAN_INCONCLUSIVE")
        + report.count("INCONCLUSIVE_DIV");
    println!(
        "  MATCH={match_} MISMATCH={mismatch} MISMATCH_KIND={mismatch_kind} INCONCLUSIVE={inconclusive}"
    );
    if !report.note.is_empty() {
        println!("  note: {}", report.note);
    }

    if report.mismatches.is_empty() {
        println!("no semantic divergence (no MISMATCH).");
        return Ok(0);
    }

    // Flag loudly.
    eprintln!("\n########################################################");
    eprintln!("# SEMDIFF: {} MISMATCH(es) — CANDIDATE MISCOMPILATION #", report.mismatches.len());
    eprintln!("########################################################");
    for (m, dir) in report.mismatches.iter().zip(report.repro_dirs.iter()) {
        println!(
            "  MISMATCH {}: native={} lean={}  -> {}",
            m.name,
            m.native_str(),
            m.lean_str(),
            dir.display()
        );
        eprintln!(
            "  [MISMATCH] {} native={} lean={} repro={}",
            m.name,
            m.native_str(),
            m.lean_str(),
            dir.display()
        );
    }
    eprintln!("VERIFY BY HAND before claiming a bug (re-run native + Lean, inspect the .lean).");
    // Exit 4 signals a semantic divergence candidate (distinct from the crash
    // campaign's exit 3), so a CI wrapper can treat it specially.
    Ok(4)
}

fn load_units_from_file(input: &Path) -> Result<Vec<PackInput>> {
    let text = std::fs::read_to_string(input)
        .with_context(|| format!("reading input {}", input.display()))?;
    let units = corpus::units_from_source(&text, input)?;
    anyhow::ensure!(
        !units.is_empty(),
        "no extractable free functions in {}",
        input.display()
    );
    Ok(units
        .into_iter()
        .map(|u| {
            let provenance = u.provenance();
            PackInput { unit: u, provenance }
        })
        .collect())
}

fn db_path(findings_dir: &Path) -> PathBuf {
    findings_dir.join("db.json")
}

// ---------------------------------------------------------------------------
// one
// ---------------------------------------------------------------------------

fn cmd_one(a: OneArgs) -> Result<()> {
    let cfg = TargetConfig::load(&a.target)?;
    let inputs = load_units_from_file(&a.input)?;
    let pipeline = Pipeline::new(&cfg, a.work.clone(), "one".to_string());
    let opts = PipelineOpts {
        use_checks: a.checks,
        run_borrowck: a.borrowck,
        ..Default::default()
    };
    let crate_id = "single";
    let (res, _pack) = pipeline.run_pack(&inputs, crate_id, &opts)?;
    print_crate_summary(&res);

    if let Some(Verdict::Crash { fingerprint }) = &res.verdict {
        let db = FindingsDb::load(&db_path(&a.findings));
        match db.matching(fingerprint, DEFAULT_TOLERANCE) {
            Some(i) => {
                let f = &db.findings[i];
                println!(
                    "dedup: KNOWN finding {} ({}), issue {}",
                    f.id,
                    format_status(f.status),
                    f.issue_ref.clone().unwrap_or_else(|| "-".into())
                );
            }
            None => println!("dedup: NEW fingerprint (no DB match within +/-{DEFAULT_TOLERANCE})"),
        }
    }
    Ok(())
}

fn format_status(s: triage::Status) -> &'static str {
    match s {
        triage::Status::New => "new",
        triage::Status::Known => "known",
        triage::Status::Filed => "filed",
        triage::Status::ConfirmedNew => "confirmed-new",
        triage::Status::Duplicate => "duplicate",
        triage::Status::ExpectedReject => "expected-reject",
        triage::Status::Invalid => "invalid",
    }
}

fn print_crate_summary(res: &CrateResult) {
    println!("crate: {}", res.crate_id);
    println!("  gate_ok={} rounds={}", res.gate_ok, res.gate_rounds);
    println!(
        "  functions kept={} dropped={}",
        res.functions.len(),
        res.dropped.len()
    );
    println!("  charon_ok={}", res.charon_ok);
    match &res.verdict {
        Some(v) => println!("  verdict: {}", v.label()),
        None => println!("  verdict: <not reached>"),
    }
    if let Some(v) = &res.borrowck {
        println!("  borrowck: {}", v.label());
    }
    if let Some(ok) = res.lean_elab_ok {
        println!("  lean-elab: {}", if ok { "ok" } else { "FAILED" });
    }
    if let Some(Verdict::Crash { fingerprint }) = &res.verdict {
        println!(
            "  fingerprint: {} {}:{}  msg=\"{}\"",
            fingerprint.error_class.as_str(),
            fingerprint.file,
            fingerprint.line,
            fingerprint.message
        );
        if let Some(tf) = &fingerprint.top_frame {
            println!("  top-frame: {tf}");
        }
    }
    println!("  timings_ms: {:?}", res.timings_ms);
}

// ---------------------------------------------------------------------------
// list-findings
// ---------------------------------------------------------------------------

fn cmd_list(a: ListArgs) -> Result<()> {
    let db = FindingsDb::load(&db_path(&a.findings));
    print!("{}", triage::format_listing(&db));
    Ok(())
}

// ---------------------------------------------------------------------------
// minimize
// ---------------------------------------------------------------------------

fn cmd_minimize(a: MinimizeArgs) -> Result<()> {
    let cfg = TargetConfig::load(&a.target)?;
    let inputs = load_units_from_file(&a.input)?;
    let pipeline = Pipeline::new(&cfg, a.work.clone(), "minimize".to_string());
    let fast = PipelineOpts::default();

    // Establish the failing fingerprint on the fast path.
    let (res, _pack) = pipeline.run_pack(&inputs, "seed", &fast)?;
    let target = match &res.verdict {
        Some(Verdict::Crash { fingerprint }) => fingerprint.clone(),
        other => {
            eprintln!("input does not crash on the fast path (verdict: {other:?}); nothing to minimize");
            print_crate_summary(&res);
            return Ok(());
        }
    };
    eprintln!(
        "[minimize] target fingerprint: {} {}:{}",
        target.error_class.as_str(),
        target.file,
        target.line
    );

    let (min_source, notes) =
        minimize_to_source(&pipeline, &inputs, &target, a.budget, &fast, &cfg)?;
    println!("{min_source}");
    eprintln!("[minimize] {notes}");
    Ok(())
}

/// Bisect to a minimal culprit set, reduce a single culprit, and render source.
fn minimize_to_source(
    pipeline: &Pipeline,
    inputs: &[PackInput],
    target: &aeneas_fuzz::oracle::Fingerprint,
    budget: usize,
    fast: &PipelineOpts,
    cfg: &TargetConfig,
) -> Result<(String, String)> {
    let minimal = bisect::bisect_functions(pipeline, inputs, target, DEFAULT_TOLERANCE, fast)?;
    eprintln!("[minimize] bisected to {} function(s)", minimal.len());

    if minimal.len() == 1 {
        let base: Vec<PackInput> = minimal.iter().map(|&i| inputs[i].clone()).collect();
        let reduced =
            bisect::reduce_culprit(pipeline, &base, 0, target, DEFAULT_TOLERANCE, budget, fast)?;
        let src = bisect::render_min_source(&base[0], &reduced);

        // Confirmation pass with checks (verify path), per target config.
        let mut confirm_note = String::from("checks-confirm: skipped");
        if !cfg.checks_flags.is_empty() {
            let mut trial = base[0].clone();
            trial.unit.func = reduced.clone();
            let checks_opts = PipelineOpts {
                use_checks: true,
                ..Default::default()
            };
            if let Ok((cres, _)) = pipeline.run_pack(std::slice::from_ref(&trial), "confirm", &checks_opts) {
                confirm_note = format!("checks-confirm verdict: {}",
                    cres.verdict.as_ref().map(|v| v.label()).unwrap_or_else(|| "<none>".into()));
            }
        }
        Ok((src, confirm_note))
    } else {
        // Multiple culprits needed: emit the packed minimal subset as-is.
        let subset: Vec<PackInput> = minimal.iter().map(|&i| inputs[i].clone()).collect();
        let pack = corpus::pack(&subset, "min");
        Ok((
            pack.source,
            format!("needs {} functions together; not statement-reduced", minimal.len()),
        ))
    }
}

// ---------------------------------------------------------------------------
// run (campaign)
// ---------------------------------------------------------------------------

/// What `handle_finding` did with an interesting verdict.
enum FindingRecord {
    /// Crash deduped against the DB (known bug / already filed).
    KnownCrash { id: String },
    /// Brand-new crash: a repro dir was emitted (unless bisect/triage failed).
    NewCrash {
        id: String,
        repro_dir: Option<PathBuf>,
    },
    /// Suspicious reject (logged, not filed as a crash finding in phase 1).
    Suspicious,
    /// Nothing actionable.
    Nothing,
}

/// One aggregated crash fingerprint seen during the run.
#[derive(Serialize)]
struct FingerprintEntry {
    error_class: String,
    file: String,
    line: u32,
    message: String,
    known: bool,
    finding_id: Option<String>,
    count: usize,
}

/// Running tallies for a campaign, feeding the summary + exit code.
#[derive(Default)]
struct RunStats {
    rounds: usize,
    wall_time_secs: u64,
    successes: usize,
    known_crashes: usize,
    new_findings: usize,
    expected_rejects: usize,
    suspicious_rejects: usize,
    timeouts: usize,
    charon_fail: usize,
    gate_fail: usize,
    functions_translated: usize,
    functions_dropped: usize,
    fingerprints: Vec<FingerprintEntry>,
    new_finding_dirs: Vec<String>,
}

impl RunStats {
    /// Record a crash fingerprint, aggregating by (class, file, line).
    fn record_fp(
        &mut self,
        fp: &aeneas_fuzz::oracle::Fingerprint,
        known: bool,
        id: Option<String>,
    ) {
        for e in &mut self.fingerprints {
            if e.error_class == fp.error_class.as_str() && e.file == fp.file && e.line == fp.line {
                e.count += 1;
                return;
            }
        }
        self.fingerprints.push(FingerprintEntry {
            error_class: fp.error_class.as_str().to_string(),
            file: fp.file.clone(),
            line: fp.line,
            message: fp.message.clone(),
            known,
            finding_id: id,
            count: 1,
        });
    }
}

#[derive(Serialize)]
struct RunCounts {
    successes: usize,
    known_crashes: usize,
    new_findings: usize,
    expected_rejects: usize,
    suspicious_rejects: usize,
    timeouts: usize,
    charon_fail: usize,
    gate_fail: usize,
}

/// The machine-readable run summary (written as JSON; also rendered to Markdown).
#[derive(Serialize)]
struct RunSummary {
    schema_version: u32,
    target: String,
    ci: bool,
    seed: u64,
    run_id: String,
    github_run_id: Option<String>,
    github_run_attempt: Option<String>,
    wall_time_secs: u64,
    rounds: usize,
    pack_size: usize,
    mutate_depth: usize,
    corpus_units_note: String,
    seed_dirs: Vec<String>,
    functions_translated: usize,
    functions_dropped: usize,
    counts: RunCounts,
    fingerprints: Vec<FingerprintEntry>,
    new_finding_dirs: Vec<String>,
    result_line: String,
}

impl RunSummary {
    #[allow(clippy::too_many_arguments)]
    fn build(
        a: &RunArgs,
        cfg: &TargetConfig,
        seed: u64,
        run_id: &str,
        gh_run_id: &Option<String>,
        gh_attempt: &Option<String>,
        seed_dirs: &[PathBuf],
        stats: &RunStats,
        result_line: &str,
    ) -> RunSummary {
        RunSummary {
            schema_version: 1,
            target: cfg.name.clone(),
            ci: a.ci,
            seed,
            run_id: run_id.to_string(),
            github_run_id: gh_run_id.clone(),
            github_run_attempt: gh_attempt.clone(),
            wall_time_secs: stats.wall_time_secs,
            rounds: stats.rounds,
            pack_size: a.pack_size,
            mutate_depth: a.mutate_depth,
            corpus_units_note: "see campaign.jsonl for per-round detail".to_string(),
            seed_dirs: seed_dirs.iter().map(|p| p.display().to_string()).collect(),
            functions_translated: stats.functions_translated,
            functions_dropped: stats.functions_dropped,
            counts: RunCounts {
                successes: stats.successes,
                known_crashes: stats.known_crashes,
                new_findings: stats.new_findings,
                expected_rejects: stats.expected_rejects,
                suspicious_rejects: stats.suspicious_rejects,
                timeouts: stats.timeouts,
                charon_fail: stats.charon_fail,
                gate_fail: stats.gate_fail,
            },
            // Copy the fingerprint entries (RunStats owns the originals).
            fingerprints: stats
                .fingerprints
                .iter()
                .map(|e| FingerprintEntry {
                    error_class: e.error_class.clone(),
                    file: e.file.clone(),
                    line: e.line,
                    message: e.message.clone(),
                    known: e.known,
                    finding_id: e.finding_id.clone(),
                    count: e.count,
                })
                .collect(),
            new_finding_dirs: stats.new_finding_dirs.clone(),
            result_line: result_line.to_string(),
        }
    }

    /// A short Markdown block suitable for `$GITHUB_STEP_SUMMARY`.
    fn to_markdown(&self) -> String {
        let mut md = String::new();
        md.push_str(&format!("## Aeneas fuzz — target `{}`\n\n", self.target));
        let verdict = if self.counts.new_findings > 0 {
            format!("**❌ {}**", self.result_line)
        } else {
            format!("**✅ {}**", self.result_line)
        };
        md.push_str(&verdict);
        md.push_str("\n\n");
        md.push_str(&format!(
            "- seed: `{}` (reproduce with `run --seed {}`)\n",
            self.seed, self.seed
        ));
        md.push_str(&format!(
            "- wall time: {}s, {} round(s), pack size {}\n",
            self.wall_time_secs, self.rounds, self.pack_size
        ));
        md.push_str(&format!(
            "- functions translated: {} (dropped {})\n",
            self.functions_translated, self.functions_dropped
        ));
        md.push_str(&format!(
            "- timeouts: {}, suspicious rejects: {}, charon/gate fails: {}/{}\n\n",
            self.counts.timeouts,
            self.counts.suspicious_rejects,
            self.counts.charon_fail,
            self.counts.gate_fail
        ));
        if self.fingerprints.is_empty() {
            md.push_str("_No crash fingerprints this run._\n");
        } else {
            md.push_str("| fingerprint | site | count | status |\n");
            md.push_str("|---|---|---|---|\n");
            for e in &self.fingerprints {
                let status = if e.known {
                    format!("known {}", e.finding_id.as_deref().unwrap_or("-"))
                } else {
                    format!("**NEW** {}", e.finding_id.as_deref().unwrap_or("-"))
                };
                md.push_str(&format!(
                    "| {} | {}:{} | {} | {} |\n",
                    e.error_class, e.file, e.line, e.count, status
                ));
            }
        }
        if !self.new_finding_dirs.is_empty() {
            md.push_str("\n### New finding repro dirs\n\n");
            for d in &self.new_finding_dirs {
                md.push_str(&format!("- `{d}`\n"));
            }
        }
        md
    }
}

/// Derive the effective CI seed. When `GITHUB_RUN_ID` is present it is combined
/// with `GITHUB_RUN_ATTEMPT` into a stable u64 (so re-runs of the same job get a
/// distinct-but-reproducible seed); otherwise the provided `--seed` is used.
fn derive_ci_seed(provided: u64) -> (u64, Option<String>, Option<String>) {
    let run_id = std::env::var("GITHUB_RUN_ID").ok().filter(|s| !s.is_empty());
    let attempt = std::env::var("GITHUB_RUN_ATTEMPT").ok().filter(|s| !s.is_empty());
    let seed = match &run_id {
        Some(rid) => {
            let base = rid.parse::<u64>().unwrap_or_else(|_| fnv1a(rid));
            let att = attempt
                .as_deref()
                .and_then(|a| a.parse::<u64>().ok())
                .unwrap_or(1);
            base.wrapping_mul(0x100000001b3).wrapping_add(att)
        }
        None => provided,
    };
    (seed, run_id, attempt)
}

/// FNV-1a hash for non-numeric run ids.
fn fnv1a(s: &str) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in s.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

fn cmd_run(a: RunArgs) -> Result<i32> {
    let cfg = TargetConfig::load(&a.target)?;
    let seed_dirs = if a.seed_dirs.is_empty() {
        vec![PathBuf::from("tests/src")]
    } else {
        a.seed_dirs.clone()
    };

    if a.gen_only {
        anyhow::ensure!(a.gen_count > 0, "--gen-only requires --gen-count N");
    }

    // Build the corpus: seed dirs (unless --gen-only) plus, when --gen-count>0,
    // a deterministic pool of generated borrow-heavy "open" functions.
    let mut units = if a.gen_only {
        Vec::new()
    } else {
        eprintln!("[run] loading corpus from {:?}", seed_dirs);
        Corpus::load(&seed_dirs)?.units
    };
    if a.gen_count > 0 {
        let gen_units = gen::gen_open_units(a.seed, a.gen_count);
        eprintln!(
            "[run] generator: +{} open functions (requested {}, seed {})",
            gen_units.len(),
            a.gen_count,
            a.seed
        );
        units.extend(gen_units);
    }
    let corpus = Corpus::from_units(units);
    anyhow::ensure!(
        !corpus.is_empty(),
        "corpus is empty; check --seed-dir / --gen-count"
    );
    eprintln!("[run] corpus: {} units", corpus.len());

    // --- effective seed (CI-reproducible) ---
    let (seed, gh_run_id, gh_attempt) = if a.ci {
        derive_ci_seed(a.seed)
    } else {
        (a.seed, None, None)
    };

    let run_id = a.run_id.clone().unwrap_or_else(|| {
        if a.ci {
            format!("ci-{seed}")
        } else {
            format!("run-s{seed}")
        }
    });

    if a.ci {
        eprintln!("========================================================");
        eprintln!("[ci] target        : {}", cfg.name);
        eprintln!("[ci] EFFECTIVE SEED: {seed}");
        eprintln!(
            "[ci]   GITHUB_RUN_ID={} GITHUB_RUN_ATTEMPT={}",
            gh_run_id.as_deref().unwrap_or("<none>"),
            gh_attempt.as_deref().unwrap_or("<none>")
        );
        eprintln!(
            "[ci]   reproduce: cargo run --release --manifest-path fuzz/harness/Cargo.toml -- \\"
        );
        eprintln!(
            "[ci]     run --target {} --seed {seed} --rounds {} --pack-size {} --seed-dir {}",
            a.target.display(),
            a.rounds,
            a.pack_size,
            seed_dirs
                .iter()
                .map(|p| p.display().to_string())
                .collect::<Vec<_>>()
                .join(" --seed-dir ")
        );
        eprintln!("========================================================");
    }

    let pipeline = Pipeline::new(&cfg, a.work.clone(), run_id.clone());

    // campaign log
    let log_dir = a.work.join(&run_id);
    std::fs::create_dir_all(&log_dir)?;
    let log_path = log_dir.join("campaign.jsonl");
    let mut log = std::io::BufWriter::new(
        std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&log_path)?,
    );
    eprintln!("[run] campaign log: {}", log_path.display());

    let db_file = db_path(&a.findings);
    let mut db = FindingsDb::load(&db_file);

    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let fast = PipelineOpts {
        use_checks: false,
        run_borrowck: a.borrowck,
        run_lean_elab: a.lean_elab,
        ..Default::default()
    };

    let start = Instant::now();
    let budget = a.time_budget.map(|m| Duration::from_secs(m.saturating_mul(60)));
    if let Some(b) = &budget {
        eprintln!("[run] time budget: {} min ({}s)", a.time_budget.unwrap(), b.as_secs());
    }

    let mut stats = RunStats::default();
    let mut n_interesting = 0usize;
    let mut round = 0usize;
    loop {
        // Stop conditions: budget elapsed (if set) else round cap.
        match &budget {
            Some(b) => {
                if start.elapsed() >= *b {
                    break;
                }
            }
            None => {
                if round >= a.rounds {
                    break;
                }
            }
        }

        let inputs = sample_and_mutate(&corpus, &mut rng, a.pack_size, a.mutate_depth);
        let crate_id = format!("r{round:04}");
        eprintln!(
            "[run] round {round}: packing {} functions (elapsed {}s)",
            inputs.len(),
            start.elapsed().as_secs()
        );
        let (res, _pack) = pipeline.run_pack(&inputs, &crate_id, &fast)?;
        writeln!(log, "{}", serde_json::to_string(&res)?)?;
        log.flush()?;

        stats.functions_translated += res.functions.len();
        stats.functions_dropped += res.dropped.len();

        let verdict_label = res
            .verdict
            .as_ref()
            .map(|v| v.label())
            .unwrap_or_else(|| "<charon/gate>".into());
        eprintln!(
            "[run] round {round}: gate_ok={} kept={} verdict={}",
            res.gate_ok,
            res.functions.len(),
            verdict_label
        );

        // Tally the non-crash verdicts (crashes are tallied via handle_finding
        // so we can split known vs new).
        match &res.verdict {
            Some(Verdict::Success) => stats.successes += 1,
            Some(Verdict::Timeout) => stats.timeouts += 1,
            Some(Verdict::Reject {
                classification: RejectClass::Expected,
                ..
            }) => stats.expected_rejects += 1,
            Some(Verdict::Reject {
                classification: RejectClass::Suspicious,
                ..
            }) => stats.suspicious_rejects += 1,
            Some(Verdict::Crash { .. }) => {}
            None => {
                if !res.gate_ok {
                    stats.gate_fail += 1;
                } else if !res.charon_ok {
                    stats.charon_fail += 1;
                }
            }
        }

        // Auto-triage interesting outcomes.
        if let Some(v) = &res.verdict {
            if v.is_interesting() {
                n_interesting += 1;
                match handle_finding(
                    &pipeline,
                    &inputs,
                    &res,
                    &cfg,
                    &mut db,
                    &a.findings,
                    a.reduce_budget,
                ) {
                    Ok(record) => {
                        if let Some(fp) = v.fingerprint() {
                            let (known, id) = match &record {
                                FindingRecord::KnownCrash { id } => {
                                    stats.known_crashes += 1;
                                    (true, Some(id.clone()))
                                }
                                FindingRecord::NewCrash { id, repro_dir } => {
                                    stats.new_findings += 1;
                                    if let Some(d) = repro_dir {
                                        stats.new_finding_dirs.push(d.to_string_lossy().into_owned());
                                    }
                                    (false, Some(id.clone()))
                                }
                                _ => (false, None),
                            };
                            stats.record_fp(fp, known, id);
                        }
                    }
                    Err(e) => eprintln!("[run] triage error: {e:#}"),
                }
                db.save(&db_file)?;
            }
        }

        round += 1;
    }
    stats.rounds = round;
    stats.wall_time_secs = start.elapsed().as_secs();

    let result_line = format!(
        "CI RESULT: {} new findings ({} known crashes, {} expected rejects, {} successes)",
        stats.new_findings, stats.known_crashes, stats.expected_rejects, stats.successes
    );
    println!("{result_line}");
    eprintln!(
        "[run] done: {} round(s), {} interesting outcome(s). findings DB: {}",
        round,
        n_interesting,
        db_file.display()
    );

    // --- run summary (JSON + optional Markdown) ---
    let summary = RunSummary::build(&a, &cfg, seed, &run_id, &gh_run_id, &gh_attempt, &seed_dirs, &stats, &result_line);
    let summary_path = a
        .summary_out
        .clone()
        .unwrap_or_else(|| log_dir.join("summary.json"));
    if let Some(parent) = summary_path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    std::fs::write(&summary_path, serde_json::to_string_pretty(&summary)?)
        .with_context(|| format!("writing summary {}", summary_path.display()))?;
    eprintln!("[run] summary: {}", summary_path.display());

    if let Some(md_path) = &a.md_summary_out {
        if let Some(parent) = md_path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(md_path, summary.to_markdown())
            .with_context(|| format!("writing md summary {}", md_path.display()))?;
        eprintln!("[run] md summary: {}", md_path.display());
    }

    // --- exit-code contract ---
    // In CI mode: exit 3 iff NEW (non-deduped, non-expected-reject) findings were
    // recorded. Known bugs (F4/F6, anything in db.json) and expected rejects do
    // NOT fail the job. Non-CI runs always exit 0.
    if a.ci && stats.new_findings > 0 {
        eprintln!(
            "[ci] {} NEW finding(s) recorded -> exit 3 (see {})",
            stats.new_findings,
            a.findings.display()
        );
        Ok(3)
    } else {
        Ok(0)
    }
}

/// Sample `k` units and apply a mutation chain to each.
fn sample_and_mutate(
    corpus: &Corpus,
    rng: &mut ChaCha8Rng,
    k: usize,
    mutate_depth: usize,
) -> Vec<PackInput> {
    let n = corpus.len();
    let indices = sample_indices(rng, n, k);
    let mut inputs = Vec::new();
    for idx in indices {
        let unit = &corpus.units[idx];
        let mut prov = unit.provenance();
        let (func, chain) = if mutate_depth > 0 {
            mutate::mutate_with_depth_range(&unit.func, rng, 1, mutate_depth)
        } else {
            (unit.func.clone(), Vec::new())
        };
        prov.mutations = chain;
        let mut u = unit.clone();
        u.func = func;
        inputs.push(PackInput {
            unit: u,
            provenance: prov,
        });
    }
    inputs
}

/// Sample `k` indices from `0..n`. Without replacement when `k <= n`.
fn sample_indices(rng: &mut ChaCha8Rng, n: usize, k: usize) -> Vec<usize> {
    if n == 0 {
        return Vec::new();
    }
    if k >= n {
        // all, possibly padded with random picks (with replacement)
        let mut v: Vec<usize> = (0..n).collect();
        while v.len() < k {
            v.push(rng.random_range(0..n));
        }
        return v;
    }
    // partial Fisher-Yates
    let mut pool: Vec<usize> = (0..n).collect();
    let mut out = Vec::with_capacity(k);
    for i in 0..k {
        let j = i + rng.random_range(0..(n - i));
        pool.swap(i, j);
        out.push(pool[i]);
    }
    out
}

/// Bisect + reduce + triage one interesting crate result.
fn handle_finding(
    pipeline: &Pipeline,
    inputs: &[PackInput],
    res: &CrateResult,
    cfg: &TargetConfig,
    db: &mut FindingsDb,
    findings_dir: &Path,
    reduce_budget: usize,
) -> Result<FindingRecord> {
    let verdict = res.verdict.as_ref().unwrap();
    let observed_output = format!(
        "=== stdout ===\n{}\n=== stderr ===\n{}\n",
        res.aeneas_stdout, res.aeneas_stderr
    );

    match verdict {
        Verdict::Crash { fingerprint } => {
            // Dedup fast-path: if already known, just record and stop (avoid the
            // expensive bisect for known bugs).
            if let Some(i) = db.matching(fingerprint, DEFAULT_TOLERANCE) {
                db.findings[i]
                    .targets_reproducing
                    .insert(cfg.name.clone(), fingerprint.line);
                let id = db.findings[i].id.clone();
                eprintln!(
                    "[triage] crash {} -> KNOWN {} ({})",
                    verdict.label(),
                    id,
                    db.findings[i].issue_ref.clone().unwrap_or_else(|| "-".into())
                );
                return Ok(FindingRecord::KnownCrash { id });
            }

            // New crash: bisect + reduce for a clean repro.
            eprintln!("[triage] NEW crash {}: bisecting...", verdict.label());
            let fast = PipelineOpts::default();
            let (min_source, notes) = match bisect::bisect_functions(
                pipeline,
                inputs,
                fingerprint,
                DEFAULT_TOLERANCE,
                &fast,
            ) {
                Ok(minimal) if minimal.len() == 1 => {
                    let base: Vec<PackInput> =
                        minimal.iter().map(|&i| inputs[i].clone()).collect();
                    let reduced = bisect::reduce_culprit(
                        pipeline,
                        &base,
                        0,
                        fingerprint,
                        DEFAULT_TOLERANCE,
                        reduce_budget,
                        &fast,
                    )?;
                    let src = bisect::render_min_source(&base[0], &reduced);
                    (src, provenance_note(&base[0].provenance, verdict))
                }
                Ok(minimal) => {
                    let subset: Vec<PackInput> =
                        minimal.iter().map(|&i| inputs[i].clone()).collect();
                    let pack = corpus::pack(&subset, "min");
                    (
                        pack.source,
                        format!("needs {} functions together", minimal.len()),
                    )
                }
                Err(e) => {
                    eprintln!("[triage] bisect failed: {e:#}; emitting full crate");
                    let pack = corpus::pack(inputs, "min");
                    (pack.source, "bisect failed; full crate".to_string())
                }
            };

            let input = TriageInput {
                fingerprint,
                target_name: &cfg.name,
                cfg,
                min_source: &min_source,
                observed_output: &observed_output,
                notes: &notes,
            };
            match triage::triage(db, findings_dir, &input, DEFAULT_TOLERANCE)? {
                TriageOutcome::Known { id } => {
                    eprintln!("[triage] deduped to {id}");
                    Ok(FindingRecord::KnownCrash { id })
                }
                TriageOutcome::New { id, repro_dir } => {
                    eprintln!("[triage] NEW finding {id} -> {}", repro_dir.display());
                    Ok(FindingRecord::NewCrash {
                        id,
                        repro_dir: Some(repro_dir),
                    })
                }
            }
        }
        Verdict::Reject {
            classification: RejectClass::Suspicious,
            message,
            ..
        } => {
            eprintln!("[triage] suspicious reject: {message}");
            // Suspicious rejects are logged (potential completeness bug) but not
            // auto-filed as crash findings in phase 1.
            Ok(FindingRecord::Suspicious)
        }
        _ => Ok(FindingRecord::Nothing),
    }
}

fn provenance_note(prov: &Provenance, verdict: &Verdict) -> String {
    format!(
        "provenance: seed_file={} orig={} mutations=[{}]\noracle: {}\n",
        prov.seed_file,
        prov.orig_name,
        prov.mutations.join(", "),
        verdict.label()
    )
}
