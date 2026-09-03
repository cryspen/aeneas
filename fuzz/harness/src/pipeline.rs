//! The translation pipeline: rustc validity gate -> charon -> aeneas.
//!
//! Process management uses file-redirected stdout/stderr (so large output never
//! deadlocks a pipe) plus `wait-timeout` for hard per-stage timeouts with kill.
//! Work happens under `fuzz/work/<run-id>/<crate-id>/`.

use anyhow::{Context, Result};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};
use wait_timeout::ChildExt;

use crate::config::{substitute, TargetConfig};
use crate::corpus::{self, Pack, PackInput, Provenance};
use crate::oracle::{self, RejectPatterns, Verdict};

/// Raw outcome of running one external process.
#[derive(Clone, Debug, Serialize)]
pub struct ProcOutcome {
    pub cmd: Vec<String>,
    pub exit_code: Option<i32>,
    pub timed_out: bool,
    pub duration_ms: u128,
    #[serde(skip)]
    pub stdout: String,
    #[serde(skip)]
    pub stderr: String,
    /// Short tail of stderr for the log.
    pub stderr_tail: String,
}

fn tail(s: &str, lines: usize) -> String {
    let v: Vec<&str> = s.lines().collect();
    let start = v.len().saturating_sub(lines);
    v[start..].join("\n")
}

/// Run a command with a timeout, redirecting output to files in `cwd`.
pub fn run_cmd(
    argv: &[String],
    env: &BTreeMap<String, String>,
    cwd: &Path,
    timeout: Duration,
    tag: &str,
) -> Result<ProcOutcome> {
    anyhow::ensure!(!argv.is_empty(), "empty argv for {tag}");
    let stdout_path = cwd.join(format!("{tag}.stdout"));
    let stderr_path = cwd.join(format!("{tag}.stderr"));
    let out_file = File::create(&stdout_path)
        .with_context(|| format!("create {}", stdout_path.display()))?;
    let err_file = File::create(&stderr_path)
        .with_context(|| format!("create {}", stderr_path.display()))?;

    let mut cmd = Command::new(&argv[0]);
    cmd.args(&argv[1..])
        .current_dir(cwd)
        .stdin(Stdio::null())
        .stdout(Stdio::from(out_file))
        .stderr(Stdio::from(err_file));
    for (k, v) in env {
        cmd.env(k, v);
    }

    let start = Instant::now();
    let mut child = cmd
        .spawn()
        .with_context(|| format!("spawning {} ({tag})", argv[0]))?;

    let (exit_code, timed_out) = match child.wait_timeout(timeout)? {
        Some(status) => (status.code(), false),
        None => {
            let _ = child.kill();
            let _ = child.wait();
            (None, true)
        }
    };
    let duration_ms = start.elapsed().as_millis();

    let stdout = std::fs::read_to_string(&stdout_path).unwrap_or_default();
    let stderr = std::fs::read_to_string(&stderr_path).unwrap_or_default();
    let stderr_tail = tail(&stderr, 8);

    Ok(ProcOutcome {
        cmd: argv.to_vec(),
        exit_code,
        timed_out,
        duration_ms,
        stdout,
        stderr,
        stderr_tail,
    })
}

/// The result of driving one crate through the pipeline.
#[derive(Clone, Debug, Serialize)]
pub struct CrateResult {
    pub crate_id: String,
    pub workdir: String,
    /// Functions that survived the rustc gate (packed + translated).
    pub functions: Vec<Provenance>,
    /// Functions dropped by the gate (didn't compile / packing conflict).
    pub dropped: Vec<Provenance>,
    pub gate_ok: bool,
    pub gate_rounds: usize,
    pub charon_ok: bool,
    /// The translation verdict (None if we never reached aeneas).
    pub verdict: Option<Verdict>,
    /// Optional borrow-check verdict.
    pub borrowck: Option<Verdict>,
    /// Optional O3 lean-elab result (true = elaborated).
    pub lean_elab_ok: Option<bool>,
    pub timings_ms: BTreeMap<String, u128>,
    /// Aeneas stdout/stderr, retained for triage/repro of interesting outcomes.
    #[serde(skip_serializing_if = "String::is_empty", default)]
    pub aeneas_stdout: String,
    #[serde(skip_serializing_if = "String::is_empty", default)]
    pub aeneas_stderr: String,
}

/// Options for a pipeline run.
pub struct PipelineOpts {
    /// Use the slow `checks_flags` instead of `translate_flags` (verify path).
    pub use_checks: bool,
    /// Also run standalone borrow-check.
    pub run_borrowck: bool,
    /// Run the O3 lean elaboration oracle (requires lean_backend_dir).
    pub run_lean_elab: bool,
    /// Max rustc greedy-drop rounds.
    pub max_gate_rounds: usize,
}

impl Default for PipelineOpts {
    fn default() -> Self {
        PipelineOpts {
            use_checks: false,
            run_borrowck: false,
            run_lean_elab: false,
            max_gate_rounds: 4,
        }
    }
}

/// The pipeline driver, bundling config + work root + reject patterns.
pub struct Pipeline<'a> {
    pub cfg: &'a TargetConfig,
    pub work_root: PathBuf,
    pub run_id: String,
    pub patterns: RejectPatterns,
}

impl<'a> Pipeline<'a> {
    pub fn new(cfg: &'a TargetConfig, work_root: PathBuf, run_id: String) -> Pipeline<'a> {
        // Absolutize the work root. Child processes run with `current_dir` set to
        // the crate dir, and we hand them derived paths (`-o gate.rmeta`, the
        // `.llbc`, the `dest`, charon's `{input}`/`{output}`). If `work_root` is
        // relative those derived paths get resolved *again* against the child's
        // cwd, doubling the prefix (e.g. `work/r0/work/r0/...`) — which only
        // surfaces once a pack compiles cleanly (rustc reaches metadata emit and
        // fails to create its temp dir at the doubled path). Making the root
        // absolute up front keeps every derived path unambiguous.
        let work_root = if work_root.is_absolute() {
            work_root
        } else {
            std::env::current_dir()
                .map(|cwd| cwd.join(&work_root))
                .unwrap_or(work_root)
        };
        Pipeline {
            cfg,
            work_root,
            run_id,
            patterns: RejectPatterns::default_embedded(),
        }
    }

    fn crate_dir(&self, crate_id: &str) -> PathBuf {
        self.work_root.join(&self.run_id).join(crate_id)
    }

    /// Run a set of units (as PackInputs) through the whole pipeline.
    pub fn run_pack(
        &self,
        inputs: &[PackInput],
        crate_id: &str,
        opts: &PipelineOpts,
    ) -> Result<(CrateResult, Pack)> {
        let dir = self.crate_dir(crate_id);
        std::fs::create_dir_all(&dir)
            .with_context(|| format!("create workdir {}", dir.display()))?;
        let mut timings = BTreeMap::new();

        // --- rustc validity gate with greedy drop ---
        // `active` holds ORIGINAL input indices still in play. Each round we
        // pack them, gate with rustc, and (if it fails) drop the functions whose
        // line spans carry errors, then re-pack and retry.
        let mut active: Vec<usize> = (0..inputs.len()).collect();
        let mut dropped: Vec<Provenance> = Vec::new();
        let mut rounds = 0;
        let mut pack: Pack;
        let gate_ok: bool;
        let mut rustc_ms_total = 0u128;

        let rustc_argv = vec![
            "rustc".to_string(),
            "--edition=2021".to_string(),
            "--crate-type=rlib".to_string(),
            "--emit=metadata".to_string(),
            "--error-format=json".to_string(),
            "-o".to_string(),
            dir.join("gate.rmeta").to_string_lossy().into_owned(),
            "lib.rs".to_string(),
        ];

        loop {
            rounds += 1;
            // Snapshot: subset position -> original index.
            let subset_orig = active.clone();
            let subset: Vec<PackInput> =
                subset_orig.iter().map(|&i| inputs[i].clone()).collect();
            pack = corpus::pack(&subset, crate_id);

            // Record units the packer itself dropped (support-item conflict).
            let survived_pos: BTreeSet<usize> =
                pack.functions.iter().map(|f| f.index).collect();
            let mut alive: Vec<usize> = Vec::new();
            for (pos, &orig) in subset_orig.iter().enumerate() {
                if survived_pos.contains(&pos) {
                    alive.push(orig);
                } else {
                    dropped.push(inputs[orig].provenance.clone());
                }
            }
            if alive.is_empty() {
                active = alive;
                gate_ok = false;
                break;
            }

            let lib_path = dir.join("lib.rs");
            std::fs::write(&lib_path, &pack.source)?;

            let outcome = run_cmd(
                &rustc_argv,
                &self.cfg.extra_env,
                &dir,
                Duration::from_secs(self.cfg.timeout_secs.rustc),
                &format!("rustc-r{rounds}"),
            )?;
            rustc_ms_total += outcome.duration_ms;

            if outcome.exit_code == Some(0) {
                active = alive;
                gate_ok = true;
                break;
            }

            if rounds >= opts.max_gate_rounds {
                active = alive;
                gate_ok = false;
                break;
            }

            // Map errors (subset positions) back to original indices and drop.
            let offenders_pos = parse_rustc_offenders(&outcome.stderr, &pack);
            if offenders_pos.is_empty() {
                // Can't attribute the failure to any function; give up.
                active = alive;
                gate_ok = false;
                break;
            }
            let offender_orig: BTreeSet<usize> =
                offenders_pos.iter().map(|&p| subset_orig[p]).collect();
            let mut next_active = Vec::new();
            for &orig in &alive {
                if offender_orig.contains(&orig) {
                    dropped.push(inputs[orig].provenance.clone());
                } else {
                    next_active.push(orig);
                }
            }
            active = next_active;
            if active.is_empty() {
                gate_ok = false;
                break;
            }
        }
        let _ = active;
        timings.insert("rustc_ms".to_string(), rustc_ms_total);

        let surviving: Vec<Provenance> = pack.functions.iter().map(|f| f.provenance.clone()).collect();

        let mut result = CrateResult {
            crate_id: crate_id.to_string(),
            workdir: dir.to_string_lossy().into_owned(),
            functions: surviving,
            dropped,
            gate_ok,
            gate_rounds: rounds,
            charon_ok: false,
            verdict: None,
            borrowck: None,
            lean_elab_ok: None,
            timings_ms: timings,
            aeneas_stdout: String::new(),
            aeneas_stderr: String::new(),
        };

        if !gate_ok || pack.functions.is_empty() {
            return Ok((result, pack));
        }

        // --- charon ---
        let lib_path = dir.join("lib.rs");
        let llbc_path = dir.join("crate.llbc");
        let charon_argv = substitute(
            &self.cfg.charon_cmd,
            &[
                ("input", &lib_path.to_string_lossy()),
                ("output", &llbc_path.to_string_lossy()),
            ],
        );
        let charon_out = run_cmd(
            &charon_argv,
            &self.cfg.extra_env,
            &dir,
            Duration::from_secs(self.cfg.timeout_secs.charon),
            "charon",
        )?;
        result
            .timings_ms
            .insert("charon_ms".to_string(), charon_out.duration_ms);
        result.charon_ok = charon_out.exit_code == Some(0) && llbc_path.exists();
        if !result.charon_ok {
            // charon failure on rustc-accepted code: out of scope (logged only).
            return Ok((result, pack));
        }

        // --- aeneas (translate) ---
        let dest = dir.join("lean-out");
        let flags = if opts.use_checks {
            self.cfg.checks_flags_or_translate()
        } else {
            &self.cfg.translate_flags
        };
        let subs = substitute(
            flags,
            &[
                ("llbc", &llbc_path.to_string_lossy()),
                ("dest", &dest.to_string_lossy()),
            ],
        );
        let mut aeneas_argv = self.cfg.aeneas_cmd.clone();
        aeneas_argv.extend(subs);
        let aeneas_out = run_cmd(
            &aeneas_argv,
            &self.cfg.extra_env,
            &dir,
            Duration::from_secs(self.cfg.timeout_secs.aeneas),
            "aeneas",
        )?;
        result
            .timings_ms
            .insert("aeneas_ms".to_string(), aeneas_out.duration_ms);
        let verdict = oracle::classify(
            &oracle::RawOutcome {
                exit_code: aeneas_out.exit_code,
                stdout: &aeneas_out.stdout,
                stderr: &aeneas_out.stderr,
                timed_out: aeneas_out.timed_out,
            },
            &self.patterns,
        );
        result.aeneas_stdout = aeneas_out.stdout.clone();
        result.aeneas_stderr = aeneas_out.stderr.clone();
        result.verdict = Some(verdict.clone());

        // --- optional borrow-check ---
        if opts.run_borrowck && !self.cfg.borrowck_flags.is_empty() {
            let subs = substitute(
                &self.cfg.borrowck_flags,
                &[("llbc", &llbc_path.to_string_lossy())],
            );
            let mut bc_argv = self.cfg.aeneas_cmd.clone();
            bc_argv.extend(subs);
            let bc_out = run_cmd(
                &bc_argv,
                &self.cfg.extra_env,
                &dir,
                Duration::from_secs(self.cfg.timeout_secs.aeneas),
                "borrowck",
            )?;
            result
                .timings_ms
                .insert("borrowck_ms".to_string(), bc_out.duration_ms);
            let bcv = oracle::classify(
                &oracle::RawOutcome {
                    exit_code: bc_out.exit_code,
                    stdout: &bc_out.stdout,
                    stderr: &bc_out.stderr,
                    timed_out: bc_out.timed_out,
                },
                &self.patterns,
            );
            result.borrowck = Some(bcv);
        }

        // --- optional O3 lean elaboration ---
        if opts.run_lean_elab && matches!(result.verdict, Some(Verdict::Success)) {
            if let Some(backend) = &self.cfg.lean_backend_dir {
                match self.run_lean_elab(&dir, &dest, backend) {
                    Ok(ok) => result.lean_elab_ok = Some(ok),
                    Err(e) => {
                        eprintln!("[lean-elab] {crate_id}: {e}");
                        result.lean_elab_ok = None;
                    }
                }
            }
        }

        Ok((result, pack))
    }

    /// Best-effort O3 lean-elab: assemble a scratch lake project that imports the
    /// generated `.lean` files and requires the backend, then `lake build`.
    /// This is scaffolding: exact module wiring is target-specific.
    fn run_lean_elab(&self, dir: &Path, dest: &Path, backend: &str) -> Result<bool> {
        let lean_files: Vec<PathBuf> = walk_files(dest, "lean");
        if lean_files.is_empty() {
            return Ok(true); // nothing to elaborate
        }
        let proj = dir.join("lean-proj");
        std::fs::create_dir_all(&proj)?;
        // Reference the backend via a relative/absolute lake require.
        let lakefile = format!(
            "import Lake\nopen Lake DSL\n\npackage fuzzcheck\n\nrequire aeneas from \"{}\"\n\nlean_lib FuzzCheck\n",
            backend
        );
        std::fs::write(proj.join("lakefile.lean"), lakefile)?;
        // Copy generated lean files into the project root.
        let libdir = proj.join("FuzzCheck");
        std::fs::create_dir_all(&libdir)?;
        for lf in &lean_files {
            if let Some(name) = lf.file_name() {
                std::fs::copy(lf, libdir.join(name))?;
            }
        }
        let argv = vec!["lake".to_string(), "build".to_string()];
        let out = run_cmd(
            &argv,
            &self.cfg.extra_env,
            &proj,
            Duration::from_secs(self.cfg.timeout_secs.lake),
            "lake",
        )?;
        Ok(out.exit_code == Some(0))
    }
}

/// Recursively collect files with a given extension.
fn walk_files(dir: &Path, ext: &str) -> Vec<PathBuf> {
    let mut out = Vec::new();
    if let Ok(rd) = std::fs::read_dir(dir) {
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                out.extend(walk_files(&p, ext));
            } else if p.extension().map(|x| x == ext).unwrap_or(false) {
                out.push(p);
            }
        }
    }
    out
}

/// Parse rustc `--error-format=json` stderr and map error line spans to the
/// pack unit indices that own them.
pub fn parse_rustc_offenders(stderr_json: &str, pack: &Pack) -> BTreeSet<usize> {
    let mut offenders = BTreeSet::new();
    for line in stderr_json.lines() {
        let line = line.trim();
        if !line.starts_with('{') {
            continue;
        }
        let v: serde_json::Value = match serde_json::from_str(line) {
            Ok(v) => v,
            Err(_) => continue,
        };
        if v.get("level").and_then(|l| l.as_str()) != Some("error") {
            continue;
        }
        collect_spans(&v, pack, &mut offenders);
    }
    offenders
}

fn collect_spans(v: &serde_json::Value, pack: &Pack, offenders: &mut BTreeSet<usize>) {
    if let Some(spans) = v.get("spans").and_then(|s| s.as_array()) {
        for sp in spans {
            if let Some(l) = sp.get("line_start").and_then(|n| n.as_u64()) {
                for u in pack.units_at_line(l as usize) {
                    offenders.insert(u);
                }
            }
        }
    }
    // Errors can attach their real location in children.
    if let Some(children) = v.get("children").and_then(|c| c.as_array()) {
        for c in children {
            collect_spans(c, pack, offenders);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::corpus::units_from_source;

    fn mk_inputs(srcs: &[(&str, &str)]) -> Vec<PackInput> {
        let mut inputs = Vec::new();
        for (src, fname) in srcs {
            let units = units_from_source(src, Path::new("t.rs")).unwrap();
            let unit = units.into_iter().find(|u| &u.orig_name == fname).unwrap();
            let prov = unit.provenance();
            inputs.push(PackInput {
                unit,
                provenance: prov,
            });
        }
        inputs
    }

    #[test]
    fn offender_mapping_from_json() {
        let inputs = mk_inputs(&[
            ("pub fn a() -> u32 { 1 }", "a"),
            ("pub fn b() -> u32 { 2 }", "b"),
        ]);
        let pack = corpus::pack(&inputs, "c");
        // pick a line inside f_1_b and craft a fake rustc error there.
        let line = pack.functions[1].line_start;
        let json = format!(
            "{{\"$message_type\":\"diagnostic\",\"level\":\"error\",\"message\":\"x\",\"spans\":[{{\"file_name\":\"lib.rs\",\"line_start\":{line},\"line_end\":{line},\"is_primary\":true}}],\"children\":[]}}"
        );
        let offenders = parse_rustc_offenders(&json, &pack);
        assert!(offenders.contains(&1));
        assert!(!offenders.contains(&0));
    }
}
