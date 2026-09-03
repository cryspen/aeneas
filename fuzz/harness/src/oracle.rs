//! Oracles: classify an aeneas invocation outcome into a verdict.
//!
//! O1 (crash) and O2 (wrong-rejection) live here. O3 (lean elaboration) is
//! driven from `pipeline.rs` but its outcome is also a [`Verdict`].
//!
//! Stream conventions (see `fuzz/targets/fork.toml`):
//!   * `[Error] <message>` and `Compiler source: <file>, line N` -> STDOUT
//!   * `Uncaught exception:` + `Raised at` / `Called from ... in file "X", line N`
//!     backtrace frames -> STDERR
//!   * `Source: '<path.rs>', lines ...` (the *user* source) -> STDOUT, and is
//!     deliberately excluded from fingerprints.

use serde::{Deserialize, Serialize};

/// Error class inferred from the `[Error]` message text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ErrorClass {
    InternalError,
    Unreachable,
    SanityCheck,
    Other,
}

impl ErrorClass {
    pub fn as_str(&self) -> &'static str {
        match self {
            ErrorClass::InternalError => "InternalError",
            ErrorClass::Unreachable => "Unreachable",
            ErrorClass::SanityCheck => "SanityCheck",
            ErrorClass::Other => "Other",
        }
    }

    pub fn parse(s: &str) -> ErrorClass {
        match s {
            "InternalError" => ErrorClass::InternalError,
            "Unreachable" => ErrorClass::Unreachable,
            "SanityCheck" => ErrorClass::SanityCheck,
            _ => ErrorClass::Other,
        }
    }

    /// Infer the class from the human error message text.
    pub fn from_message(msg: &str) -> ErrorClass {
        let m = msg.to_ascii_lowercase();
        if m.contains("unreachable") {
            ErrorClass::Unreachable
        } else if m.contains("sanity") || m.contains("assertion failed") {
            ErrorClass::SanityCheck
        } else if m.contains("internal error") {
            ErrorClass::InternalError
        } else {
            ErrorClass::Other
        }
    }
}

/// A crash fingerprint: the match key for dedup is (class, basename(file), line),
/// with a line-drift tolerance applied by the triage layer.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Fingerprint {
    pub error_class: ErrorClass,
    /// Aeneas source file exactly as printed (may carry a dir prefix).
    pub file: String,
    pub line: u32,
    /// The human `[Error]` message (first line), for readability.
    pub message: String,
    /// Topmost meaningful aeneas backtrace frame (fn name + file:line), if any.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub top_frame: Option<String>,
}

impl Fingerprint {
    /// Basename of the source file (directory prefix stripped), used as the
    /// stable match key so `pure/Foo.ml` and `Foo.ml` unify across builds.
    pub fn file_basename(&self) -> &str {
        self.file
            .rsplit(['/', '\\'])
            .next()
            .unwrap_or(&self.file)
    }
}

/// Whether a clean rejection is an expected feature gate or a suspicious one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RejectClass {
    Expected,
    Suspicious,
}

/// The final verdict for one aeneas invocation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum Verdict {
    Success,
    Crash {
        fingerprint: Fingerprint,
    },
    Reject {
        #[serde(skip_serializing_if = "Option::is_none")]
        site: Option<String>,
        classification: RejectClass,
        message: String,
    },
    Timeout,
}

impl Verdict {
    pub fn is_crash(&self) -> bool {
        matches!(self, Verdict::Crash { .. })
    }
    pub fn is_success(&self) -> bool {
        matches!(self, Verdict::Success)
    }
    pub fn fingerprint(&self) -> Option<&Fingerprint> {
        match self {
            Verdict::Crash { fingerprint } => Some(fingerprint),
            _ => None,
        }
    }
    /// A short label for logs.
    pub fn label(&self) -> String {
        match self {
            Verdict::Success => "success".into(),
            Verdict::Crash { fingerprint } => format!(
                "crash[{} {}:{}]",
                fingerprint.error_class.as_str(),
                fingerprint.file_basename(),
                fingerprint.line
            ),
            Verdict::Reject { classification, .. } => match classification {
                RejectClass::Expected => "reject[expected]".into(),
                RejectClass::Suspicious => "reject[SUSPICIOUS]".into(),
            },
            Verdict::Timeout => "timeout".into(),
        }
    }
    /// Is this an interesting outcome worth triaging? (crash or suspicious reject)
    pub fn is_interesting(&self) -> bool {
        matches!(self, Verdict::Crash { .. })
            || matches!(
                self,
                Verdict::Reject {
                    classification: RejectClass::Suspicious,
                    ..
                }
            )
    }
}

/// Expected-rejection pattern set (oracle O2 config).
#[derive(Debug, Clone)]
pub struct RejectPatterns {
    patterns: Vec<String>,
}

const EMBEDDED_PATTERNS: &str = include_str!("../data/expected_reject_patterns.txt");

impl RejectPatterns {
    pub fn from_text(text: &str) -> RejectPatterns {
        let patterns = text
            .lines()
            .map(|l| l.trim())
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
            .map(|l| l.to_ascii_lowercase())
            .collect();
        RejectPatterns { patterns }
    }

    /// The compiled-in default set (from `data/expected_reject_patterns.txt`).
    pub fn default_embedded() -> RejectPatterns {
        RejectPatterns::from_text(EMBEDDED_PATTERNS)
    }

    /// Load a pattern set from a file, falling back to the embedded default.
    pub fn load(path: &std::path::Path) -> RejectPatterns {
        match std::fs::read_to_string(path) {
            Ok(t) => RejectPatterns::from_text(&t),
            Err(_) => RejectPatterns::default_embedded(),
        }
    }

    pub fn is_expected(&self, message: &str) -> bool {
        let m = message.to_ascii_lowercase();
        self.patterns.iter().any(|p| m.contains(p))
    }
}

/// Raw process output to classify.
pub struct RawOutcome<'a> {
    pub exit_code: Option<i32>,
    pub stdout: &'a str,
    pub stderr: &'a str,
    pub timed_out: bool,
}

/// True if the output carries a genuine crash signal: an uncaught OCaml
/// exception or a backtrace. A bare `Compiler source:` line is NOT sufficient —
/// `[%warn]` prints one on a *successful* (exit 0) run, which is not a crash
/// (this was the `extract/Extract.ml:2851` false positive). Crash classification
/// additionally requires a nonzero exit (see `classify`).
fn has_crash_signal(stderr: &str) -> bool {
    stderr.contains("Uncaught exception:") || has_backtrace_frame(stderr)
}

/// The uncaught-exception region of stderr: from `(Failure` up to the start of
/// the OCaml backtrace (`Raised at`). This is the fatal event; anchoring the
/// fingerprint's message + `Compiler source:` here (rather than to any earlier
/// non-fatal `[Error]`/`Compiler source:` printed on stdout) is what fixes the
/// multi-error-pack mislabels.
fn failure_region(stderr: &str) -> Option<&str> {
    let start = stderr.find("(Failure")?;
    let after = &stderr[start..];
    let end = after.find("Raised at").unwrap_or(after.len());
    Some(&after[..end])
}

fn has_backtrace_frame(stderr: &str) -> bool {
    stderr.lines().any(|l| {
        let l = l.trim_start();
        (l.starts_with("Raised at") || l.starts_with("Called from"))
            && l.contains("in file \"")
    })
}

/// Extract the human error message. Two layouts occur in practice:
///   1. a `[Error] <message>` line (non-abort / logger path), and/or
///   2. an OCaml `Failure "<message>\nSource: ...\nCompiler source: ..."` on
///      stderr under `-abort-on-error` (stdout is often empty in this case).
///
/// When an uncaught exception exists, its `Failure` text is the *fatal* event
/// and takes precedence over any earlier non-fatal `[Error]` line printed on
/// stdout (a stray soft error must not steal the fingerprint's message).
fn extract_error_message(stdout: &str, stderr: &str) -> Option<String> {
    if let Some(m) = extract_failure_message(stderr) {
        return Some(m);
    }
    for stream in [stdout, stderr] {
        for line in stream.lines() {
            let t = line.trim_start();
            if let Some(rest) = t.strip_prefix("[Error]") {
                let msg = rest.trim();
                if !msg.is_empty() {
                    return Some(msg.to_string());
                }
            }
        }
    }
    None
}

/// Pull the leading message out of an OCaml `(Failure "...")` on stderr. The
/// message is the text before the first embedded `\n` escape or closing quote
/// (i.e. before the `Source:`/`Compiler source:` tail).
fn extract_failure_message(stderr: &str) -> Option<String> {
    let idx = stderr.find("(Failure")?;
    let after = &stderr[idx..];
    let q = after.find('"')?;
    let body = &after[q + 1..];
    // Cut at the first backslash (start of a `\n` escape) or closing quote.
    let end = body.find(['\\', '"']).unwrap_or(body.len());
    let msg = body[..end].trim();
    if msg.is_empty() {
        None
    } else {
        Some(msg.to_string())
    }
}

/// Parse the first `Compiler source: <file>, line <N>` in a single stream.
fn scan_compiler_source(stream: &str) -> Option<(String, u32)> {
    for line in stream.lines() {
        if let Some(idx) = line.find("Compiler source:") {
            let rest = &line[idx + "Compiler source:".len()..];
            // format: " <file>, line <N>"  (the `\` line-continuation in the
            // Failure block leaves a trailing backslash we trim off)
            if let Some((file_part, line_part)) = rest.rsplit_once(", line") {
                let file = file_part.trim().to_string();
                let digits: String = line_part
                    .trim_start()
                    .chars()
                    .take_while(|c| c.is_ascii_digit())
                    .collect();
                if let Ok(n) = digits.parse::<u32>() {
                    return Some((file, n));
                }
            }
        }
    }
    None
}

/// Parse `Compiler source: <file>, line <N>`, scanning stdout then stderr.
fn extract_compiler_source(stdout: &str, stderr: &str) -> Option<(String, u32)> {
    scan_compiler_source(stdout).or_else(|| scan_compiler_source(stderr))
}

/// Files that are raise-helpers / stdlib / runtime plumbing — never the real
/// crash site. Matched by basename.
fn is_plumbing_file(basename: &str) -> bool {
    const PLUMBING: &[&str] = &[
        "Errors.ml",
        "Parallel.ml",
        "renderer.ml",
        "fun.ml",
        "option.ml",
        "list.ml",
        "array.ml",
        "map.ml",
        "set.ml",
        "string.ml",
        "hashtbl.ml",
        "buffer.ml",
        "stdlib.ml",
    ];
    PLUMBING.iter().any(|p| p.eq_ignore_ascii_case(basename))
}

fn basename(path: &str) -> &str {
    path.rsplit(['/', '\\']).next().unwrap_or(path)
}

/// Find the topmost meaningful aeneas frame from the stderr backtrace.
/// Returns `(fn_desc, file, line)`.
fn extract_top_frame(stderr: &str) -> Option<(String, String, u32)> {
    for line in stderr.lines() {
        let t = line.trim_start();
        if !(t.starts_with("Raised at") || t.starts_with("Called from")) {
            continue;
        }
        // e.g. `Called from Aeneas__X.f in file "pure/Y.ml", lines 1818-1819, ...`
        let file_key = "in file \"";
        let fidx = match t.find(file_key) {
            Some(i) => i,
            None => continue,
        };
        let after = &t[fidx + file_key.len()..];
        let fend = match after.find('"') {
            Some(i) => i,
            None => continue,
        };
        let file = &after[..fend];
        if is_plumbing_file(basename(file)) {
            continue;
        }
        // line number: after `line ` or `lines `
        let tail = &after[fend..];
        let line_no = tail
            .find("line")
            .and_then(|i| {
                let s = &tail[i + 4..];
                let s = s.trim_start_matches('s').trim_start();
                let digits: String = s.chars().take_while(|c| c.is_ascii_digit()).collect();
                digits.parse::<u32>().ok()
            })
            .unwrap_or(0);
        // function descriptor: between the leading keyword and " in file"
        let desc_start = if t.starts_with("Raised at") {
            "Raised at".len()
        } else {
            "Called from".len()
        };
        let desc = t[desc_start..fidx].trim().to_string();
        return Some((desc, file.to_string(), line_no));
    }
    None
}

/// Build a crash fingerprint from process output.
pub fn extract_fingerprint(stdout: &str, stderr: &str) -> Fingerprint {
    let message = extract_error_message(stdout, stderr).unwrap_or_default();
    let mut error_class = ErrorClass::from_message(&message);
    if matches!(error_class, ErrorClass::Other) {
        // The abort-on-error path embeds the class inside the exception text;
        // fall back to scanning the whole combined output.
        let combined = format!("{stdout}\n{stderr}");
        error_class = ErrorClass::from_message(&combined);
    }
    let top = extract_top_frame(stderr);

    // File:line anchoring, most-authoritative first:
    //  1. the `Compiler source:` embedded in the uncaught-exception block (the
    //     fatal event — beats any stray earlier line on stdout),
    //  2. any `Compiler source:` line (non-abort logger path),
    //  3. the topmost meaningful backtrace frame.
    let (file, line) = failure_region(stderr)
        .and_then(scan_compiler_source)
        .or_else(|| extract_compiler_source(stdout, stderr))
        .or_else(|| top.as_ref().map(|(_, f, n)| (f.clone(), *n)))
        .unwrap_or_else(|| ("<unknown>".to_string(), 0));

    let top_frame = top.map(|(desc, f, n)| format!("{} @ {}:{}", desc, f, n));

    Fingerprint {
        error_class,
        file,
        line,
        message,
        top_frame,
    }
}

/// Classify a raw aeneas outcome into a verdict.
pub fn classify(raw: &RawOutcome, patterns: &RejectPatterns) -> Verdict {
    if raw.timed_out {
        return Verdict::Timeout;
    }

    // A crash requires BOTH a nonzero exit AND a genuine crash signal (uncaught
    // exception / backtrace). Exit 0 is a success even if a `[%warn]` printed a
    // `Compiler source:` line; a nonzero exit with only a `[Error]` diagnostic
    // (no backtrace) is a rejection, handled below.
    let nonzero = !matches!(raw.exit_code, Some(0));
    if nonzero && has_crash_signal(raw.stderr) {
        let fingerprint = extract_fingerprint(raw.stdout, raw.stderr);
        // Feature gates (e.g. "Returns inside of nested loops are not supported
        // yet") are raised through the same `craise`/sanity-check machinery as
        // real internal errors, so they carry a backtrace + `Compiler source:`
        // line and trip `has_crash_signal`. But per DESIGN.md O2 they are
        // *expected* limitations, not completeness-bug findings. Reclassify them
        // as Expected rejections. Genuine crashes (F4 "Internal error, please
        // file an issue"; F6 "Unreachable") do not match any feature-gate
        // pattern and stay crashes.
        if patterns.is_expected(&fingerprint.message) {
            return Verdict::Reject {
                site: Some(format!("{}:{}", fingerprint.file, fingerprint.line)),
                classification: RejectClass::Expected,
                message: fingerprint.message,
            };
        }
        return Verdict::Crash { fingerprint };
    }

    if let Some(message) = extract_error_message(raw.stdout, raw.stderr) {
        let classification = if patterns.is_expected(&message) {
            RejectClass::Expected
        } else {
            RejectClass::Suspicious
        };
        let site = extract_compiler_source(raw.stdout, raw.stderr)
            .map(|(f, n)| format!("{}:{}", f, n));
        return Verdict::Reject {
            site,
            classification,
            message,
        };
    }

    if raw.exit_code == Some(0) {
        return Verdict::Success;
    }

    // Nonzero exit, no diagnostic we recognize (e.g. an arg-usage error). Treat
    // as a suspicious rejection so it surfaces in triage rather than silently
    // counting as success.
    let tail: String = raw
        .stderr
        .lines()
        .rev()
        .take(3)
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .collect::<Vec<_>>()
        .join(" | ");
    Verdict::Reject {
        site: None,
        classification: RejectClass::Suspicious,
        message: format!("nonzero exit {:?}, no diagnostic: {}", raw.exit_code, tail),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Canned F4 backtrace, split across streams the way the fork binary emits it.
    const F4_STDOUT: &str = "\
[Info ] Imported: f4_return_in_loop.llbc
[Error] Internal error, please file an issue
Source: '/tmp/x/f4_return_in_loop.rs', lines 1:0-3:1
Compiler source: pure/PureMicroPassesLoops.ml, line 1818
";
    const F4_STDERR: &str = "\
Uncaught exception:
  (Failure \"Internal error, please file an issue\")
Raised at Aeneas__Errors.craise_opt_span in file \"Errors.ml\", line 120, characters 4-23
Called from Aeneas__PureMicroPassesLoops.reorder_loop_outputs.update_and_close_loop_body.upd in file \"pure/PureMicroPassesLoops.ml\", lines 1818-1819, characters 18-67
Called from Aeneas__PureMicroPassesLoops.reorder_loop_outputs.explore in file \"pure/PureMicroPassesLoops.ml\", lines 2205-2206, characters 22-45
";

    const F6_STDOUT: &str = "\
[Info ] Imported: f6a.llbc
[Error] Unreachable
Source: '/tmp/x/f6a.rs', lines 7:4-11:5
Compiler source: interp/InterpAbs.ml, line 1671
";
    const F6_STDERR: &str = "\
Uncaught exception:
  (Failure \"Unreachable\")
Raised at Aeneas__Errors.craise_opt_span in file \"Errors.ml\", line 120, characters 4-23
Called from Aeneas__InterpAbs.merge_abs_conts_aux in file \"interp/InterpAbs.ml\", line 1915, characters 4-65
";

    #[test]
    fn f4_fingerprint() {
        let fp = extract_fingerprint(F4_STDOUT, F4_STDERR);
        assert_eq!(fp.error_class, ErrorClass::InternalError);
        assert_eq!(fp.file, "pure/PureMicroPassesLoops.ml");
        assert_eq!(fp.file_basename(), "PureMicroPassesLoops.ml");
        assert_eq!(fp.line, 1818);
        // top meaningful frame skips Errors.ml (the craise helper)
        let tf = fp.top_frame.unwrap();
        assert!(tf.contains("reorder_loop_outputs"), "got {tf}");
        assert!(tf.contains("PureMicroPassesLoops.ml:1818"), "got {tf}");
    }

    #[test]
    fn f4_classify_is_crash() {
        let raw = RawOutcome {
            exit_code: Some(2),
            stdout: F4_STDOUT,
            stderr: F4_STDERR,
            timed_out: false,
        };
        let v = classify(&raw, &RejectPatterns::default_embedded());
        match v {
            Verdict::Crash { fingerprint } => {
                assert_eq!(fingerprint.line, 1818);
                assert_eq!(fingerprint.error_class, ErrorClass::InternalError);
            }
            other => panic!("expected crash, got {other:?}"),
        }
    }

    // The real fork binary under -abort-on-error: stdout EMPTY, everything
    // embedded in the OCaml Failure string on stderr.
    const F4_ABORT_STDERR: &str = "\
Uncaught exception:

  (Failure
    \"Internal error, please file an issue\\
   \\nSource: '/tmp/x/lib.rs', lines 4:0-11:1\\
   \\nCompiler source: pure/PureMicroPassesLoops.ml, line 1818\")

Raised at Aeneas__Errors.craise_opt_span in file \"Errors.ml\", line 120, characters 4-23
Called from Aeneas__PureMicroPassesLoops.reorder_loop_outputs.update_and_close_loop_body.upd in file \"pure/PureMicroPassesLoops.ml\", lines 1818-1819, characters 18-67
";

    #[test]
    fn f4_abort_format_fingerprint() {
        let fp = extract_fingerprint("", F4_ABORT_STDERR);
        assert_eq!(fp.error_class, ErrorClass::InternalError, "fp={fp:?}");
        assert_eq!(fp.file_basename(), "PureMicroPassesLoops.ml");
        assert_eq!(fp.line, 1818);
        assert_eq!(fp.message, "Internal error, please file an issue");
    }

    #[test]
    fn f4_abort_format_classify_is_crash() {
        let v = classify(
            &RawOutcome {
                exit_code: Some(2),
                stdout: "",
                stderr: F4_ABORT_STDERR,
                timed_out: false,
            },
            &RejectPatterns::default_embedded(),
        );
        match v {
            Verdict::Crash { fingerprint } => {
                assert_eq!(fingerprint.error_class, ErrorClass::InternalError);
                assert_eq!(fingerprint.line, 1818);
            }
            other => panic!("expected crash, got {other:?}"),
        }
    }

    // A feature gate raised via craise: it carries a backtrace + Compiler-source
    // line (so it trips has_crash_signal) yet is an EXPECTED limitation.
    const NESTED_RETURN_STDOUT: &str = "\
[Info ] Imported: lib.llbc
[Error] Returns inside of nested loops are not supported yet
Source: '/tmp/x/lib.rs', lines 1:0-9:1
Compiler source: PrePasses.ml, line 628
";
    const NESTED_RETURN_STDERR: &str = "\
Uncaught exception:
  (Failure \"Returns inside of nested loops are not supported yet\")
Raised at Aeneas__Errors.craise_opt_span in file \"Errors.ml\", line 120, characters 4-23
Called from Aeneas__PrePasses.update_loops.object#visit_statement in file \"PrePasses.ml\", line 628, characters 4-40
";

    #[test]
    fn feature_gate_with_backtrace_is_expected_not_crash() {
        let v = classify(
            &RawOutcome {
                exit_code: Some(2),
                stdout: NESTED_RETURN_STDOUT,
                stderr: NESTED_RETURN_STDERR,
                timed_out: false,
            },
            &RejectPatterns::default_embedded(),
        );
        match v {
            Verdict::Reject {
                classification: RejectClass::Expected,
                ..
            } => {}
            other => panic!("expected Expected reject for a feature gate, got {other:?}"),
        }
    }

    #[test]
    fn f6_fingerprint() {
        let fp = extract_fingerprint(F6_STDOUT, F6_STDERR);
        assert_eq!(fp.error_class, ErrorClass::Unreachable);
        assert_eq!(fp.file_basename(), "InterpAbs.ml");
        assert_eq!(fp.line, 1671);
        assert!(fp.top_frame.unwrap().contains("merge_abs_conts_aux"));
    }

    // Real fork emission of the N1 assert-double-eval crash under -abort-on-error:
    // the Compiler-source line is embedded inside the (Failure "...") block.
    const N1_STDOUT: &str = "\
[Info ] Imported: nb.llbc
[Error] There should be no bottoms in the value
Source: 'nb.rs', lines 3:12-3:14
Compiler source: interp/InterpExpressions.ml, line 55
";
    const N1_STDERR: &str = "\
Uncaught exception:

  (Failure
    \"There should be no bottoms in the value\\
   \\nSource: 'nb.rs', lines 3:12-3:14\\
   \\nCompiler source: interp/InterpExpressions.ml, line 55\")

Raised at Aeneas__Errors.craise_opt_span in file \"Errors.ml\", line 120, characters 4-23
Called from Aeneas__InterpExpressions.read_place_check in file \"interp/InterpExpressions.ml\", lines 55-57, characters 2-45
Called from Aeneas__InterpStatements.eval_assertion_concrete.(fun) in file \"interp/InterpStatements.ml\", line 133, characters 24-67
";

    #[test]
    fn n1_fingerprint_from_failure_block() {
        let fp = extract_fingerprint(N1_STDOUT, N1_STDERR);
        assert_eq!(fp.file_basename(), "InterpExpressions.ml");
        assert_eq!(fp.line, 55);
        assert_eq!(fp.message, "There should be no bottoms in the value");
        // top meaningful frame is the read_place_check site (skips Errors.ml)
        assert!(fp.top_frame.unwrap().contains("read_place_check"));
    }

    // A [%warn] prints "[Error]"/"Compiler source:" but aeneas EXITS 0 and
    // generates Lean — this must be Success, not a crash (extract/Extract.ml:2851
    // false positive). No uncaught exception / backtrace is present.
    // A [%warn] emits a "Compiler source:" marker with NO "[Error]" line (the
    // real finding recorded an empty message) and exits 0.
    const WARN_EXIT0_STDOUT: &str = "\
[Info ] Imported: lib.llbc
[Warning] No model for core::iter::adapters::...::collect; axiomatizing
Source: 'lib.rs', lines 2:4-2:20
Compiler source: extract/Extract.ml, line 2851
[Info ] Generated the Lean file: out/Lib.lean
";

    #[test]
    fn warn_at_exit0_is_success_not_crash() {
        let v = classify(
            &RawOutcome {
                exit_code: Some(0),
                stdout: WARN_EXIT0_STDOUT,
                stderr: "",
                timed_out: false,
            },
            &RejectPatterns::default_embedded(),
        );
        assert!(v.is_success(), "expected Success for an exit-0 warn, got {v:?}");
    }

    // Multi-error pack: a stray non-fatal error prints its own [Error]/Compiler-
    // source on stdout FIRST, but the fatal uncaught exception is F6. The
    // fingerprint must anchor to the fatal event (InterpAbs.ml:1671), not the
    // stray InterpExpressions.ml:55 on stdout.
    const MISLABEL_STDOUT: &str = "\
[Info ] Imported: pack.llbc
[Error] There should be no bottoms in the value
Source: 'pack.rs', lines 3:12-3:14
Compiler source: interp/InterpExpressions.ml, line 55
[Error] Unreachable
Source: 'pack.rs', lines 20:4-24:5
Compiler source: interp/InterpAbs.ml, line 1671
";
    const MISLABEL_STDERR: &str = "\
Uncaught exception:

  (Failure
    \"Unreachable\\
   \\nSource: 'pack.rs', lines 20:4-24:5\\
   \\nCompiler source: interp/InterpAbs.ml, line 1671\")

Raised at Aeneas__Errors.craise_opt_span in file \"Errors.ml\", line 120, characters 4-23
Called from Aeneas__InterpAbs.merge_abs_conts_aux in file \"interp/InterpAbs.ml\", line 1915, characters 4-65
";

    #[test]
    fn mislabel_pack_anchors_to_fatal_exception() {
        let fp = extract_fingerprint(MISLABEL_STDOUT, MISLABEL_STDERR);
        assert_eq!(fp.message, "Unreachable");
        assert_eq!(fp.error_class, ErrorClass::Unreachable);
        assert_eq!(fp.file_basename(), "InterpAbs.ml");
        assert_eq!(fp.line, 1671, "must anchor to the fatal F6 event, not the stray :55");
    }

    #[test]
    fn expected_reject() {
        let raw = RawOutcome {
            exit_code: Some(1),
            stdout: "[Error] Nested borrows are not supported yet\n",
            stderr: "",
            timed_out: false,
        };
        let v = classify(&raw, &RejectPatterns::default_embedded());
        match v {
            Verdict::Reject {
                classification: RejectClass::Expected,
                ..
            } => {}
            other => panic!("expected Expected reject, got {other:?}"),
        }
    }

    #[test]
    fn suspicious_reject() {
        let raw = RawOutcome {
            exit_code: Some(1),
            stdout: "[Error] the frobnicator exploded unexpectedly\n",
            stderr: "",
            timed_out: false,
        };
        let v = classify(&raw, &RejectPatterns::default_embedded());
        match v {
            Verdict::Reject {
                classification: RejectClass::Suspicious,
                ..
            } => {}
            other => panic!("expected Suspicious reject, got {other:?}"),
        }
    }

    #[test]
    fn success_and_timeout() {
        let ok = classify(
            &RawOutcome {
                exit_code: Some(0),
                stdout: "[Info ] done\n",
                stderr: "",
                timed_out: false,
            },
            &RejectPatterns::default_embedded(),
        );
        assert!(ok.is_success());

        let to = classify(
            &RawOutcome {
                exit_code: None,
                stdout: "",
                stderr: "",
                timed_out: true,
            },
            &RejectPatterns::default_embedded(),
        );
        assert_eq!(to, Verdict::Timeout);
    }
}
