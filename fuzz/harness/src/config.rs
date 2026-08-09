//! Target configuration loading.
//!
//! A *target* describes how to invoke a particular (charon, aeneas) pair. It is
//! entirely config-driven — no charon/aeneas paths are hardcoded anywhere in
//! the harness. See `fuzz/targets/example.toml` for the documented schema and
//! `fuzz/targets/fork.toml` for a real config.
//!
//! Command templates are argv lists (first element = program) containing
//! placeholder tokens that are substituted per stage:
//!   * charon_cmd : `{input}` (the lib.rs) and `{output}` (the .llbc)
//!   * aeneas_cmd : the base argv (usually just the binary). The per-mode flag
//!                  sets (`translate_flags` / `checks_flags` / `borrowck_flags`)
//!                  are appended and carry the `{llbc}` and `{dest}`
//!                  placeholders.

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::path::Path;

/// Per-stage process timeouts, in seconds.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct Timeouts {
    #[serde(default = "default_rustc_timeout")]
    pub rustc: u64,
    #[serde(default = "default_charon_timeout")]
    pub charon: u64,
    #[serde(default = "default_aeneas_timeout")]
    pub aeneas: u64,
    #[serde(default = "default_lake_timeout")]
    pub lake: u64,
}

fn default_rustc_timeout() -> u64 {
    30
}
fn default_charon_timeout() -> u64 {
    60
}
fn default_aeneas_timeout() -> u64 {
    120
}
fn default_lake_timeout() -> u64 {
    600
}

impl Default for Timeouts {
    fn default() -> Self {
        Timeouts {
            rustc: default_rustc_timeout(),
            charon: default_charon_timeout(),
            aeneas: default_aeneas_timeout(),
            lake: default_lake_timeout(),
        }
    }
}

/// A known-bug fingerprint carried in a target config, so a target can declare
/// which crashes it is *expected* to reproduce (e.g. the fork reproduces F4/F6).
/// These augment `fuzz/findings/db.json` for dedup/recognition.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct KnownFinding {
    pub id: String,
    /// One of: InternalError | Unreachable | SanityCheck | Other
    pub error_class: String,
    #[serde(default)]
    pub message: String,
    /// Aeneas source file (may carry a directory prefix, e.g. `pure/Foo.ml`).
    pub file: String,
    pub line: u32,
    #[serde(default)]
    pub issue: Option<String>,
}

/// A fully-parsed target configuration.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct TargetConfig {
    pub name: String,

    /// charon argv template. Placeholders: `{input}` (lib.rs), `{output}` (llbc).
    pub charon_cmd: Vec<String>,

    /// aeneas base argv (usually just the binary path). The per-mode flag sets
    /// are appended to this.
    pub aeneas_cmd: Vec<String>,

    /// Extra environment variables applied to every stage.
    #[serde(default)]
    pub extra_env: BTreeMap<String, String>,

    /// Flags for the fast translation pass (campaign default). Placeholders:
    /// `{llbc}`, `{dest}`.
    #[serde(default)]
    pub translate_flags: Vec<String>,

    /// Flags for the slow, thorough verification pass (verify/minimize path).
    /// Placeholders: `{llbc}`, `{dest}`. Optional; falls back to translate_flags.
    #[serde(default)]
    pub checks_flags: Vec<String>,

    /// Flags for standalone borrow-check mode. Placeholder: `{llbc}` (no dest).
    #[serde(default)]
    pub borrowck_flags: Vec<String>,

    /// Path to the Lean backend dir (for the O3 elaboration oracle). Optional.
    #[serde(default)]
    pub lean_backend_dir: Option<String>,

    /// Whether the target's aeneas supports `-dump-pure-ir` (phase 3).
    #[serde(default)]
    pub supports_dump_pure_ir: bool,

    #[serde(default)]
    pub timeout_secs: Timeouts,

    /// Known-bug fingerprints this target is expected to reproduce.
    #[serde(default)]
    pub known_findings: Vec<KnownFinding>,
}

impl TargetConfig {
    pub fn load(path: &Path) -> Result<TargetConfig> {
        let text = std::fs::read_to_string(path)
            .with_context(|| format!("reading target config {}", path.display()))?;
        let mut cfg: TargetConfig = toml::from_str(&text)
            .with_context(|| format!("parsing target config {}", path.display()))?;
        // Expand `${VAR}` / `${VAR:-default}` from the process environment in all
        // string fields, so one committed TOML works on any machine (see the
        // env-var contract in `fuzz/setup/common.sh`).
        cfg.expand_env();
        cfg.validate()
            .with_context(|| format!("validating target config {}", path.display()))?;
        Ok(cfg)
    }

    pub fn from_str(text: &str) -> Result<TargetConfig> {
        let cfg: TargetConfig = toml::from_str(text)?;
        cfg.validate()?;
        Ok(cfg)
    }

    /// Expand `${VAR}` / `${VAR:-default}` references in every string field
    /// (paths, argv templates, extra_env values, lean backend dir) from the
    /// process environment. `{placeholder}` tokens (single braces, no `$`) are
    /// left untouched — those are the per-stage substitutions handled elsewhere.
    pub fn expand_env(&mut self) {
        expand_vec(&mut self.charon_cmd);
        expand_vec(&mut self.aeneas_cmd);
        expand_vec(&mut self.translate_flags);
        expand_vec(&mut self.checks_flags);
        expand_vec(&mut self.borrowck_flags);
        for v in self.extra_env.values_mut() {
            *v = expand_env_str(v);
        }
        if let Some(dir) = &mut self.lean_backend_dir {
            *dir = expand_env_str(dir);
        }
    }

    fn validate(&self) -> Result<()> {
        anyhow::ensure!(!self.name.is_empty(), "target `name` is empty");
        anyhow::ensure!(
            !self.charon_cmd.is_empty(),
            "target `charon_cmd` must have at least the program"
        );
        anyhow::ensure!(
            !self.aeneas_cmd.is_empty(),
            "target `aeneas_cmd` must have at least the program"
        );
        anyhow::ensure!(
            self.charon_cmd.iter().any(|a| a.contains("{input}")),
            "charon_cmd must reference {{input}}"
        );
        anyhow::ensure!(
            self.charon_cmd.iter().any(|a| a.contains("{output}")),
            "charon_cmd must reference {{output}}"
        );
        anyhow::ensure!(
            !self.translate_flags.is_empty(),
            "translate_flags must be set"
        );
        Ok(())
    }

    /// The flag set used for the fast pass; falls back to translate.
    pub fn checks_flags_or_translate(&self) -> &[String] {
        if self.checks_flags.is_empty() {
            &self.translate_flags
        } else {
            &self.checks_flags
        }
    }
}

fn expand_vec(v: &mut [String]) {
    for s in v.iter_mut() {
        *s = expand_env_str(s);
    }
}

/// Expand `${VAR}` and `${VAR:-default}` references in `s` using the process
/// environment.
pub fn expand_env_str(s: &str) -> String {
    expand_with(s, &|k| std::env::var(k).ok())
}

/// Core expander: replace every `${VAR}` / `${VAR:-default}` in `input`,
/// resolving names via `lookup`. A `${VAR}` that resolves to nothing (unset and
/// no default) expands to the empty string and logs a warning — every shipped
/// TOML should carry a `:-default`, so this only fires on a genuine typo/misuse.
/// Single-brace `{tokens}` (no leading `$`) and stray `$` are passed through
/// verbatim.
pub fn expand_with<F>(input: &str, lookup: &F) -> String
where
    F: Fn(&str) -> Option<String>,
{
    let mut out = String::with_capacity(input.len());
    let bytes = input.as_bytes();
    let mut i = 0;
    while i < input.len() {
        // Only ASCII `${` starts an expansion; everything else is copied as-is.
        if bytes[i] == b'$' && i + 1 < input.len() && bytes[i + 1] == b'{' {
            if let Some(rel) = input[i + 2..].find('}') {
                let inner = &input[i + 2..i + 2 + rel];
                let (name, default) = match inner.split_once(":-") {
                    Some((n, d)) => (n.trim(), Some(d)),
                    None => (inner.trim(), None),
                };
                match lookup(name).or_else(|| default.map(str::to_string)) {
                    Some(val) => out.push_str(&val),
                    None => eprintln!(
                        "[config] warning: `${{{name}}}` is unset and has no `:-default`; \
                         expanding to empty string"
                    ),
                }
                i += 2 + rel + 1;
                continue;
            }
        }
        // Copy one full UTF-8 char.
        let ch = input[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

/// Substitute `{key}` placeholders in an argv template.
pub fn substitute(template: &[String], vars: &[(&str, &str)]) -> Vec<String> {
    template
        .iter()
        .map(|arg| {
            let mut out = arg.clone();
            for (k, v) in vars {
                out = out.replace(&format!("{{{}}}", k), v);
            }
            out
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE: &str = r#"
name = "t"
charon_cmd = ["charon", "rustc", "--dest-file", "{output}", "--", "{input}"]
aeneas_cmd = ["aeneas"]
translate_flags = ["-backend", "lean", "{llbc}", "-dest", "{dest}"]
checks_flags = ["-backend", "lean", "-checks", "{llbc}", "-dest", "{dest}"]
borrowck_flags = ["-borrow-check", "{llbc}"]
supports_dump_pure_ir = true

[timeout_secs]
aeneas = 42

[[known_findings]]
id = "F4"
error_class = "InternalError"
message = "Internal error, please file an issue"
file = "pure/PureMicroPassesLoops.ml"
line = 1818
issue = "cryspen/aeneas#22"
"#;

    #[test]
    fn parse_sample() {
        let cfg = TargetConfig::from_str(SAMPLE).unwrap();
        assert_eq!(cfg.name, "t");
        assert!(cfg.supports_dump_pure_ir);
        // per-stage timeout: explicit override + defaults
        assert_eq!(cfg.timeout_secs.aeneas, 42);
        assert_eq!(cfg.timeout_secs.rustc, 30);
        assert_eq!(cfg.known_findings.len(), 1);
        assert_eq!(cfg.known_findings[0].line, 1818);
    }

    #[test]
    fn substitution() {
        let cfg = TargetConfig::from_str(SAMPLE).unwrap();
        let out = substitute(&cfg.translate_flags, &[("llbc", "a.llbc"), ("dest", "out")]);
        assert_eq!(out, vec!["-backend", "lean", "a.llbc", "-dest", "out"]);
    }

    #[test]
    fn expand_with_env_and_defaults() {
        let vars: std::collections::BTreeMap<&str, &str> =
            [("ROOT", "/opt/aeneas"), ("EMPTYDEF", "")].into_iter().collect();
        let lookup = |k: &str| vars.get(k).map(|v| v.to_string());

        // present var
        assert_eq!(expand_with("${ROOT}/bin/aeneas", &lookup), "/opt/aeneas/bin/aeneas");
        // missing var falls back to default
        assert_eq!(
            expand_with("${MISSING:-/tmp/fallback}", &lookup),
            "/tmp/fallback"
        );
        // present var wins over default
        assert_eq!(expand_with("${ROOT:-/nope}", &lookup), "/opt/aeneas");
        // multiple refs + literal `{placeholder}` left untouched
        assert_eq!(
            expand_with("${ROOT}/charon --dest {output} ${MISSING:-x}", &lookup),
            "/opt/aeneas/charon --dest {output} x"
        );
        // a set-but-empty var expands to empty (not the default)
        assert_eq!(expand_with("[${EMPTYDEF:-def}]", &lookup), "[]");
        // stray `$` and non-ascii pass through
        assert_eq!(expand_with("price $5 é", &lookup), "price $5 é");
    }

    #[test]
    fn config_expand_env_substitutes_all_string_fields() {
        // Unique names to avoid colliding with any other test's env.
        std::env::set_var("FUZZ_CFG_TEST_ROOT", "/opt/x");
        std::env::set_var("FUZZ_CFG_TEST_CHARON", "/opt/x/charon/bin/charon");
        let toml = r#"
name = "t"
charon_cmd = ["${FUZZ_CFG_TEST_CHARON}", "rustc", "--dest-file", "{output}", "--", "{input}"]
aeneas_cmd = ["${FUZZ_CFG_TEST_ROOT}/bin/aeneas"]
translate_flags = ["-backend", "lean", "{llbc}", "-dest", "{dest}"]
lean_backend_dir = "${FUZZ_CFG_TEST_ROOT}/backends/lean"

[extra_env]
PATH = "${FUZZ_CFG_TEST_ROOT}/charon/bin:${FUZZ_CFG_MISSING:-/usr/bin}"
"#;
        let mut cfg = TargetConfig::from_str(toml).unwrap();
        cfg.expand_env();
        assert_eq!(cfg.charon_cmd[0], "/opt/x/charon/bin/charon");
        assert_eq!(cfg.aeneas_cmd[0], "/opt/x/bin/aeneas");
        assert_eq!(cfg.lean_backend_dir.as_deref(), Some("/opt/x/backends/lean"));
        assert_eq!(cfg.extra_env["PATH"], "/opt/x/charon/bin:/usr/bin");
        // the `{output}`/`{input}`/`{llbc}` placeholders survive env expansion
        assert!(cfg.charon_cmd.iter().any(|a| a == "{output}"));
        assert!(cfg.translate_flags.iter().any(|a| a == "{llbc}"));
        std::env::remove_var("FUZZ_CFG_TEST_ROOT");
        std::env::remove_var("FUZZ_CFG_TEST_CHARON");
    }

    #[test]
    fn missing_placeholder_rejected() {
        let bad = r#"
name = "t"
charon_cmd = ["charon", "{output}"]
aeneas_cmd = ["aeneas"]
translate_flags = ["{llbc}"]
"#;
        assert!(TargetConfig::from_str(bad).is_err());
    }
}
