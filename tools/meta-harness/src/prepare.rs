//! Front-end stages that resolve a `--crate <Cargo.toml dir>` or
//! `--llbc <path>` input into a `.cert.json` the rest of the harness
//! consumes. For `--cert <path>`, this module is a no-op pass-through.

use anyhow::{Context, Result, bail};
use std::path::{Path, PathBuf};
use std::process::Command;

/// Resolved intermediate artefacts for one input. `cert_path` is what
/// the gates read; `llbc_path` is preserved for diagnostic use when
/// the cert came from a `--llbc` or `--crate` invocation.
pub struct Prepared {
    pub cert_path: PathBuf,
    pub llbc_path: Option<PathBuf>,
    /// Holds the tempdir alive until `Prepared` drops; intermediate
    /// `.llbc` / `.cert.json` files vanish with it (unless the user
    /// passed `--work-dir`, in which case the field is `None`).
    pub _tmp: Option<tempfile::TempDir>,
}

/// Drive `charon cargo --preset=aeneas --dest-file=…` then
/// `aeneas -emit-cert …` on a Cargo crate root. The crate must
/// contain a `Cargo.toml` directly.
pub fn from_crate(
    crate_dir: &Path,
    charon: &Path,
    aeneas: &Path,
    work_dir: Option<&Path>,
) -> Result<Prepared> {
    let manifest = crate_dir.join("Cargo.toml");
    if !manifest.is_file() {
        bail!(
            "--crate: no Cargo.toml at {} (got {})",
            crate_dir.display(),
            manifest.display()
        );
    }

    let (out_dir, tmp_holder) = resolve_work_dir(work_dir)?;
    let crate_stem = crate_dir
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("crate")
        .to_string();
    let llbc_path = out_dir.join(format!("{crate_stem}.llbc"));
    let cert_path = out_dir.join(format!("{crate_stem}.cert.json"));

    eprintln!(
        "[meta-harness] charon cargo --preset=aeneas → {}",
        llbc_path.display()
    );
    let out = Command::new(charon)
        .current_dir(crate_dir)
        .arg("cargo")
        .arg("--preset=aeneas")
        .arg("--dest-file")
        .arg(&llbc_path)
        .output()
        .with_context(|| format!("running charon at {}", charon.display()))?;
    if !out.status.success() {
        bail!(
            "charon cargo failed for {}\n--- stderr ---\n{}",
            crate_dir.display(),
            String::from_utf8_lossy(&out.stderr)
        );
    }
    if !llbc_path.is_file() {
        bail!(
            "charon claimed success but {} doesn't exist",
            llbc_path.display()
        );
    }

    run_emit_cert(aeneas, &llbc_path, &cert_path)?;

    Ok(Prepared {
        cert_path,
        llbc_path: Some(llbc_path),
        _tmp: tmp_holder,
    })
}

/// Run `aeneas -emit-cert <llbc>` on a pre-built LLBC. Charon stage
/// is skipped.
pub fn from_llbc(
    llbc_path: &Path,
    aeneas: &Path,
    work_dir: Option<&Path>,
) -> Result<Prepared> {
    if !llbc_path.is_file() {
        bail!("--llbc: file not found at {}", llbc_path.display());
    }
    let (out_dir, tmp_holder) = resolve_work_dir(work_dir)?;
    let stem = llbc_path
        .file_stem()
        .and_then(|n| n.to_str())
        .unwrap_or("crate")
        .to_string();
    let cert_path = out_dir.join(format!("{stem}.cert.json"));
    run_emit_cert(aeneas, llbc_path, &cert_path)?;
    Ok(Prepared {
        cert_path,
        llbc_path: Some(llbc_path.to_path_buf()),
        _tmp: tmp_holder,
    })
}

fn run_emit_cert(aeneas: &Path, llbc: &Path, expect_cert: &Path) -> Result<()> {
    eprintln!(
        "[meta-harness] aeneas -emit-cert {} → {}",
        llbc.display(),
        expect_cert.display()
    );
    // aeneas writes the cert next to the llbc by default (e.g.
    // `/tmp/foo.llbc` → `/tmp/foo.cert.json`), not at the path we
    // specify. So we run from the llbc's parent and let it land
    // beside, then verify the path matches.
    let out = Command::new(aeneas)
        .arg("-emit-cert")
        .arg(llbc)
        .output()
        .with_context(|| format!("running aeneas at {}", aeneas.display()))?;
    if !out.status.success() {
        bail!(
            "aeneas -emit-cert failed for {}\n--- stderr ---\n{}",
            llbc.display(),
            String::from_utf8_lossy(&out.stderr)
        );
    }
    // aeneas writes to <llbc-stem>.cert.json next to the llbc.
    let auto_cert = llbc.with_extension("cert.json");
    if !auto_cert.is_file() {
        bail!(
            "aeneas claimed success but {} doesn't exist",
            auto_cert.display()
        );
    }
    if auto_cert != expect_cert {
        std::fs::rename(&auto_cert, expect_cert).with_context(|| {
            format!(
                "renaming {} → {}",
                auto_cert.display(),
                expect_cert.display()
            )
        })?;
    }
    Ok(())
}

fn resolve_work_dir(
    user: Option<&Path>,
) -> Result<(PathBuf, Option<tempfile::TempDir>)> {
    match user {
        Some(p) => {
            std::fs::create_dir_all(p)
                .with_context(|| format!("creating --work-dir {}", p.display()))?;
            Ok((p.to_path_buf(), None))
        }
        None => {
            let tmp = tempfile::Builder::new()
                .prefix("meta-harness-")
                .tempdir()?;
            Ok((tmp.path().to_path_buf(), Some(tmp)))
        }
    }
}
