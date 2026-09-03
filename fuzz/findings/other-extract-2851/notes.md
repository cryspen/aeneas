# other-extract-2851

## Fingerprint

- class: Other
- site: extract/Extract.ml:2851
- message: 
- top frame: n/a

## Provenance / oracle

provenance: seed_file=/Users/karthik/aeneas/tests/src/string-chars.rs orig=collect mutations=[StmtDup]
oracle: crash[Other Extract.ml:2851]

## Triage (2026-07-26)

See `verified.md`. Verdict: **INVALID — NOT A CRASH.** `Extract.ml:2851` is a
`[%warn]` (missing builtin model for `Iterator::collect`); aeneas exits 0 and
generates `Crate.lean`. Harness false-positive: the oracle matched the
`Compiler source: ... line` marker that `[%warn]` also prints. Benign on fork
and upstream. No bug.

