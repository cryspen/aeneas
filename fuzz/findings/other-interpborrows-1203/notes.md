# other-interpborrows-1203

## Fingerprint

- class: Other
- site: interp/InterpBorrows.ml:1203
- message: Can't end abstraction 16 as it is set as non-endable
- top frame: Aeneas__InterpBorrows.end_abs_aux.(fun) @ interp/InterpBorrows.ml:1203

## Provenance / oracle

provenance: seed_file=/Users/karthik/aeneas/tests/src/issue-804-closure-return-ref.rs orig=each_ref mutations=[IntEdge, IntEdge]
oracle: crash[Other InterpBorrows.ml:1203]

## Triage (2026-07-26)

See `verified.md`. Verdict: **class C — DUPLICATE of AeneasVerif/aeneas#804**
(closure returning refs via `array::from_fn`). Real sanity-check crash on the
FORK toolchain (charon v0.1.196) at InterpBorrows.ml:1203; **does NOT reproduce
on current upstream** (charon v0.1.225 axiomatizes `array::from_fn`). Not a new
bug. `min.rs` cleaned to the 1-element form; closure is essential (manual
`[&s[0]]` does not crash). Not fork-induced.

