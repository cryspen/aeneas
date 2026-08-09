# other-interpexpressions-55

## Fingerprint

- class: Other
- site: interp/InterpExpressions.ml:55
- message: There should be no bottoms in the value
- top frame: Aeneas__InterpExpressions.read_place_check @ interp/InterpExpressions.ml:55

## Provenance / oracle

provenance: seed_file=/Users/karthik/aeneas/tests/src/assert-cfg.rs orig=assert_b0_and_not_b1 mutations=[StmtSwap, StmtDup, StmtDup]
oracle: crash[Other InterpExpressions.ml:55]

## Triage (2026-07-26)

See `verified.md`. Verdict: **class A — REAL, genuinely NEW bug** (not F1-F6 /
#22-#24 / #804). Crashes on FORK **and UPSTREAM** at InterpExpressions.ml:55.
Root cause: `eval_assertion` double-evaluates a `move` assert operand — it reads
once, then (concrete-bool path) `eval_assertion_concrete` calls `eval_operand`
again on the post-move context, reading the ⊥. Triggered by asserting the same
bool twice. `min.rs` minimized to `assert!(b0); assert!(b0);`. **File on
cryspen/aeneas.**

