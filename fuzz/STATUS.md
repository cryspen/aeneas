# Fuzzing campaign status

## Phase 0 — toolchain setup (fork done, upstream in progress)
- Branch `fuzz-harness` created off `dump-pure-ir-minimal` (uncommitted fork
  fixes left in place, uncommitted).
- Fork target VALIDATED (2026-07-26): binary `bin/aeneas` (6a3fc35b-dirty),
  charon wrapper `/Users/karthik/charon/charon/target/release/charon`
  (v0.1.196; PATH charon is 0.1.218 → rejected). F4 (PureMicroPassesLoops.ml:1818,
  InternalError) and F6 (InterpAbs.ml:1671, Unreachable; also in -borrow-check)
  both reproduce on the fork binary → acceptance-gate targets live. Flag
  differences: `-checks` replaces `-type-check-pure-code` (100x slow → verify
  path only); `-borrow-check` standalone; `-no-progress-bar` needed for clean
  stderr. Exit codes 0/1/2 (2 = crash only with backtrace present). Config:
  fuzz/targets/fork.toml.
- Upstream target VALIDATED (2026-07-26): aeneas @ main 3a8586fa built at
  /tmp/aeneas-upstream (bin/aeneas), charon pin 527ea8e3 = v0.1.225 (needs
  rustup on PATH at runtime; source file after `--`). charon-ml is vendored
  in-tree (dune workspace symlink), so no opam conflicts with the fork. F4 and
  F6 BOTH PRESENT at upstream main (empirical: F4 → PureMicroPassesLoops.ml:1818
  InternalError; F6 → InterpAbs.ml:1688 Unreachable). `-type-check-pure-code`
  exists on neither binary; `-checks` is the sanity-check flag on both. Config:
  fuzz/targets/upstream.toml.

## Phase 1 — harness + cheap oracles (DONE, gate PASSED)
- Harness built (fuzz/harness/, 41 tests green), committed bb87a51f.
- Acceptance gate PASSED: F4 (PureMicroPassesLoops.ml:1818) and F6
  (InterpAbs.ml:1671) rediscovered purely by mutating tests/src seeds (real
  provenance chains, not repro replay), minimized to single functions,
  deduped as known #22/#24.
- Gate fixes: absolutize work_root (aeneas was never being reached!),
  reclassify feature-gate craises as expected rejects, strengthen the
  F4/F6-family mutators, drop unresolvable file-local `use` on minimization.
- Candidate crash sites triaged → **1 confirmed NEW bug** (N1): assert-operand
  double-evaluation, `pub fn f(b0: bool){ assert!(b0); assert!(b0); }` crashes
  BOTH fork and upstream at InterpExpressions.ml:55 ("no bottoms"). Valid Rust,
  minimal, root-caused (eval_assertion re-evaluates the `move` cond via
  eval_assertion_concrete). Repro + issue draft: fuzz/findings/n1-assert-double-eval/.
  Verified firsthand on clean builds of both targets. Severity MEDIUM. NOT dup
  of upstream#392. → to be filed on cryspen/aeneas in the Phase 4 batch.
  The other 4 candidates: dup of AeneasVerif#804, feature-gate reject,
  F6 dup (mislabeled), and one harness false positive (a [%warn], exit 0).
- Harness fingerprinting/classification bugs found by triage (task #8): require
  nonzero-exit + real backtrace for Crash; fingerprint on exception top frame.

## Phase 2 — generator + semantic differential (in progress)
- Lean-eval oracle validated (fuzz/semdiff/, committed b7a2d184): ~3s per
  100-test crate, panic⇄fail correspondence table, overflow-checks=on for
  native ground truth, prefer while/index loops (range-for → noncomputable).
- IN PROGRESS: borrow-weighted grammar generator (gen.rs) + wiring semdiff
  into the harness (semdiff.rs), + a several-hundred-test differential run.

## Phase 3 — pure-IR evaluator + per-pass differential (evaluator done)
- pure-eval crate done (committed 16d5dc5a): monadic interpreter, all int
  widths + checked semantics, run + diff CLIs, 22 tests, zero false positives
  on ~10 fixtures + goldens after ok(())≡ok(unit) normalization.
- IN PROGRESS: stage-diff driver (sweep post-s2p vs post-micro over a corpus,
  metamorphic transforms, coverage accounting).

## Phase 4 — CI-recurring operation + reporting (harness done, campaign running)
- CI DONE (committed 3d153c04): config ${ENV} substitution, run --ci +
  --time-budget (exit 3 only on NEW findings, keyed off committed DB),
  fuzz/setup/ provisioning scripts, .github/workflows/fuzz-nightly.yml
  (nightly fast + weekly full, caching), fuzz/README.md. Exit-code contract
  proven by smoke run.
- Oracle misclassification fixed (committed c30d58ec, task #8): crash needs
  nonzero-exit + real backtrace; fingerprint anchors to the uncaught-exception
  block; richer finding statuses.
- IN PROGRESS: bug-hunt campaign on BOTH targets (stable binary copy),
  triaging any new findings.
- Remaining: file N1 on cryspen/aeneas; final triage report.

## Confirmed findings so far
- N1 (NEW, both targets): assert double-eval crash, InterpExpressions.ml:55.
  Repro + issue draft ready (fuzz/findings/n1-assert-double-eval/). To file.
- N2 (NEW, both targets): two sequential loops over a &mut-borrow iterator,
  first early-returns → loop-fixed-point join "Could not match the contexts",
  InterpJoin.ml:1515 (fork) / 1542 (upstream). Verified firsthand on both.
  To file on cryspen (applies upstream). Sibling family: break variant →
  InterpAbs.ml:2169/2188.
- N3 (fork-toolchain-only): closure reading a captured &mut →
  SymbolicToPureValues.ml:366 on fork; upstream OK. NOT filed — crash-site code
  identical fork/upstream, not the uncommitted work; charon-version vs
  upstream-since-fixed confound unresolved.
- F4/F6 re-confirmed on fork AND upstream (dedup as #22/#24). N1/F4/F6 all
  reproduce across BOTH charon versions → not charon-version artifacts.
- Non-bugs: interpborrows-1203 (dup AeneasVerif#804), interploops-407
  (feature gate), extract-2851 (harness false positive, now fixed).
- Campaign scale: ~1551 crates across both targets; 8 distinct crash sites,
  all accounted for (no other new sites).

## Phase 3 differential result
- pure-eval sweep post-s2p vs post-micro over tests/src: 2164 argsets AGREE,
  0 DISAGREE (micro-passes semantically faithful on the reachable subset).
  Coverage ~28% conclusive (non-scalar params dominate skips). Stage-diff
  driver (fuzz/stage-diff/) + metamorphic transforms: 0 disagreements.

## CAMPAIGN COMPLETE (2026-07-26) — see fuzz/FINDINGS.md for the full report
All four phases delivered and committed.
- **N1** — the campaign's one genuinely NEW, cleanly-filable bug. FILED as
  cryspen/aeneas#28 (assert double-eval, InterpExpressions.ml:55).
- **N5 (HIGH soundness)** — `iN::MIN % -1` modeled as 0 but PANICS in Rust. NOT
  a campaign discovery: found by prior MANUAL AUDITING and already fixed in
  cryspen/aeneas PR #21 (fix/rem-min-overflow, 2026-07-22), predating the
  campaign. The Phase-2 semantic differential INDEPENDENTLY REPRODUCES it
  (native panic vs Lean ok 0 → MISMATCH, verified firsthand) — an oracle-
  validation datapoint, the analogue of F4/F6 rediscovery for the crash oracle.
- **N4**: `match` on `char` → "Inconsistent state" (InterpStatements.ml:1100/
  1132), both targets. DUPLICATE of upstream #797. Not filed.
- **N2**: DUPLICATE of upstream #930 (+ #1206 break variant), verified via gh.
- **N3**: fork-toolchain-only crash, attribution unresolved → not filed.
Net genuinely-new filable from the campaign: **N1 only** (filed #28). Everything
else dedups to known fork/upstream issues (incl. N5/PR#21) or is a non-bug.
Final ledger: fuzz/FINDINGS.md.
