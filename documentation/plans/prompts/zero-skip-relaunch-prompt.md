# Zero-skip relaunch — drive c_lean from 25/89 to ~80/89

Paste into a fresh Claude Code session at
`/Users/karthik/aeneas/.claude/worktrees/diff-test` on branch
`aeneas-lean-certificate-diff-test`. Execute autonomously: commit
between steps, only stop on the documented hard-stop conditions.

---

You are resuming the zero-skip campaign from
`documentation/plans/zero-skip-plan.md`. The original framing was
"eliminate 19 `--skip-decl` flags in
`tests/lean-checker/lean-diff/scripts/run-diff.sh`"; that target has
been ~80% closed (see Status below). The campaign now has a sharper,
fleet-wide measurement: the **`c_lean` gate** in the meta-harness,
which runs `aeneas-check --out <fixture>.lean` then `lake env lean
<fixture>.lean` against the `RuntimeShim`'s `Aeneas` import. Today
it reports **25 of 89 fixtures typecheck** and **2997 of 3143 decls
fail**. Goal: close as many of those 64 failing fixtures as the
emitter clusters allow within ~3 working days.

## Boot sequence — read in order

1. `documentation/plans/zero-skip-plan.md` — the original step-by-
   step backlog. Steps 1-7 have status annotations (DONE / PARTIAL /
   open) inline. Step 4 (`closure_leak_trait_mut_self`) is the only
   step never started.
2. `documentation/plans/grust-coverage-expansion.md` §2 — the
   c_lean fleet snapshot (25/89 pass, 64 fail), failure cluster
   tallies (18 type mismatch, 11 end-namespace, 9 function-expected,
   7 parse errors, 1 field/fn collision, 18 other).
3. `tools/meta-harness/src/gates/c_lean.rs` — the gate
   implementation. You'll re-run this gate as the campaign's
   primary signal.
4. `aeneas-lean-checker/AeneasCheck/Pure/Pretty.lean` —
   `isLeanKeyword` / `sanitizeIdent` helpers landed by `0195f149`.
   Extend the keyword list as new collisions surface.
5. Recent commits on the branch:
   ```
   git log --oneline -10
   ```
   Expected top: `0195f149 aeneas-check: escape Lean keywords ...`
   atop `69dd59dc meta-harness: c_lean gate`. If HEAD doesn't
   include both, abort with a status report — something rebased
   under you.

## Status of the prior steps

| Step | Cluster | State | Notes |
|---|---|---|---|
| 0 | stale-skip cleanup | DONE | 3 mis-skipped flags removed |
| 1 | `discriminant_isize_attr` | DONE (`7e8c7ca9`) | shim attribute add |
| 2 | Box.new shim | PARTIAL (`c7286a96`) | shim binding done, cascade waits on Step 3 |
| 3 | `recursive_match_arm_scoping` | PARTIAL (`9a658c5b`) | 2 of 7 decls unlocked; 5 deferred to BLOCKED notes |
| 4 | `closure_leak_trait_mut_self` | **OPEN** | the only never-started step |
| 5 | `loop_body_undefined_locals` | PARTIAL (`a51913d6` + `a54234ff`) | wrapper-signature half landed; body-rewrite half open |
| 6 | `tail_back_closure_wrap` | PARTIAL (`d53a88aa`) | `test_choose` unlocked; `call_choose` deferred |
| 7 | `use_v_arity` | DONE (`09ea51e0`) | const-generic plumbing added |
| (new) | keyword escape | DONE (`0195f149`) | `«end»` field names |

## Primary signal — c_lean gate

Build + run the gate before any change:

```bash
cd /Users/karthik/aeneas/.claude/worktrees/diff-test
cargo build --manifest-path tools/meta-harness/Cargo.toml --release
./tools/meta-harness/target/release/meta-harness \
  --sweep tests/llbc --gates c_lean \
  --report-json /tmp/cl-before.json \
  --report-md /tmp/cl-before.md
```

Expected output today:
```
c_lean per-fixture pass: 25  fail: 64
c_lean per-decl pass:   146  fail: 2997
```

After each fix, re-run and confirm the pass count **increases**
without any previously-passing fixture regressing.

## Sequencing

Order by `(c_lean fixtures unlocked) / (fix size)`. The clusters,
prioritised by the failure-mode tallies in
`grust-coverage-expansion.md` §2:

### Cluster A — `end <ns>` namespace mismatch (11 fixtures)

The `0195f149` keyword-escape fix unblocked the *parse* error on
`structure ... end : Idx`. The 11 fixtures listed in the analysis
(e.g. `array_slice_index`, `arrays`, `assert-cfg`, `drop`,
`loops-issues`) still fail c_lean because the second-tier errors
remain. Inspect each fixture's `/tmp/lean-typecheck/<fx>.log` —
likely a mix of:

- Other Lean keywords in field / local / variant names (extend the
  `isLeanKeyword` list — `pub`, `priv`, `move`, `ref`, `mut`,
  `extern`, etc. weren't included in the conservative initial list).
- Missing `core.slice.index` / `core.slice` shim bindings —
  RuntimeShim doesn't model them. Either add the bindings (mirroring
  the existing `alloc.boxed.Box.new` pattern from Step 2) or mark
  the fixtures as "depends on full Aeneas.Std" and exclude from
  c_lean's scope via the manifest.

Estimated work: half day. Expected unlock: 5-8 fixtures.

### Cluster B — Step 4 trait `&mut self` closure-leak (untouched)

Per `zero-skip-plan.md` §Step 4: trait-impl method signatures
diverge from the trait's expected one because the impl-method
translator doesn't consult the trait's signature when shaping the
body. Affects 4 explicit decls (`demo::Counter`, `demo::Std.Usize.
Insts.DemoCounter`, `…incr`, `demo::use_counter`) plus the cascade
into `traits`, `default`, `defaulted_method`, `blanket_impl`.

Fix surface: `aeneas-lean-checker/AeneasCheck/Translate/Forward.lean`
and `Translate/Driver.lean::traitImplOfLlbcTraitImpl`. The
translator needs to read the trait method's signature when shaping
the impl-method body.

Estimated work: half-to-full day. Expected unlock: 4 demo decls +
~4 trait-impl-heavy fixtures (`traits`, `default`,
`defaulted_method`, `blanket_impl` if not already passing).

### Cluster C — "function expected" (9 fixtures)

Look at one representative failure (`as_mut` was the example given).
The Lean error `Function expected at <expr>` usually means a
non-functional value is being applied — most commonly a tuple or
struct value getting `()`-called. Likely cluster of cert-walker
bugs around back-closures / tuple-typed returns. Possibly shares
root with Step 6's `call_choose` BLOCKED note (tuple destructure at
function entry).

Estimated work: 1 day (case-by-case until the recipe transfers).
Expected unlock: 3-5 fixtures.

### Cluster D — type mismatch (18 fixtures)

The largest bucket. Likely a mix of:
- Signature reshape mismatches (R₀ vs R₁ at the Lean level)
- ADT-typed inputs falling through to `Std.U32` catch-all (the
  `llbcTyToPTyWithVars` issue from Step 5's first half — already
  partially fixed there)
- Missing trait-bound parameters

For each, the c_lean error log carries the file/line. Triage 3-4
fixtures by hand; if a recipe emerges, batch the rest. If they're
all distinct, switch to a per-fixture diary at
`zero-skip-plan.md`.

Estimated work: 1-2 days. Expected unlock: 5-10 fixtures
(realistically; some will be deep walker bugs).

### Cluster E — Step 5 body rewrite (3 decls in 1 fixture)

The deferred half from `zero-skip-plan.md` §Step 5: rewrite
`buildLoopBody` so the loop body walks as a normal function
expression and the recursive self-call becomes `cont <args>` /
`Return v` becomes `done v`. Scoped to `demo::list_nth1` and its
loop siblings.

The scaffold at
`aeneas-lean-checker/tests/Walker/loop_body_scaffold.py` documents
the exact assertion still failing.

Estimated work: ~half day if the scaffold's assertion-by-assertion
guidance holds; longer if the walker-state shape needs refactoring.
Expected unlock: 1 fixture (`demo` may already pass per
`list_nth1`'s blocking).

## Operational rules

- **Single-agent campaign.** Run sequentially through clusters A
  → E. Spin up sibling worktree agents only if a cluster genuinely
  splits into independent files.
- **Worktree isolation.** Always work in
  `/Users/karthik/aeneas/.claude/worktrees/diff-test`. Never `cd`
  to `/Users/karthik/aeneas`. For agent dispatches with
  `isolation: worktree`, the first Bash call MUST be:
  ```bash
  echo "[status] boot" && pwd && git log -1 --oneline && \
    git branch --show-current
  ```
  Abort if HEAD isn't a descendant of `aeneas-lean-certificate-
  diff-test`.
- **Stay out of `aeneas-lean-soundness/` and `aeneas-lean-checker/
  AeneasCheck/Theorems/`**. These belong to the soundness agent.
  If a cluster fix would require touching them, document the
  blocker and skip the cluster.
- **Rebuild aeneas-check after every emit change**:
  ```bash
  cd aeneas-lean-checker && lake build aeneas-check
  ```
  Stale binaries silently use old emit logic; the first symptom is
  c_lean numbers that don't change after a fix.
- **Rebuild meta-harness after any change to its sources**:
  ```bash
  cargo build --manifest-path tools/meta-harness/Cargo.toml --release
  ```

## Acceptance per cluster

After each cluster commit:

1. `lake build aeneas-check` clean (50/50 jobs).
2. `cargo test --manifest-path tests/lean-checker/differential/
   Cargo.toml --release --no-fail-fast`: existing 44 hand-written
   + 42 auto-generated tests still pass (86 total).
3. `meta-harness --sweep tests/llbc --gates c_lean,g_byte,g_rust`:
   - c_lean per-fixture pass count **increased** vs baseline.
   - g_byte per-fixture: 3 pass / 83 div / 3 skip unchanged.
   - g_rust per-fixture: at least 13 with hits, no mismatch.
4. No new entries in
   `tests/lean-checker/lean-diff/scripts/run-diff.sh`'s
   `--skip-decl` list.

If any of (1)-(3) regress, revert the cluster's commit and
document the regression in `zero-skip-plan.md`'s relevant section.

## Stopping conditions

- **Net c_lean pass count drops** at any point → revert and stop.
- **Any cluster takes >2x its estimate** → stop the cluster, commit
  what's working, document blocker, advance to next cluster.
- **3 fixtures cascade into the same deep walker bug** (e.g.
  tuple-destructure-at-entry from Step 6's `call_choose`) → stop
  the per-fixture chase, scope the deeper walker work as its own
  session, return for the next.
- **Wall time >5 working days** → stop. Even closing 1 cluster
  cleanly is a meaningful win.

## Report back

Each cluster ends with a `Step X — DONE/PARTIAL <date>` update
under `zero-skip-plan.md`, mirroring the existing entries. The
session ends with one PR-style summary covering:

- Clusters closed (full or partial) with commit hashes.
- c_lean before/after per-fixture pass counts.
- g_byte / g_rust delta (expected: unchanged).
- Architectural surprises worth flagging in the contract.
- Wall-clock time.

Local commits only on `aeneas-lean-certificate-diff-test`. Never
push.

## What this session does NOT touch

- **Meta-harness gate logic** (`g_byte`, `g_rust`, `c_lean`
  themselves). They're the measurement — don't move the goalposts.
- **`tools/meta-harness/` source code** except to fix bugs
  surfaced by the campaign (e.g. a gate misclassifying a fixture).
- **The differential crate's hand-written tests in
  `tests/lean-checker/differential/tests/diff.rs`**. Read-only.
- **The auto-generator** (`--generate-tests`, `--regen-models`).
  Their output (`diff_auto.rs`, the auto portions of `model.rs`)
  will benefit naturally as the emitter improves; don't pre-empt
  it.
- **External-crate work** (`--crate` invocations against
  libcrux-iot etc.). Separate workstream.
