# Differential Testing Plan — Four-Artifact Audit

## Context

The Aeneas cert pipeline produces four distinct artifacts from a single
Rust source program. Each is a candidate for the "trusted output," and
each can disagree with the others in ways that pinpoint specific bugs.
Today's coverage is uneven: one comparison is well-tested on one
function, another on three; the remaining four comparisons have no
harness at all. This plan brings all six pairwise comparisons under a
single sweep with consistent per-fixture status reporting, so any
regression is visible against any artifact.

The motivating insight: **when artifacts agree, you've collected
evidence; when they disagree, the disagreement itself is a precise bug
report.** A divergence between mainline Aeneas Lean and our Lean
backend on a single function tells you exactly which translation step
diverged from a battle-tested baseline. A divergence between original
source Rust and emitted Rust tells you exactly which OCaml interpreter
hint or Pure-IR translation drifted from real Rust semantics. The four
artifacts give us four oracles; with sweep coverage we get four
independent opinions per fixture.

## The four artifacts

For a given fixture `tests/src/<crate>.rs`:

| # | Artifact | Producer | Path | Purpose |
|---|---|---|---|---|
| **R₀** | Original source Rust | the developer | `tests/src/<crate>.rs` | Ground truth — what the program was written to compute |
| **R₁** | Emitted Rust ("model") | `aeneas-check --rust-model <out.rs>` (our cert pipeline's Rust backend) | `tests/lean-checker/differential/src/model.rs` | Transliteration of the cert-extracted Pure IR back into Rust — used as a differential-test oracle, not as a faithful retranslation. Mutability erased, `Result` dropped, slices → `Vec<T>` per the M8 conventions. |
| **L₀** | Aeneas backend Lean | mainline OCaml `aeneas -backend lean` | per-fixture `.lean` file emitted under `-dest <dir>` | The trusted baseline. Years of upstream use; the de facto correctness oracle for Lean output. |
| **L₁** | Our backend Lean | `aeneas-check --out <out.lean>` (our cert pipeline's Lean backend) | per-fixture `.lean` file | The new, cert-verified Lean output. Should equal L₀ in spirit (the whole point of the cert pipeline is to produce L₀-equivalent output via a verifiable path). |

R₀ is the **input** to all three producers; R₁, L₀, L₁ are **outputs**.
The four sit at distinct trust levels:

```
        R₀  (developer-authored; trusted as the spec)
        │
        ├──[Charon → OCaml interp]──► cert.json ──► R₁  (cert pipeline, our Rust backend)
        │                                       └──► L₁  (cert pipeline, our Lean backend)
        │
        └──[Charon → OCaml backend]──────────────► L₀  (mainline Aeneas, trusted)
```

## The six pairwise comparisons

Four of the six pairs are independently informative; the other two are
implied by transitivity on shared inputs. We invest in **four primary
gates** and treat the implied pairs as bonus coverage if cheap.

| Pair | Comparison | What it tells us | Status today |
|---|---|---|---|
| **G_rust** | R₀ ↔ R₁ | Cert pipeline's Rust output matches developer intent | 39 proptests / 11 fixtures (in `tests/lean-checker/differential/`); needs scaling |
| **G_lean** | R₀ ↔ L₁ | Cert pipeline's Lean output matches developer intent (semantic check, end-to-end) | 224 vectors / 6 fixtures (in `tests/lean-checker/lean-diff/`); needs scaling |
| **G_byte** | L₀ ↔ L₁ (byte-equal) | Our Lean backend produces the same source as mainline (cheap syntactic check) | `scripts/compare-backends.sh` exists; per-fixture, opt-in; no allowed-divergence list |
| **G_rfl** | L₀ ↔ L₁ (definitional equality, `rfl`) | Our Lean's *meaning* matches mainline's, even where syntax differs (e.g. binder order, beta-equivalence) | Does not exist; this plan adds it |
| (implied) | R₀ ↔ L₀ | Mainline Aeneas's Lean matches developer intent | Trusted via upstream test suite; we don't add separate coverage |
| (implied) | R₁ ↔ L₁ | Our Rust and Lean outputs agree | Falls out of G_rust + G_lean (both go through R₀) |

We also keep two compilation gates that already exist and a new one to
add:

| Compilation gate | What | Status |
|---|---|---|
| `C_rust` | Emitted R₁ compiles (`cargo check`) | Implicit in cargo test; we'll make it explicit |
| `C_lean_ours` | Emitted L₁ compiles (`lake build GeneratedTests`) | Exists as gate G3 in the M9/M10 plans |
| `C_lean_aeneas` | Emitted L₀ compiles | Trusted via mainline CI |

## Primary gate definitions

### G_rust — Source Rust ↔ Emitted Rust (proptest)

**Mechanism.** Existing differential harness at
`tests/lean-checker/differential/`. Per fixture:

1. `aeneas-check --rust-model /tmp/<crate>_model.rs <crate>.cert.json`
2. Copy the relevant `<fn>_model` functions into
   `tests/lean-checker/differential/src/model.rs`.
3. Add a `<fn>_ref` reference in `src/lib.rs` that calls the source
   Rust function from `tests/src/<crate>.rs` (copy the `pub fn` body
   in or use `#[path]`).
4. Add a proptest in `tests/diff.rs` of the form
   `prop_assert_eq!(<fn>_ref(x), <fn>_model(x))`.
5. `cargo test --release` runs the proptest with random inputs.

**Coverage criteria.** A fixture passes G_rust if every `pub fn` in
the source whose signature is differential-testable (primitive inputs,
no closures, no dyn traits) has a passing proptest. Functions that
*can't* be differential-tested (closures, generics with unbound type
params, ADTs without `Arbitrary` instances, slices with semantic gaps)
are listed in `tests/lean-checker/differential/known-divergent.md`
with a one-sentence reason.

**Known unblockers.** Emitter quirks (RustEmit) that currently block
fixtures from passing should be filed as separate emitter-bug tickets.
Resolved on this branch:
- `3d086b79` — brace-decorated paths (`core::num::{u32}::wrapping_add`); unblocks `compare_simple::add_u32`, `calls::pick`, parts of `builtin`.
- `ac176ee3` + `df1441cd` (Phase 1C) — ADT placeholders: `record_lit { … }` and `with_<field>(base, value)` now render as real `Foo { f: e, … }` and `Foo { f: v, ..base }` syntax via plumbed `adtName` on `PExpr.recordLit` / `PExpr.structUpdate`. Unblocks `aggregates_basic`, `reborrows::set_fst` and other ADT-heavy fixtures.
- `c84781e4` (Session 4 / Phase 4b-4b) — variant-ctor path rewrite: `PExpr.toRust` introduces `rustifyPath` (sanitize braces + `.` → `::`) and applies it to `.var` (nullary ctor) and `.app` head (payload ctor). Unblocks `enums_basic::flip`, `enums_payload::{value,wrap,zero}`.

Remaining: generic binders on `<T,U>` functions; `Array.update` rendered as Lean dot-notation instead of `Array::update(…)` (surfaces in `reborrows::set_idx_model`); the cast emitter drops the `as` op (`x as u16` emits as bare `x`, so `cast_*` fixtures in `no_nested_borrows` produce ill-typed Rust); branch-variable confusion in `get_max` / similar (`if x1 { x1 } else { x2 }` where the if-cond should be the precomputed bool `t0`).

### G_lean — Source Rust ↔ Our Lean (executed)

**Mechanism.** Lake project at `tests/lean-checker/lean-diff/`. Per
fixture:

1. `aeneas-check --out tests/lean-checker/lean-diff/generated/<crate>.lean`
2. The `LeanDiff` executable imports the generated module, runs each
   function on hardcoded test vectors, and prints one byte-stable line
   per vector: `<fixture>::<fn>(args) = ok <decimal>`.
3. A sibling `rust-runner/` cargo project produces byte-identical
   lines for the same inputs by calling the source Rust function
   in-process.
4. `scripts/run-diff.sh` diffs the two streams; exit code 0 iff
   identical.

**Why hardcoded vectors instead of proptest.** The Lean side runs as
a compiled binary that's invoked once per sweep; per-input subprocess
overhead would make random testing slow. The hardcoded vectors are
selected per-function to exercise: zero, one, max, overflow boundary
(for arithmetic); empty, single-element, full (for slices/arrays);
both branches (for if/match). A later iteration can move to
JSON-stdin proptest if the per-fixture variant explosion warrants it.

**Coverage criteria.** A fixture passes G_lean if every `pub fn` in
the source has at least 4 vectors covered (or its full input domain
if smaller). Same exclusion list as G_rust for non-testable functions.

**Known unblockers.** Resolved on this branch:
- `6438a751` (Phase 1A) — `RuntimeShim` gained `#isize` / `#i32` / `#i64` macros; the hand-patch in `tests/Generated/Bitwise.lean` was reverted. `bitwise.rs` is now wired into the lean-diff harness (30 vectors passing, byte-identical).
- `ac176ee3` + `f26cc772` (Phase 1B) — `LeanEmit` now emits a type-correct zero of the field type when the root expression is a default `0#u32` placeholder and the projected field type is a literal int/bool. `unwrap_y` and `get_z1` are well-typed (`ok 0#i32` instead of `ok 0#u32.value`).
- `f23a6175` (Phase 4a-1) — `RuntimeShim` gained `HAdd`/`HSub`/`HMul I32 I32 (Result I32)` instances; `constants::add` (`i32`) now elaborates.
- `e03f1aa5` (Phase 4a-2) — `LeanEmit.sanitizeCallName` switched to a balanced-brace walker mirroring `RustEmit.sanitizeRustPath`; `def {constants.Wrap<T>}.new` → `def Wrap.new` and the call-site `constants.{constants.Wrap<T>}.new` → `constants.Wrap.new`. Applied symmetrically at the def-head in `Decl.toLean`.
- `c59c91ed` (Phase 4a-3 + Phase 4a-5) — tdm-aware ADT placeholder + caller-decl topological sort. `static S3: Pair<u32, u32> = P3` now emits `ok { x := 0#u32, y := 0#u32 }` (typechecks against `Result (Pair U32 U32)` — value still placeholder); `V.LEN : Result Usize` emits `ok 0#usize` (was the U32-typed catch-all); `def Y` (line 42 source) now emits *after* its dependency `def Wrap.new` (line 55 source) via the DFS sort over caller decls.
- `fede2492` (Phase 4a wire-in) — `constants.lean` is wired into the lean-diff harness; the runner exercises the subset of fns whose emit is non-placeholder (incr, add, mk_pair0, plus 7 nullary const/static evaluations).
- `6539a087` (Session 4 / Phase 4b-1) — `scalars.lean` wired in. Pure-binop let-bind fix in `Pretty.lean` (detect `BitXor`/`BitAnd`/`BitOr` + comparisons in `letIn` RHS, emit `let t := …` instead of `let t ← …`). Shim adds: `HShift{L,R} {U32,I32} I32 (Result …)`, `HAdd/Sub/Mul Isize Isize (Result Isize)`, `core.num.I32.wrapping_{add,sub,mul}`, `core.num.{U32,I32}.rotate_{left,right}`, `core.default.{U32,I32}.default`, `CoeHead U32→U16 / U16→U32 / U32→I16 / I16→U32` (cast placeholders). G_lean: 119 → 224 vectors.

Remaining for the next session (cert-walker-level, not LeanEmit):
- The `S3`-class placeholders are syntactically valid but semantically wrong (`{ x := 0, y := 0 }` vs the source `P3 = { x: 0, y: 1 }`). The cert event walker is dropping the right-hand side; pinning it down requires a Charon-cert-event-side patch.
- `demo.lean` needs more than the let-bind fix: `@[discriminant isize]` attribute (currently unknown), `Counter` trait impl signature mismatch (`incr : Self → Result Std.Usize` declared vs `Self → Result (Usize × (Unit → Usize))` emitted), broken bodies for closure-returning `choose` / `list_nth` / `list_nth_mut` / `list_tail`, undefined variables `s33` / `t3` in `list_nth1_loop.body` and `i32_id`. These are M12.2a-placeholder territory; wire-in deferred.

### G_byte — Mainline Lean ↔ Our Lean (byte diff)

**Mechanism.** Extend `scripts/compare-backends.sh` from its current
single-fixture interactive mode to a sweep mode:

```bash
scripts/compare-backends.sh --sweep
# For each tests/src/*.rs:
#   1. aeneas -backend lean -dest /tmp/aeneas-out/  → L₀
#   2. aeneas-check --out /tmp/checker-out/         → L₁
#   3. diff -u L₀ L₁ → record pass / divergent / fail
# Output: per-fixture status table + bytes-diffed count.
```

**Allowed-divergence list.** Some L₀ ↔ L₁ differences are known and
harmless (whitespace, comment order, banner differences, hand-rolled
trait-instance ordering). Maintain
`scripts/compare-backends-known-divergent.txt` listing
`<fixture>:<reason>` for each accepted divergence. The list shrinks
as the cert pipeline converges. CI fails only on un-listed divergence.

**Coverage criteria.** A fixture passes G_byte if its L₀ and L₁ are
either byte-identical or covered by an entry in
`known-divergent.txt`. Convergence target: byte-equal coverage rises
over time; divergence list shrinks. Both numbers reported per sweep.

**Why this is cheap and useful.** Byte-equality is a strong signal: if
L₀ and L₁ are textually equal, then any property mainline's Lean
satisfies, ours does too. The 89-fixture sweep already runs cert
pipeline and lake build; adding a parallel mainline emit + diff is
linear additional time. Catches regressions instantly.

### G_rfl — Mainline Lean ↔ Our Lean (definitional equality)

**Mechanism.** A new harness at `tests/lean-checker/lean-rfl/` (or
extend `lean-diff/`). Per fixture:

1. Emit L₀ to `tests/lean-checker/lean-rfl/aeneas-out/<crate>.lean`
2. Emit L₁ to `tests/lean-checker/lean-rfl/checker-out/<crate>.lean`
3. Generate (mechanically) a test file
   `tests/lean-checker/lean-rfl/Test/<Crate>.lean`:
   ```lean
   import «aeneas-out».«crate»
   import «checker-out».«crate»
   namespace AeneasOut := «aeneas-out».«crate»
   namespace CheckerOut := «checker-out».«crate»
   example : AeneasOut.foo = CheckerOut.foo := by rfl
   example : AeneasOut.bar = CheckerOut.bar := by rfl
   -- one example per public def
   ```
4. `lake build` the test files. Any failed `rfl` is a divergence.

**Fallback tactics for failed `rfl`.** `rfl` is strict definitional
equality. If two outputs differ by something Lean's kernel can reduce
(e.g. beta, eta, iota), `rfl` still works. If they differ by
something the kernel can't reduce (e.g. `let`-introduction order, a
swapped binder), use `decide` for closed terms or
`by simp; rfl` for ones with simple normalization. Anything that
needs more than that is a *real* divergence, not just syntax noise.

**Coverage criteria.** A fixture passes G_rfl if every public def has
an `rfl` (or sanctioned-tactic) proof of equality. Same allowed-
divergence list pattern as G_byte: unprovable equalities go on a list
with reasons.

**Why this is strictly stronger than G_byte.** Two Lean terms can be
byte-different (G_byte fails) but definitionally equal (G_rfl
passes). Common cases: different binder names, different `let`-vs-
inline choices, different (but equivalent) instance synthesis. G_rfl
catches these as equivalent; G_byte flags them as divergent.
Conversely, two terms can be byte-identical (G_byte passes) and
`rfl`-equal trivially (G_rfl passes for free). So G_rfl subsumes
G_byte in correctness but not in convenience: G_byte is faster to run
and produces actionable diffs; G_rfl is slower (requires Lake build)
and produces "passes" or "kernel error" with less surgical info.

Run both. G_byte for fast feedback in the inner dev loop; G_rfl for
the merge-blocker gate.

## Compilation gates

These exist alongside the differential gates and are cheap to maintain:

- **C_rust**: `cd tests/lean-checker/differential && cargo check
  --release` per sweep. Already implicit in `cargo test`; surface as
  its own pass/fail so emitter-parse bugs are distinguishable from
  semantic-equivalence failures.
- **C_lean_ours**: `cd aeneas-lean-checker && lake build
  GeneratedTests` (existing gate G3 from the M9/M10 plans). Validates
  L₁ compiles against `RuntimeShim`. **Important caveat surfaced by
  the Lean-diff agent:** `RuntimeShim` is a thin stand-in for the
  real `backends/lean/Aeneas/Std`; semantic differences exist (e.g.
  shim's U32 add returns `.ok wrapping` while the real runtime errors
  on overflow). Add a G3-prime that builds against the real runtime
  for at least the lean-diff-covered fixtures.
- **C_lean_aeneas**: mainline `aeneas -backend lean` followed by a
  Lake build against `backends/lean/Aeneas/Std`. Mainline already has
  this; we re-run on the same fixture set for consistency.

## Harness layout (target end-state)

```
tests/lean-checker/
├── differential/              # G_rust (existing; scale to ~30 fixtures)
│   ├── Cargo.toml
│   ├── src/{lib.rs, model.rs}
│   ├── tests/diff.rs
│   └── known-divergent.md
├── lean-diff/                 # G_lean (existing; scale to ~30 fixtures)
│   ├── lakefile.lean
│   ├── generated/<crate>.lean
│   ├── LeanDiff/<Crate>Runner.lean
│   ├── rust-runner/{Cargo.toml, src/main.rs}
│   ├── scripts/run-diff.sh
│   └── known-divergent.md
├── lean-rfl/                  # G_rfl (new)
│   ├── lakefile.lean
│   ├── aeneas-out/<crate>.lean
│   ├── checker-out/<crate>.lean
│   ├── Test/<Crate>.lean
│   └── known-divergent.txt
└── sweep/                     # The orchestrator (new)
    ├── run-sweep.sh           # runs all 4 gates over all fixtures
    ├── report.sh              # collates per-fixture, per-gate status
    └── fixtures.list          # canonical list (subset of tests/src/*.rs)
```

And alongside:

```
scripts/
├── compare-backends.sh                       # G_byte (existing; extend to --sweep)
└── compare-backends-known-divergent.txt      # G_byte allowed divergences (new)
```

## Per-fixture coverage matrix

`tests/lean-checker/sweep/report.sh` produces a Markdown table:

```
Fixture          | C_rust | C_lean | G_rust | G_lean | G_byte | G_rfl
---              | ---    | ---    | ---    | ---    | ---    | ---
incr_cert        |   ✓    |   ✓    |  2/2   |  16/16 |   ✓    |  2/2
constants        |   ✓    |   ✓    |  3/3   |   N/A* |   ✓    |  3/3
bitwise          |   ✓    |   ✗*   |  5/5   |   N/A* |   ✓    |  ✗*
compare_simple   |   ✓    |   ✓    |  3/3   |  22/22 |   ✓    |  3/3
calls            |   ✓    |   ✓    |  1/1   |  22/22 |   ✓    |  1/1
arrays           |   ✗    |   ✓    |   —    |   —    |   —    |   —
…
```

Asterisks reference notes below the table explaining accepted gaps
(`*emitter generates #isize, RuntimeShim missing macro`, etc.).

This matrix is the single most useful artifact for "what's the state
of the pipeline?" — a contributor can scan one screen and see exactly
which fixtures are clean and which are blocked.

## Phased rollout

The plan recovers from a strong existing base (G_rust at 5 fixtures /
11 proptests, G_lean at 3 fixtures / 60 vectors) and builds out. In
priority order:

### Phase 0 — Recover lost work (~1 day)

The first Rust differential agent's worktree was cleaned without
committing; its 11 proptests across 5 fixtures need to be redone on
this branch. Dispatch an agent against the new `aeneas-lean-
certificate-diff-test` branch with the same scope as before, plus the
2 newly-unblocked fixtures (`compare_simple::add_u32`, `calls::pick`)
made possible by commit `3d086b79`.

### Phase 1 — File the surfaced emitter bugs (~1 day)

Three concrete bugs were surfaced by Phase 0 / the Lean-diff agent:

1. **`LeanEmit` generates `16#isize` but `RuntimeShim` only registers
   `#usize` / `#u32` macros.** Blocks `bitwise.rs` in G_lean. The
   committed `aeneas-lean-checker/tests/Generated/Bitwise.lean` was
   hand-patched to `(16 : Std.Isize)`, masking the drift from gate G3.
   Either fix the emitter to use the parenthesised form or extend the
   shim.
2. **`LeanEmit` generates ill-typed constants in `constants.lean`** —
   `def unwrap_y : Result Std.I32 := do ok 0#u32.value`. Constant
   evaluation of `Z1::Z1::Y` and `S1`/`S2` constant-shape rendering
   look broken.
3. **`RustEmit` placeholders** — `record_lit { … }` and
   `with_<field>(base, value)` require hand-written shims and block
   ADT fixtures in G_rust. Decide whether to (a) implement real ADT
   support in the Rust model emitter or (b) accept these as
   permanently-skipped in `known-divergent.md`.

Each is a one-agent-job sized fix.

### Phase 2 — Build G_byte sweep mode (~2 days)

Extend `scripts/compare-backends.sh` to take a `--sweep` flag that
runs over all fixtures, produces per-fixture pass/divergent/fail
status, and respects `compare-backends-known-divergent.txt`. Initial
population of the known-divergent list will be 30+ entries (the cert
pipeline differs from mainline in many small ways at the syntactic
level). Plan for the list to shrink quarterly as the cert pipeline
converges.

### Phase 3 — Build G_rfl harness (~3 days)

New `tests/lean-checker/lean-rfl/` Lake project. The hard part isn't
the `rfl` proofs themselves — those are one-liners — but the
mechanical generation of the test files from the two emit outputs.
Build a small driver (Lean or shell) that walks both directories and
produces matched test files.

### Phase 4 — Scale G_rust and G_lean to ~30 fixtures each (~1 week)

Mostly mechanical per-fixture work. ~25 LOC Lean glue + ~15 LOC Rust
mirror per fixture for G_lean; ~30 LOC per fixture for G_rust. The
unblockers (Phase 1) determine how many of the 89 fixtures are
reachable; realistic target is 30–40 covered, the rest in
`known-divergent.md`.

### Phase 5 — Single-command sweep + CI (~2 days)

Build `tests/lean-checker/sweep/run-sweep.sh` that runs all four
gates + both compilation gates + emits the per-fixture matrix.
Integrate into CI as a non-blocking weekly job initially; promote to
blocking once divergence lists stabilize.

## Bug surfacing as a feature

Different divergences map cleanly to different bugs:

| G_rust fails, G_lean passes | RustEmit bug; LeanEmit is OK |
| G_rust passes, G_lean fails | LeanEmit bug or `RuntimeShim` semantic gap |
| Both fail same way | Upstream (cert format, OCaml interp, Pure-IR) bug |
| Both fail differently | Two independent bugs; investigate both |
| G_byte passes, G_rfl fails | Kernel sees them as different; likely an instance-synthesis ordering issue |
| G_byte fails, G_rfl passes | Syntactic divergence with no semantic content; add to allowed-divergence list |
| G_byte fails, G_rfl fails | Real divergence between cert and mainline Lean backends; high-priority fix |

The matrix tells you *where* to look without having to read the
divergent output line-by-line. This is the operational payoff of
running four gates instead of one.

## CI integration

Today: G1 (vertical slice on `incr_cert`) + G2 + G3 + G4 (89-fixture
sweep on Lean replayer/emit) run per-PR. Adding the diff gates:

- **Per-PR (fast)**: G_byte sweep, C_rust, C_lean_ours. Each runs in
  < 5 minutes once warm. Blocking.
- **Per-PR (slow lane)**: G_rust + G_lean proptests on the
  Phase-4-covered fixture subset. ~10 minutes. Blocking.
- **Nightly**: G_rfl on all covered fixtures (Lake build can be 5+
  minutes per fixture). Non-blocking; surfaces regressions for the
  morning standup.
- **Weekly**: full sweep with all gates, including
  expected-failure fixtures, producing the coverage matrix. Posted
  to a dashboard or pinned issue.

CI artifacts:
- Per-PR: pass/fail counts + diff against main's allowed-divergence
  list.
- Nightly: full matrix as a build artifact.
- Weekly: pinned issue updated in-place with the matrix.

## Open questions

1. **Is the source Rust always a fair reference?** For functions
   whose semantics depend on the runtime (e.g. allocator behaviour,
   panic-on-overflow vs wrapping), source Rust may not match what the
   emitted Lean computes. The `RuntimeShim` overflow gap is one
   example: real Rust `u32::wrapping_add` doesn't error; emitted Lean
   against the shim returns `.ok wrap`; emitted Lean against the
   real `Aeneas.Std` returns `.error .overflow`. Decide per-function
   which runtime semantics is the reference; document in
   `known-divergent.md`.

2. **What about non-deterministic functions?** Some fixtures use
   `HashMap` (insertion order) or other sources of non-determinism.
   These can't be byte-compared on output values. Likely answer: skip
   for differential gates, rely on G_byte + G_rfl for structural
   equivalence.

3. **Should we generate test vectors from cert events?** The cert
   already records every input/output pair the OCaml interpreter saw
   during symbolic execution. Reusing those as G_lean vectors would
   give "free" coverage without hand-curating each fixture.
   Architectural cleanliness question: does this make the cert do
   double duty as a test oracle?

4. **What about backward closures and effect tracking?** Pair G_rust
   doesn't handle backward closures (the M12.2a placeholder). Pair
   G_lean might — backward functions are first-class in Pure IR. If
   so, G_lean has a natural advantage on closure-heavy fixtures;
   accept that and skip those in G_rust permanently.

5. **Mainline `aeneas -backend lean` is the trusted oracle, but
   *is* it always correct?** Years of upstream use is strong evidence
   but not a proof. If G_rfl fails consistently between mainline and
   cert pipeline on a fixture, the right move might be to file a
   mainline bug rather than auto-blaming the cert pipeline. Make this
   a triage convention.

## Critical files

For implementation, in priority order:

- `tests/lean-checker/differential/` — existing G_rust harness; expand
- `tests/lean-checker/lean-diff/` — existing G_lean harness; expand
- `scripts/compare-backends.sh` — existing G_byte interactive driver;
  add `--sweep` mode
- `tests/lean-checker/lean-rfl/` (new) — G_rfl harness
- `tests/lean-checker/sweep/` (new) — orchestrator
- `aeneas-lean-checker/AeneasCheck/Backends/RustEmit.lean` — three
  pending emitter fixes (Phase 1)
- `aeneas-lean-checker/AeneasCheck/Backends/LeanEmit.lean` — two
  pending emitter fixes (Phase 1)
- `aeneas-lean-checker/RuntimeShim/Aeneas/Std.lean` — semantic-gap
  documentation; `#isize` macro addition

## Verification

The plan is itself testable. End-to-end:

```bash
cd /Users/karthik/aeneas

# After Phase 5 lands:
bash tests/lean-checker/sweep/run-sweep.sh
# Produces:
# - per-fixture matrix to stdout
# - JSON status to /tmp/aeneas-sweep/results.json
# - exits non-zero if any gate has un-allowed regressions

# To check a single fixture:
bash tests/lean-checker/sweep/run-sweep.sh --fixture incr_cert

# To regenerate the known-divergent lists from current state:
bash tests/lean-checker/sweep/run-sweep.sh --regen-divergent
# Edit the lists to add reasons; commit.
```

The matrix itself is the verification: every cell is green or has an
asterisked-and-explained gap. There is no "we think it works" — there
is only "the sweep was green on commit X."
