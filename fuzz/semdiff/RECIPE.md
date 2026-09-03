# Phase-2 Semantic-Differential Oracle — Lean side (validated recipe)

Compare **native Rust execution** (ground truth: which `assert!`s pass, which
panic) against **Lean evaluation of the Aeneas translation**, per closed
deterministic `test_*()` function. A divergence (native says OK, Lean says
fail — or vice-versa) is a candidate Aeneas bug.

```
 SRC.rs ──charon──▶ .llbc ──aeneas──▶ Crate.lean ──lake env lean──▶ SEMDIFF|name|status
   │                                                                        │
   └──── rustc  -C overflow-checks=on  (native, catch_unwind) ── native.json┘
                                                                            ▼
                                                        check.py join ─▶ per-test verdicts
```

Everything here lives under `fuzz/semdiff/` + `/tmp` scratch. Nothing tracked
is modified; `fuzz/harness/**` is untouched.

---

## 1. Emitted-shape findings (this fork)

Aeneas emits, for a crate `foo`, a single file `<Dest>/Foo.lean`:

```lean
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
...
namespace foo
def test_pass : Result Unit := do
  let x ← lift (core.num.U32.wrapping_add 2#u32 3#u32)
  massert (x = 5#u32)

/- Unit test for [foo::test_pass] -/
#assert (test_pass == ok ())          -- only for #[verify::test] UNIT fns
...
end foo
```

Confirmed facts:

* **Closed unit test fn** `pub fn test_x()` → `def test_x : Result Unit := do …`
  (niladic: the `:` follows the name directly, no parameter list).
* **`#assert (test_x == ok ())`** is emitted **only when both** hold:
  1. the fn carries the `#[verify::test]` attribute, and the crate has
     `#![feature(register_tool)] #![register_tool(verify)]`;
  2. the signature is exactly `() -> ()` (Lean `Result Unit`).
  The emitter is `extract_unit_test_if_marked` in `src/extract/Extract.ml`.
* **Value-returning fn** `pub fn test_v() -> u32` → `def test_v : Result Std.U32 := do …`
  and **no `#assert`** (even with `#[verify::test]`, because the output is not
  `Result Unit`).
* `assert!(c)` in Rust → `massert (c)` in Lean, and
  `massert b = if b then ok () else fail assertionFailure`.

**The oracle does NOT rely on Aeneas's `#assert`.** We strip those lines
(they throw a *hard elaboration error* on a failing test, which would abort the
batch) and instead generate our own `#eval` per niladic `Result` def. This
also means the fuzzer does **not** need to add `#[verify::test]` — any
`pub fn test_*()` works.

### Result / Error shape (the comparison codomain)

`Aeneas.Std.Result` (`backends/lean/Aeneas/Std/Primitives.lean`):

```lean
inductive Error | assertionFailure | integerOverflow | divisionByZero
               | arrayOutOfBounds | maximumSizeExceeded | panic | undef
inductive Result α | ok (v:α) | fail (e:Error) | div
```

Validated Rust-panic ⇄ Lean-fail correspondence (end-to-end, all MATCH):

| Rust native                          | native `kind`     | Lean value                    |
|--------------------------------------|-------------------|-------------------------------|
| returns normally                     | `ok`              | `ok _`                        |
| `assert!` fails                      | `assertionFailure`| `fail assertionFailure`       |
| `a + b` overflow (checked)           | `integerOverflow` | `fail integerOverflow`        |
| `a / 0`                              | `divisionByZero`  | `fail divisionByZero`         |
| `arr[i]` out of bounds               | `arrayOutOfBounds`| `fail arrayOutOfBounds`       |
| (non-terminating)                    | timeout           | `div` / interpreter loops     |

The driver classifier turns a `Result` into one of:
`OK` · `FAIL:<errorVariant>` · `DIV`, printed as `SEMDIFF|<name>|<status>`.

---

## 2. Driver mechanics (chosen approach)

**Single-file `lake env lean`, no per-crate `lake build`.** We keep one
prebuilt lake project (`lean-driver/`) that depends on the Aeneas backend, and
per crate we:

1. `gen_driver.py Crate.lean` → writes `lean-driver/Driver.lean` = the Aeneas
   file verbatim (it already `import Aeneas` + opens the namespaces), minus
   `#assert` lines, plus a classifier and one `#eval IO.println
   s!"SEMDIFF|<name>|…"` per niladic `Result` def named `test*`.
2. `lake env lean Driver.lean` — elaborates the one file against the **prebuilt**
   Aeneas/mathlib oleans (no rebuild). `#eval IO.println` output goes straight
   to stdout as `SEMDIFF|…` lines; elaboration errors (e.g. a noncomputable
   test) are non-fatal and simply omit that test's line.
3. `check.py` joins the `SEMDIFF|…` lines with the native JSON.

Why not Aeneas's own `#assert`? It (a) aborts the batch on the first failing
test, (b) only knows `== ok ()` (can't name the error variant), and (c) can't
handle value-returning fns. `#eval` of a classifier gives clean, per-test,
machine-parseable output and the exact error variant.

`lake env lean` (not full `lake build`) is the right tool: it reuses the
compiled backend and pays only import-load + elaboration, and never writes to
`.lake`.

---

## 3. Gotchas (read before integrating)

### 3a. `-C overflow-checks=on` is MANDATORY natively  ⚠️
Aeneas models `a + b` (no `wrapping_*`) as a **fallible checked** op
(`fail integerOverflow`). Native **release** rustc silently **wraps**, so
`u32::MAX + 1` would look `OK` natively while Lean says `FAIL:integerOverflow`
— a **spurious MISMATCH**. `native_run.sh` compiles with
`-C overflow-checks=on -C debug-assertions=on`.
Demonstrated: with `SEMDIFF_OVERFLOW_CHECKS=off`, the overflow tests flip to
native-`OK` and the oracle correctly reports `MISMATCH` (exit 1). Keep it on.

(Aside: OOB index / div-by-zero / overflow on **constant** operands are const-
eval `deny` lints; `native_run.sh` adds `#![allow(unconditional_panic,
arithmetic_overflow)]` so they become runtime panics instead of compile
errors. Fuzzer-generated code with runtime operands won't hit this.)

### 3b. Range-`for` loops are noncomputable → `LEAN_INCONCLUSIVE`  ⚠️
`for i in a..b` lowers through `core::iter::range::Step::{forward_checked,…}`,
which this fork's Aeneas emits as **`axiom`s** (see the aeneas warning
"contains extracted external, unknown definitions"). An `axiom` is
`noncomputable`, so `#eval` of such a test fails to compile and produces **no**
verdict. The oracle labels these `LEAN_INCONCLUSIVE` (not a mismatch, does not
affect exit code). The official Aeneas Lean test-suite sidesteps this by
`//@ [!lean] skip`-ping range-iterator files.

**`while` loops and manual recursion DO evaluate** — they lower to the
`Aeneas.Std.loop` combinator, which *is* computable in the interpreter
(verified: `test_while_sum` → `OK`, `test_while_fail` → `FAIL:assertionFailure`).
**Recommendation for the harness:** prefer generating `while` / index-based
loops; treat range-`for` tests as Lean-inconclusive coverage gaps.

### 3c. Non-terminating tests hang BOTH sides  ⚠️
A `while true {}` (or a genuinely divergent recursion) hangs the native binary
*and* the Lean interpreter (`#eval` runs the real computation). Both runners
apply a best-effort `timeout` (coreutils `timeout`/`gtimeout`; env
`SEMDIFF_NATIVE_TIMEOUT`=60s, `SEMDIFF_LEAN_TIMEOUT`=120s). A single hanging
`#eval` poisons the whole batch (Lean has no per-command runtime limit —
`maxHeartbeats` bounds *elaboration*, not `#eval` execution). Mitigation: the
fuzzer should bound loop iterations; on a batch timeout the harness can re-run
tests individually.

### 3d. Selection must stay in lock-step
`native_run.sh` runs every niladic `pub fn NAME()`; `gen_driver.py` runs every
niladic `def NAME : Result …`. Both default to the `test` name prefix. Keep
the prefixes equal or you get spurious `MISSING_*` rows (harmless: never a
`MISMATCH`, never affects exit code).

---

## 4. Timings (measured, Apple Silicon, warm FS cache)

**One-time warm-up** (build the Aeneas backend + fetch mathlib oleans):

| step                                   | time     |
|----------------------------------------|----------|
| `lake exe cache get` (mathlib oleans)  | seconds if already downloaded; **~2 GB download on a cold machine** |
| `lake build` (Aeneas backend, 1673 jobs)| **~3.5 min** |
| total warm-up (cache present)          | **~3m40s** |

Artifacts persist: `backends/lean/.lake` (260 MB, Aeneas oleans) +
`lean-driver/.lake` (~7 GB incl. mathlib). Warm-up is once per checkout.

**Per-crate recurring cost** (100 test fns: 80 straight-line, 20 range-`for`):

| step                       | time    |
|----------------------------|---------|
| charon (rustc→llbc)        | ~0.1 s  |
| aeneas (llbc→lean)         | 0.2–1.2 s (scales w/ crate) |
| native (rustc build + run) | 0.3–0.6 s |
| **lean eval + compare**    | **~3.0 s** (repeatable: 3.37 / 3.11 / 2.96 s) |
| **total end-to-end**       | **~4–5 s** |

The Lean step is dominated by a fixed ~2 s of Aeneas import loading; test
evaluation itself is cheap. **Meets the "few seconds per 100-test crate"
target.** Batch bigger crates to amortize the import cost.

---

## 5. File map (deliverables under `fuzz/semdiff/`)

| path                    | role |
|-------------------------|------|
| `RECIPE.md`             | this document |
| `lean-driver/`          | prebuilt lake project; `require aeneas from "../../../backends/lean"`. `Driver.lean` is overwritten per crate. Run `lake build` here **once** to warm up. |
| `gen_driver.py`         | `Crate.lean` → `Driver.lean` (strip `#assert`, add per-test classifier `#eval`s). Prints `tests: …` on stderr. |
| `native_run.sh`         | native ground truth. `SRC.rs → native.json` (`{name,status,kind,msg}`), `-C overflow-checks=on`, panics via `catch_unwind`. |
| `check.py`              | join `native.json` × `SEMDIFF|…` lines → verdict JSON; exit 1 on any `MISMATCH`. `--strict` also matches the failure kind. `--expected` distinguishes noncomputable evals from absent defs. |
| `check.sh`              | LEAN side + compare: `--dest DIR --native native.json` → verdicts. Runs `gen_driver.py` then `lake env lean` then `check.py`. |
| `oracle.sh`             | full reference pipeline for one crate (charon+aeneas+native+lean+compare) with per-stage timings. |
| `examples/mixed.rs`     | pass / fail-assert / overflow / oob / div0 / value-returning. |
| `examples/loops.rs`     | `while` (computable) vs range-`for` (inconclusive). |

### Verdict vocabulary (`check.py`)
`MATCH` · `MISMATCH` (the bug signal — native/Lean disagree OK-vs-FAIL) ·
`MISMATCH_KIND` (both fail, different kind; only in `--strict`) ·
`LEAN_INCONCLUSIVE` (def emitted but noncomputable) ·
`INCONCLUSIVE_DIV` (Lean `.div`) · `MISSING_NATIVE` / `MISSING_LEAN`.
Exit code 1 iff a `MISMATCH` (or, in `--strict`, `MISMATCH_KIND`) occurred.

---

## 6. Harness integration (how Phase-2 should call this)

One-time, per machine/checkout:
```bash
cd fuzz/semdiff/lean-driver
lake exe cache get && lake build      # ~3.5 min; persists
```

Per generated crate `SRC.rs`:
```bash
# 1. native ground truth (overflow checks ON is mandatory)
fuzz/semdiff/native_run.sh SRC.rs /tmp/x.native.json

# 2. translate
charon rustc --preset=aeneas --dest-file /tmp/x.llbc -- --crate-type=rlib SRC.rs
aeneas -backend lean -abort-on-error -no-progress-bar /tmp/x.llbc -dest /tmp/xout

# 3. Lean eval + compare  (exit 1 == semantic divergence found)
fuzz/semdiff/check.sh --dest /tmp/xout --native /tmp/x.native.json \
    --out /tmp/x.verdict.json
#   add --strict to also flag error-kind disagreements
```
Consume `/tmp/x.verdict.json`; treat `MISMATCH` (and, if desired,
`MISMATCH_KIND`) as bug candidates. `oracle.sh SRC.rs` does all of the above
for one file and prints timings — use it as the reference implementation.

Env knobs: `CHARON`, `AENEAS`, `ELAN_BIN`, `CARGO_BIN` (tool paths);
`SEMDIFF_OVERFLOW_CHECKS` (default `on`), `SEMDIFF_NATIVE_TIMEOUT` (60),
`SEMDIFF_LEAN_TIMEOUT` (120).
