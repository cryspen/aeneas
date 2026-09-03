# Fuzz-campaign triage summary (2026-07-26)

Triage of the five candidate crash fingerprints surfaced beyond the known
F4/F6, on branch `fuzz-harness` / fork sources `/Users/karthik/aeneas/src`.

Toolchains: FORK = charon v0.1.196 + `/Users/karthik/aeneas/bin/aeneas`;
UPSTREAM = charon v0.1.225 + `/tmp/aeneas-upstream/bin/aeneas`. The two `.llbc`
versions are mutually incompatible, so fork-vs-upstream comparisons vary both
charon and aeneas together (noted where it matters). All `min.rs` were confirmed
accepted by `rustc --edition=2021 --crate-type=rlib -C overflow-checks=on`.

## Distinct root causes after dedup

The five findings collapse to **5 distinct phenomena** (two of the packs bundle
two functions each, and their fuzzer fingerprints were mislabeled):

| # | phenomenon | class | new? | fork | upstream |
|---|------------|-------|------|------|----------|
| 1 | assert-operand double-eval → "no bottoms" (InterpExpressions.ml:55) | **A REAL** | **YES** | crash | crash |
| 2 | closure-returns-ref via `array::from_fn` → non-endable abs (InterpBorrows.ml:1203) | C dup of AeneasVerif#804 | no | crash | OK |
| 3 | `mut &u32` reassigned before loop → Unreachable (InterpAbs.ml:1671) | C dup of **F6** / #24 | no | crash | crash |
| 4 | infinite loop, no break → "not supported yet" (InterpLoops.ml:407) | **B** expected gate | no | (gate) | (gate) |
| 5 | `chars().collect()` → missing builtin model (Extract.ml:2851) | INVALID (warn, exit 0) | no | OK | OK |

## Per-finding table

### other-interpexpressions-55  →  phenomenon #1
- **Fingerprint:** `There should be no bottoms in the value`, InterpExpressions.ml:55 (`read_place_check`).
- **VALID crash:** YES (rustc OK; reproduces fork + upstream).
- **Minimized repro:**
  ```rust
  pub fn f(b0: bool) { assert!(b0); assert!(b0); }
  ```
- **Class A — REAL, genuinely NEW.** Root cause: `eval_assertion`
  (InterpStatements.ml:156) reads the assertion operand once; on the concrete-bool
  path it delegates to `eval_assertion_concrete` (:129) which calls `eval_operand`
  **again** (:133). Charon lowers `assert!(x)` to `_t = copy x; assert(move _t)`;
  the first read moves `_t` out (→ ⊥), the second re-reads ⊥. Only bites on the
  *second* assert of the same bool (the first concretizes it to `true`, forcing
  the concrete path). Controls: two different vars OK; `||` OK; same var 2×/3× crash.
- **Fork vs upstream:** both affected (identical code shape upstream).
- **Severity:** MEDIUM. **FILE on cryspen/aeneas.**

### other-interpborrows-1203  →  phenomenon #2
- **Fingerprint:** `Can't end abstraction N as it is set as non-endable`, InterpBorrows.ml:1203 (backward eval).
- **VALID crash:** YES on fork (rustc OK).
- **Minimized repro:**
  ```rust
  pub fn each_ref(s: &[u8; 1]) -> [&u8; 1] { std::array::from_fn(|i| &s[i]) }
  ```
  (closure essential; manual `[&s[0]]` does not crash.)
- **Class C — DUPLICATE of AeneasVerif/aeneas#804** (closures returning refs from
  captured state; seed is that exact regression test, `//@ [!lean] skip`). The
  craise is the L2 "safety net" (InterpBorrows.ml:1201-1205) firing.
- **Fork vs upstream:** fork crashes; **upstream does NOT** (axiomatizes
  `array::from_fn`, exit 0). Effectively resolved/worked-around upstream.
- **Severity:** LOW as a new item (known/skip-listed). Do NOT file.

### unreachable-interpexpressions-55  →  #3 (fatal) + #1 (bundled)
- **Fingerprint (as reported):** `Unreachable`, mislabeled `InterpExpressions.ml:55`,
  top frame `merge_abs_conts_aux @ InterpAbs.ml:1915`.
- **VALID crash:** YES, but the fatal uncaught exception is **F6**
  (`Unreachable`, InterpAbs.ml:1671), not the labeled line. The `:55` came from a
  non-fatal error emitted by the pack's *other* function (= phenomenon #1).
- **Minimized repro (fatal F6 case):**
  ```rust
  pub fn reassign_shared_before_loop<'a>(mut a: &'a u32, y: &'a u32) -> u32 {
      let mut s = *a; a = y; let mut i = 0u32;
      loop { s = s.wrapping_add(*a); i = i.wrapping_add(1); if i > 10 { return s; } }
  }
  ```
- **Class C — DUPLICATE of F6 / cryspen/aeneas#24** (inverted `can_end` guard in
  `eliminate_shared_loans`, InterpReduceCollapse.ml:44-46).
- **Fork vs upstream:** both affected (upstream line InterpAbs.ml:1688).
- **Severity:** folds into #24 (already filed).

### unreachable-interploops-407  →  #4 (named) + #3 (fatal, bundled)
- **Fingerprint (as reported):** `Unreachable`, mislabeled `InterpLoops.ml:407`.
- **VALID crash:** YES, but again bundled: the fatal uncaught exception is **F6**
  (from the reassigned-shared-borrow function); the named `InterpLoops.ml:407` is
  a **feature-gate** error from the infinite-loop function.
- **Minimized repro (named InterpLoops:407 gate):**
  ```rust
  pub fn spin(p: &mut u32) { loop { *p = (*p).wrapping_add(1); } }
  ```
- **Class B (feature gate) + Class C (F6 dup).** InterpLoops.ml:407 is
  `[%craise] "(Infinite) loops which do not contain breaks are not supported yet"`
  — intended rejection, surfaced as a "crash" only by `-abort-on-error`.
- **Fork vs upstream:** both (gate at InterpLoops.ml:411 upstream; F6 at 1688).
- **Severity:** none (gate) / #24 (fatal). Do NOT file.

### other-extract-2851  →  phenomenon #5
- **Fingerprint (as reported):** empty message, Extract.ml:2851.
- **VALID crash:** **NO.** `Extract.ml:2851` is a `[%warn]` (missing builtin
  model for `Iterator::collect`); aeneas exits 0 and generates `Crate.lean`.
- **Minimized repro:**
  ```rust
  pub fn collect() { let s = "hello"; let _chs: Vec<char> = s.chars().collect(); }
  ```
- **INVALID — harness false-positive.** Oracle matched the
  `Compiler source: ... line` marker that `[%warn]` also prints.
- **Fork vs upstream:** benign on both (upstream Extract.ml:2868).
- **Severity:** none. Do NOT file.

## Genuinely NEW bugs worth filing

- **Exactly one: phenomenon #1** — the assert-operand double-evaluation
  "no bottoms" crash (finding `other-interpexpressions-55`). Class A, affects fork
  and upstream, not covered by F1-F6 / #22-#24 / #804. Suggested fix: pass the
  already-read `v`/`ctx` into `eval_assertion_concrete` instead of re-calling
  `eval_operand` on the `move` operand.

## Fork-local-fix relevance

None of the five relate to the fork's uncommitted edits
(`Config.ml`/`Main.ml`/`Translate.ml`/`pure/PureMicroPasses.ml` — pure-ir JSON
dump + preserved-defs gating, inactive without `-dump-pure-ir`). All crash sites
are interpreter/extraction level and run before/independently of those passes.
`git diff HEAD -- src/interp/` is empty; the fork's interpreter is its upstream
base unchanged.

## Notes for the harness owner (fuzz/harness/** — not modified here)

1. `-abort-on-error` promotes every `[%craise]` feature gate (e.g. InterpLoops.ml:407)
   into an uncaught `Failure`, so class-B "unsupported construct" rejections look
   identical to class-A internal crashes. Gate them by message text
   ("not supported"/"not yet") or run without `-abort-on-error`.
2. Fingerprint on the **exception backtrace top frame**, not the last-printed
   `[Error] ... Compiler source: <file>, line <n>` line — this caused both
   `unreachable-*` mislabels and the `other-extract-2851` false positive (a
   `[%warn]` prints the same marker).
3. Minimize multi-function packs to one function per fingerprint before recording.
