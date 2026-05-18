# `--skip-decl` audit — Aeneas differential testing infrastructure

**Date:** 2026-05-18
**Scope:** every `--skip-decl <name>` invocation reachable from the
`aeneas-lean-checker` / `tests/lean-checker/lean-diff` harnesses.
**Author note:** all error captures below come from a clean build of the
unfiltered Lean emit; the OCaml binary, the `aeneas-check` binary, and
the `RuntimeShim` library are the versions present in this worktree at
HEAD `33936d6a` plus uncommitted Session-7 changes.

---

## 1. Mechanism and call-site inventory

### 1.1 Mechanism

- CLI plumbing: [`aeneas-lean-checker/AeneasCheck/Cli.lean`](../../aeneas-lean-checker/AeneasCheck/Cli.lean) lines 36–46 (`findFlagsAll`) and line 95 (collect → pass to emitter).
- Emit-side filter: [`aeneas-lean-checker/AeneasCheck/Backends/LeanEmit.lean`](../../aeneas-lean-checker/AeneasCheck/Backends/LeanEmit.lean) lines 300–307. `--skip-decl N` is an exact-string match against the sanitized inner decl name and drops the matching `Decl`/`StructDecl`/`EnumDecl`/`TraitDecl`/`TraitImpl` from the Lean source. Translation, replay, typecheck, Rust-model emit, and the cert-summary output are **unaffected** — only the Lean text changes.

### 1.2 Call sites

A repo-wide grep (`*.sh`, `*.lean`, `*.ml`, `*.toml`, `*.json`, `*.md`, `*.py`) finds:

| Call site | Lines | Skips |
|---|---|---|
| `tests/lean-checker/lean-diff/scripts/run-diff.sh` | 34 | `constants`: `use_v` (1) |
| `tests/lean-checker/lean-diff/scripts/run-diff.sh` | 43–55 | `demo`: 13 skips |
| `tests/lean-checker/lean-diff/scripts/run-diff.sh` | 63–70 | `paper`: 8 skips |

**Total: 22 `--skip-decl` flags across one shell script (the diff harness driver).** No other Make targets, lakefiles, CI jobs, or Python helpers invoke the flag.

---

## 2. Decl-by-decl audit

For each skipped decl: the kind comes from the *standard* backend's `tests/lean/{Fx}.lean`; the concrete error comes from re-running `aeneas-check --out` **without** the skip and then running `lake build +{fixture}` against the diff harness `lakefile.lean`.

Failure classes:

- **Elab — body** — the Lean source typechecks at the signature level but the body is malformed (wrong literal type, undefined identifier, syntactic glitch, etc.).
- **Elab — signature** — the signature itself is wrong (e.g. an impl `def` returning a tuple where the trait expects a scalar).
- **Elab — attribute** — an unknown attribute (`@[discriminant isize]` here) appears on the decl.
- **Shim gap** — the emitted call site refers to a `RuntimeShim` binding that is missing or has the wrong arity.
- **Cascade** — the decl itself would elaborate, but it references another skipped decl, so dropping it is needed to keep the file coherent.

> Aeneas-side translation never crashes for any of these decls — `parsed cert / translated …` succeeds for every name in all three fixtures (verified by running `aeneas-check` without `--out`). There are **no "emit failure" (crash) cases** in the current skip list; every skip is masking an elaboration-time problem in the emitted Lean text.

| Fixture | Decl | Kind | Failure class | Concrete error (first line) | Owner / next-step category |
|---|---|---|---|---|---|
| `constants` | `use_v` | fn | Shim gap (arity) | `Function expected at V.LEN but this term has type Result Usize` (constants_full.lean:129) | Carry-forward #3 ("Constants `use_v` shim-side typed binding"). The emitter writes `(constants.V.LEN T N)` but the emitted `V.LEN` body and the `RuntimeShim` binding are both 0-arg. Fix: emit a typed `V.LEN (T : Type) (N : Std.Usize)` *and* update the shim, OR teach the emitter to call `V.LEN` with no generic args when the body is non-generic. |
| `demo` | `CList` | enum (recursive, generic) | Elab — attribute | `Unknown attribute [discriminant]` (demo_full.lean:26) | **Unclassified emit gap.** The emitter unconditionally prints `@[discriminant isize]` on inductives that originated from `#[repr(isize)]`. The shim has no such attribute. Fix: gate the attribute on the backend (mainline `tests/lean/Demo/Demo.lean` uses it because `Aeneas.Std` declares it) — drop it under `RuntimeShim`. |
| `demo` | `Counter` | trait | Cascade | (no direct error; the impl that fills it is broken — see next two rows) | Cascade of the `DemoCounter.incr` signature bug. Un-skipping the trait alone is fine, but doing so without also fixing the impl yields the `DemoCounter` row's signature mismatch. |
| `demo` | `Std.Usize.Insts.DemoCounter` | trait impl | Elab — signature | `Type mismatch DemoCounter.incr has type Usize → Result (Usize × (Unit → Usize)) but is expected to have type Usize → Result Usize` (demo_full.lean:42) | **Unclassified emit gap (closure-encoding bleed-through).** The forward translator is conjuring a `Unit → Usize` back-closure for an `&mut self` method when the trait sig has no such back. Same root as carry-forward "closures-everywhere"; this case is special because the impl's signature differs from its trait's expected one. |
| `demo` | `Std.Usize.Insts.DemoCounter.incr` | fn | Elab — body (and tied to above) | `Type mismatch self + Usize.ofNat 1 has type Usize but is expected to have type Result _` (demo_full.lean:35) | Same root cause as the impl row: the emitter generates a tuple-returning body that doesn't bind into the signature, *and* a non-`do` arithmetic line where a `Result` is required. Fix at the same layer. |
| `demo` | `choose` | fn (returns closure) | (compiles in isolation) | n/a — `demo_full.lean:48-49` actually elaborates: `def choose … := do if b then ok (x, fun ret => (ret, y)) else …`. No elab error in the lake build run. | **Mis-skipped** (Session-5 doc claimed "M12.2a closure-emit placeholder", but the current emit is fine). Recommend removing this `--skip-decl` and adding a runner vector. |
| `demo` | `list_nth` | fn (recursive on `CList`) | Elab — body (multiple) | `Application type mismatch ok () has type Unit but is expected to have type T` (demo_full.lean:85) | **Unclassified emit gap (recursive-match scoping).** The walker collapses the `match` to inverted arms — the `CCons` arm is `ok ()` (loses the bound `x3`), the `CNil` arm contains the recursive call meant for `CCons`. The fix lives in the forward-walker's match-arm assembly. Affects `list_nth_mut`, `sum`, `list_tail` similarly. |
| `demo` | `list_nth_mut` | fn (recursive, back-closure) | Elab — body | `unexpected token '←'; expected ':=' or '|'` (demo_full.lean:126) | Same root as `list_nth` plus a parenthesis/comma glitch in the back-closure emit (the synthesised `ok l_post_v, fun ret => l)` runs onto one tuple). |
| `demo` | `list_tail` | fn (recursive, back-closure) | Elab — body | `unexpected token ','; expected ')'` (demo_full.lean:145) | Same root as `list_nth_mut`. |
| `demo` | `list_nth1` | fn | Elab — body (type) | `Application type mismatch ok (U32.ofNat 0) has type U32 but is expected to have type T` (demo_full.lean:89) | Loop driver emits the reducible wrapper with the wrong return type (`Result T` for what should be `Result Std.U32`). |
| `demo` | `list_nth1_loop` | fn (loop) | Elab — body | `Application type mismatch ()  … in ControlFlow ()` (demo_full.lean:98) | The loop body's `ControlFlow` instantiation passes `()` (`Unit`-the-value) where `Unit`-the-type is required, *and* references `s33`/`t3` (undefined locals). Root cause: loop-body translator generates the wrong type binders. |
| `demo` | `list_nth1_loop.body` | fn (loop body) | Elab — body | `Unknown identifier s33` (demo_full.lean:99) | Same root as `list_nth1_loop`. |
| `demo` | `use_counter` | fn | Elab — body | `Type mismatch (cnt_post_v, cnt_post_back) has type ?m × ?m but is expected to have type Usize` (demo_full.lean:154) | Cascade of the `DemoCounter.incr` signature bug (the trait method's return type mismatches what `use_counter` is destructuring). |
| `demo` | `i32_id` | fn (recursive) | Elab — body | `Unknown identifier t3` (demo_full.lean:136) | **Unclassified emit gap.** The recursive-call line is dropped — only the `else` literal references a `t3` that was never bound. Same family as the `list_nth*` recursion-walker bugs. |
| `paper` | `List` | enum (recursive, generic) | Elab — attribute | `Unknown attribute [discriminant]` (paper_full.lean:20) | Same as `demo::CList`. |
| `paper` | `test_incr` | fn (unit test) | (compiles cleanly in isolation) | n/a — `paper_full.lean:34-37` elaborates without error in the lake build run. The `massert (x = 1#i32)` becomes a bound `let t1 := 0#i32 = 1#i32` followed by `ok ()`; the assertion is silently weakened but the file builds. | **Mis-skipped** (PaperRunner doc claimed `massert` semantics issue). Compiles fine; the issue is semantic (assert is a no-op), but the differential harness can still call it. Recommend removing this `--skip-decl` and adding a runner vector that calls `test_incr` directly. |
| `paper` | `choose` | fn (returns closure) | (compiles cleanly in isolation) | n/a — paper's `choose` emits the same shape as `demo`'s and elaborates. | **Mis-skipped** — same as `demo::choose`. |
| `paper` | `test_choose` | fn | Elab — body | `Type mismatch t0_back t1 has type I32 × I32 but is expected to have type Result Unit` (paper_full.lean:54) | The tail call `(t0_back t1)` is the value of the `do`, but the emitter forgot to wrap it in `ok` (or return `Unit`). Carry-forward "tail ok-wrap" already touched this area for `:`-paths but missed back-closure applications. |
| `paper` | `list_nth_mut` | fn (recursive, back-closure) | Elab — body | `unexpected token '←'; expected ':=' or '|'` (paper_full.lean:66) | Same root as `demo::list_nth_mut`. |
| `paper` | `sum` | fn (recursive on `List`) | Elab — body | `Application type mismatch ok () has type Unit but is expected to have type I32` (paper_full.lean:76) — and `failed to synthesize HAdd (List I32) I32` (paper_full.lean:79) | Same family as `demo::list_nth` (match-arm scoping): the `Cons` arm degenerates to `ok ()`, then the recursive call adds the `List` to the result. |
| `paper` | `test_nth` | fn (unit test) | Shim gap (binding) | `Unknown identifier alloc.boxed.Box.new` (paper_full.lean:86 × 3) | **Unclassified shim gap.** The mainline `Aeneas.Std` provides `alloc.boxed.Box.new`; `RuntimeShim` does not. Either add to the shim or have the emitter drop `Box::new` wrappers (mainline's `tests/lean/Paper.lean:99-101` writes `List.Cons 3#i32 (List.Cons 2#i32 List.Nil)` directly, no `Box.new`). |
| `paper` | `call_choose` | fn (uses back-closure on tuple) | Elab — body | `failed to synthesize HAdd (U32 × U32) U32` (paper_full.lean:100) | The pattern `let (px, py) := p` is missing; the emitter binds `p_post_v : U32 × U32` and then tries `p_post_v + 1#u32`. Walker drops the tuple destructure when the input itself is already a tuple. |

### 2.1 Failure-class roll-up

| Failure class | Count |
|---|---:|
| Elab — body | 12 |
| Elab — attribute | 2 |
| Elab — signature | 1 |
| Shim gap | 2 |
| Cascade | 2 |
| **Mis-skipped (compiles, recoverable now)** | 3 |
| **Total** | **22** |

Three skips (`demo::choose`, `paper::test_incr`, `paper::choose`) actually elaborate against the current shim and emitter — they are "wasted coverage" today and should be re-enabled in the runners. The remaining 19 mask real emit/elab bugs.

### 2.2 Root-cause clustering

Of the 19 genuine bugs, they cluster into a smaller set of root causes:

| Root cause | Skipped decls | Fix surface |
|---|---|---|
| `@[discriminant isize]` printed unconditionally | `CList`, `List` (2) | One-line emit gate (skip the attribute under RuntimeShim) |
| Match-arm scoping inversion in recursive walker | `list_nth`, `list_nth_mut`, `list_tail`, `i32_id`, `sum` (5) | Single fix in `Forward.lean` match-arm assembler |
| Loop body emits undefined locals (`s33`, `t3`) | `list_nth1`, `list_nth1_loop`, `list_nth1_loop.body` (3) | Loop-body translator |
| Closure-leak for trait `&mut self` methods | `DemoCounter`, `DemoCounter.incr`, `use_counter` (3) — and silently affects `Counter` cascade | Trait-impl signature shaping in the forward translator |
| Back-closure tail position not wrapped in `ok` / missing tuple destructure | `test_choose`, `call_choose` (2) | Tail-wrap predicate + tuple-input handling |
| Generic-global shim/emit arity mismatch | `use_v` (1) | Either shim or emitter, already carry-forward #3 |
| Missing shim binding | `test_nth` via `alloc.boxed.Box.new` (1) | Add to RuntimeShim (or drop `Box::new` in emitter) |
| Cascade only | `Counter` (1) | Auto-resolves once `DemoCounter` cluster is fixed |
| **Effective bug clusters** | **~7 distinct fixes** for 19 skips | |

---

## 3. Proposal

### 3.1 Why `--skip-decl` is wrong for differential coverage

`--skip-decl` is a *silent* mechanism. The harness driver lists names in a shell script, the emitter drops them, the resulting Lean file compiles, the runner reports "8/8 fixtures pass", and nothing anywhere in the workflow surfaces (a) which decls were dropped, (b) why each was dropped, or (c) whether any dropped decl has since been fixed by unrelated work. The skip-comment text in `run-diff.sh` and the per-runner docstrings drift from reality — three of the 22 current skips no longer reproduce, and the doc still says they do. For a differential harness whose explicit goal is to catch silent regressions, having 19 silent gaps and 3 silent stale ones is the worst-shaped failure mode.

There is also a more subtle problem: skip-by-name is not idempotent under emit changes. If a future emit fix renames `list_nth1_loop.body` to `list_nth1.body`, the skip stops matching, the broken decl re-enters the file, the build breaks, and the only signal is a multi-line lake error. A name-keyed allowlist cannot distinguish "the bug was fixed" from "the emitter renamed the decl" from "a new bug appeared".

### 3.2 Expected-failure tracking design

**Storage.** Per-fixture YAML manifest at `tests/lean-checker/lean-diff/expected-failures/{fixture}.yaml`, version-controlled. One file per fixture so blame/diff/PR comments scope cleanly. Schema:

```yaml
fixture: demo
schema: 1
expected_failures:
  - decl: CList
    kind: enum
    class: elab_attribute
    error_substring: "Unknown attribute [discriminant]"
    cluster: discriminant_isize_attr
    notes: |
      Mainline emits @[discriminant isize] (Aeneas.Std defines it);
      RuntimeShim does not. Gate the attribute on backend.
    introduced_session: 5
  - decl: list_nth
    kind: fn
    class: elab_body
    error_substring: "ok () has type Unit but is expected to have type T"
    cluster: recursive_match_arm_scoping
    introduced_session: 5
```

The `error_substring` field is the load-bearing one: the harness greps the lake build output for it and only treats the decl as "expected to fail" if the substring matches. This catches both directions of drift.

**Harness consumption.** The diff driver does *not* pass `--skip-decl`. Instead it runs `aeneas-check --out` unfiltered, runs `lake build` capturing stderr, then asks a small classifier script: "for each decl in `expected_failures.yaml`, does its `error_substring` appear in the build log?". Three outcomes:

1. **Match** — expected failure confirmed. Strip the decl from the generated `.lean` by post-processing (a one-shot scrub of `def <name>` / `inductive <name>` / `structure <name>` blocks), then build the runner. Differential proceeds.
2. **Decl is in `expected_failures` but its error_substring is NOT in the build log** — **loud signal**: "Decl `X` was previously failing with `<substring>` but now elaborates cleanly. Either the bug is fixed (remove from manifest, add to runner) or the error has shifted (update substring)." Build fails with a clear actionable message.
3. **Build error is NOT covered by any `expected_failures` entry** — **loud signal**: "New decl-level elab failure for `Y`. Either add an entry to the manifest (if expected) or fix the emit gap." Build fails.

This gives us the same "let the well-emitted subset ship" pragmatism the current skip mechanism has, but every silent gap becomes a structured, surfaced gap with a known fix-cluster owner.

**Surfacing fixes.** The "expected failure stopped failing" signal (#2) is the killer feature. Today, when an emitter fix accidentally repairs `i32_id`, nothing tells us — `i32_id` remains skipped, the diff still passes, and we lose the coverage the fix earned us. With the manifest, the next CI run says "remove `i32_id` from `demo.yaml`", we drop the entry, add a runner vector, and the wins compound.

**Cluster reporting.** A weekly (or per-session) report aggregates `cluster` fields across all fixtures' manifests: "`recursive_match_arm_scoping` blocks 5 decls across `demo` + `paper`; fixing it would unlock 5 runner vectors and reduce expected-failure count by ~25%." This converts the audit table into a working backlog.

### 3.3 Migration path (priority order)

1. **Land the manifest schema + classifier** (no semantic change). Translate the 22 current skips into `expected_failures/{constants, demo, paper}.yaml` entries verbatim (one per skip, populating `error_substring` from §2's table). Driver script: read manifest → run unfiltered aeneas-check → run lake → diff observed errors against expected → post-process generated `.lean` to drop expected-failing decls → continue. **Equivalent behaviour to today**, with the loud-signal machinery in place.

2. **Remove the three mis-skipped entries** (`demo::choose`, `paper::test_incr`, `paper::choose`). They no longer fail; the manifest's #2 signal will demand this anyway. Add corresponding runner vectors.

3. **Fix the cheapest bug clusters first**, in order of `(decls unlocked) / (estimated fix size)`:
   - **`discriminant_isize_attr` (2 decls)** — one-line attribute gate. Unlocks `CList` and `List`, which then unlocks all their dependents (every `list_*` decl, `sum`, `test_nth`). Probably the highest-leverage single fix.
   - **`alloc.boxed.Box.new` shim binding (1 decl, but `test_nth` is the only one of `paper`'s big remaining suite that needs it)** — add to RuntimeShim.
   - **`recursive_match_arm_scoping` (5 decls)** — central forward-walker fix; touches the most decls but is also the deepest dive.
   - **`closure_leak_trait_mut_self` (3 decls)** — trait-impl signature shaping.
   - **`loop_body_undefined_locals` (3 decls)** — loop translator.
   - **`tail_back_closure_wrap` (2 decls)** — narrow predicate widening.
   - **`use_v` generic-global** — already on carry-forward #3.

4. **Once every cluster is fixed**, the manifests for `constants`, `demo`, `paper` are empty, every emitted decl ships in the lake build, and the manifest mechanism itself can either be kept (as future-proofing for new fixtures) or retired in favour of a "no expected failures allowed" assertion.

5. **Generalise the manifest to other fixtures** as Phase-2 wire-ins happen (`loops-issues`, `assert-cfg`, `traits`, `nested_borrows`, etc.). The same machinery handles them without modification.

---

## 4. Appendix — verification protocol

To reproduce any row in §2:

```bash
# rebuild aeneas-check if needed
( cd aeneas-lean-checker && lake build aeneas-check )

# regen one fixture WITHOUT --skip-decl
aeneas-lean-checker/.lake/build/bin/aeneas-check \
  tests/llbc/<fixture>.cert.json \
  --out tests/lean-checker/lean-diff/generated/<fixture>.lean

# build the lean-diff lean lib (compiles every fixture's emit)
( cd tests/lean-checker/lean-diff && lake build +<fixture> )
```

The error output of the final `lake build +<fixture>` is the source of every "Concrete error (first line)" entry above. All three fixtures' errors were captured this way during the audit; the original generated/*.lean was restored after each measurement so the harness is byte-identical to its pre-audit state.
