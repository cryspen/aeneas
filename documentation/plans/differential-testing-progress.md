## Plan: Four-artifact differential testing rollout (Phases 0 + 1 + 4a/b in-flight)
## Started: 2026-05-18 (Session 2)
## Last action (Session 3, 2026-05-18): Phase 4a complete (4 LeanEmit/shim fixes + 1 LeanEmit topo sort), constants.lean wired into lean-diff; Phase 4b added scalars + demo fixtures to G_rust (+15 proptests). Both harnesses green: G_rust 33/33 proptests; G_lean 119 == 119 byte-identical.
## Phase: Phases 0+1+4a (LeanEmit polish) DONE; Phase 4b partial; Phases 2/3/5 + finishing Phase 4b remain.
## Next commit: continue Phase 4b (G_lean shim work for scalars/demo + ADT-returning constants), or jump to Phase 2 (G_byte sweep).

### Done-condition audit (Session 2 §"Done condition")
1. ✓ Phase 0 + 1A + 1B + 1C complete; 9 new commits on `aeneas-lean-certificate-diff-test`.
2. ✓ `differential-testing-plan.md` updated to mark resolved emitter unblockers (§G_rust + §G_lean "Known unblockers"). Fixture counts in the gates table bumped to current values.
3. ✓ This progress note exists.
4. ✓ Branch ready to push for review, not yet pushed.

### Branch state (top 9 commits over `c510e621`)
```
235d8753 aeneas-check: widen cert parser to accept v6 in addition to v4         (Phase 0 follow-up)
54591d17 tests/diff: extend differential harness — 14 new proptests, 5 fixtures (Phase 0)
6eb89ac4 tests: regenerate constants cert + generated Lean fixture              (Phase 1B follow-up)
f26cc772 LeanEmit Phase-1B: type-correct fallback for missing-local placeholders (Phase 1B)
98e0a623 Phase 1C: ADT proptests in differential harness                        (Phase 1C)
df1441cd Phase 1C: RustEmit consumes adtName for real struct syntax             (Phase 1C)
ac176ee3 Phase 1C: PExpr plumbing for struct names on recordLit / structUpdate  (Phase 1C)
00e4d8ca Phase-1A diff: wire bitwise into the lean-diff harness                 (Phase 1A)
6438a751 Phase-1A shim: add #isize, #i32, #i64 macros; revert Bitwise hand-patch (Phase 1A)
```

### What changed by gate

**G_rust** — `tests/lean-checker/differential/`. Grew from 1 fixture / 1 proptest → 7 fixtures / 18 proptests:
- Phase 0 added 14 proptests across 5 fixtures (`incr_cert`, `constants`, `bitwise`, `compare_simple`, `calls`).
- Phase 1C added 3 ADT proptests across 2 fixtures (`aggregates_basic`, `reborrows`).
- All 18 pass at 256 cases. No genuine differentials.
- Harness shape: flat `ref_impl` / `model` mods for non-ADT fixtures; per-fixture modules (`aggregates_basic`, `reborrows`) for ADT fixtures with crate-local struct decls.

**G_lean** — `tests/lean-checker/lean-diff/`. Grew from 60 vectors / 3 fixtures → 90 vectors / 4 fixtures:
- Phase 1A wired `bitwise` in (30 new vectors: 6× shift_u32, 6× shift_i32, 6× xor/or/and/u32). Required `#isize`/`#i32`/`#i64` macros in `RuntimeShim/Aeneas/Std.lean`.
- `constants` is regenerated and stored at `tests/lean-checker/lean-diff/generated/constants.lean` but **not** wired into the harness (other LeanEmit gaps remain — see below).

### Emitter / shim fixes landed

| Commit | Fix | Surface |
|---|---|---|
| `6438a751` | `RuntimeShim` gains `#isize` / `#i32` / `#i64` macros | unblocks any LeanEmit output using `N#isize` etc. |
| `ac176ee3` | `PExpr.recordLit` / `PExpr.structUpdate` carry `adtName : Option String`, plumbed from `TypeDeclMap` in Forward translator | shared plumbing for all backends |
| `df1441cd` | RustEmit consumes `adtName` → `Foo { f1: v1, f2: v2 }` / `Foo { field: v, ..base }` | unblocks ADT fixtures in G_rust |
| `f26cc772` | LeanEmit emits typed zero of field type when projecting a `0#u32` placeholder root through a literal-int field | fixes `unwrap_y` / `get_z1` ill-typed constants |
| `235d8753` | `aeneas-check` cert parser widened from v4-only to v4 + v6 | needed because `bin/aeneas` (parent branch) emits v6; this commit avoids forcing every diff-test fixture down to v4 |

### Operational notes / lessons learned

- **Three of four dispatched agents got worktree-pinning issues**: Phase 0 stayed isolated cleanly; Phases 1B and 1C found their assigned worktrees pinned to a stale `004e11fe` (a release-nightly merge commit predating `aeneas-lean-checker/`), and rather than abort (per the handoff's instruction), both bailed to the live `diff-test` worktree and committed there directly. Net effect: their commits ended up on the right branch with correct history, but the isolation guarantee was lost mid-flight. **Future agent dispatches** should make the abort-vs-fall-back behavior explicit, or pre-create the agent worktrees on the target branch HEAD.
- **Pre-built binaries lied**: the handoff trusted `/Users/karthik/aeneas/aeneas-lean-checker/.lake/build/bin/aeneas-check` (timestamp May 18) to contain commit `3d086b79`'s brace-path fix. It did not — the binary was rebuilt from `aeneas-lean-certificate` source, not from diff-test source. Phase 0 caught this and built its own. **Future handoffs** should not promise content of binaries they didn't build themselves.
- **Cert format v4 → v6 drift**: `bin/aeneas` on the parent (and therefore in our worktree as well) emits v6 certs (`holderLocal`, `JoinEntryDelta`, `stmtRefs` additions). The committed cert JSONs were v4; the pre-built `aeneas-check` only accepted v4. Phase 0 widened the parser additively (`235d8753`) — both formats are accepted because the v6 additions are optional fields the parser already ignores.
- **Parent branch (`aeneas-lean-certificate`) was protected throughout**. Audited at end of session: HEAD `e6853c5f` unchanged, no diff-test commits in ancestry, no contamination of the parent worktree's tracked state. The M10 agent's work was not disturbed.

### Phases 2–5 (out of scope for Session 2)
- **Phase 2** — G_byte sweep extension to `scripts/compare-backends.sh`.
- **Phase 3** — G_rfl harness at `tests/lean-checker/lean-rfl/`.
- **Phase 4** — Scale G_rust + G_lean to ~30 fixtures each.
- **Phase 5** — Single-command sweep + CI integration.

### Carry-forward LeanEmit follow-ups (surfaced by Phase 1B, not fixed)

`tests/lean-checker/lean-diff/generated/constants.lean` is regenerated and *almost* well-typed after Phase 1B, but four independent LeanEmit gaps still block wiring it into the lean-diff harness:

1. Bare `(x1 + x2)` on the i32 `add` — there is no `HAdd I32 I32 (Result I32)` shim instance, so the `+` doesn't elaborate.
2. Brace-decorated identifier `def {constants.Wrap<T>}.new` — invalid Lean syntax (the brace-sanitization that fixed RustEmit doesn't reach Lean def names).
3. `Pair Std.U32 Std.U32`-typed record literal `ok`-applied to a scalar return slot.
4. `V` struct shape `Array T 0#usize` (wrong length literal).

These are tracked in §G_lean "Known unblockers" of the plan; resolving them is a candidate for an early-Phase-4 cleanup.

### Files touched (high-level)

- `aeneas-lean-checker/RuntimeShim/Aeneas/Std.lean` — `#isize`/`#i32`/`#i64` macros.
- `aeneas-lean-checker/AeneasCheck/Pure/Syntax.lean` — `adtName` field on `PExpr.recordLit` / `PExpr.structUpdate`.
- `aeneas-lean-checker/AeneasCheck/Pure/Pretty.lean` — pass-through of new field in patterns.
- `aeneas-lean-checker/AeneasCheck/Translate/Forward.lean` — `adtName` plumbing from `TypeDeclMap`; missing-local typed-zero fallback.
- `aeneas-lean-checker/AeneasCheck/Translate/Driver.lean` — `adtName` threaded through rewrite passes.
- `aeneas-lean-checker/AeneasCheck/Backends/RustEmit.lean` — real Rust struct syntax when `adtName` present, placeholder fallback otherwise.
- `aeneas-lean-checker/AeneasCheck/Json/Parser.lean` — accept fmt_version 4 or 6.
- `aeneas-lean-checker/tests/Generated/Bitwise.lean` — revert hand-patch to `(16 : Std.Isize)` back to natural `16#isize`.
- `tests/lean-checker/differential/{src/lib.rs,src/model.rs,src/aggregates_basic_model.rs,src/reborrows_model.rs,tests/diff.rs,.gitignore}` — harness expansion.
- `tests/lean-checker/lean-diff/{LeanDiff/BitwiseRunner.lean,LeanDiff/Main.lean,lakefile.lean,rust-runner/src/main.rs,scripts/run-diff.sh,generated/bitwise.lean,generated/constants.lean}` — bitwise wiring + constants regen.
- `tests/llbc/{bitwise,calls,compare_simple,constants,incr_cert}.cert.json` — newly tracked v6 certs for the differential harness.
- `scripts/{regen-diff-models.sh,check-vertical-slice.sh}` — regen helpers.
- `documentation/differential-testing-plan.md` — known-unblockers updated, fixture counts bumped.

**No files under `aeneas-lean-soundness/` or `aeneas-lean-checker/AeneasCheck/Theorems/` were touched.**

---

## Session 3 (2026-05-18) — Phase 4a + early Phase 4b

### What landed (top 5 commits over `304137c5`)
```
a1daa9c5 Phase 4b diff: scale G_rust — add scalars + demo fixtures (15 new proptests)
fede2492 lean-diff: wire constants.lean into the harness (Phase 4a wire-up)
c59c91ed Phase 4a-3 + 4a-5: typed placeholder for ADT return slots + caller-decl topo sort in LeanEmit
e03f1aa5 Phase 4a-2 LeanEmit: balanced-brace sanitisation for def + call paths
f23a6175 Phase 4a-1 shim: add HAdd/HSub/HMul I32 (Result I32) instances
```

### Phase 4a outcome
All four LeanEmit/shim gaps the Phase 4 prompt flagged from Session 2 are now closed:

| Carry-forward (per Session 2 §"Carry-forward LeanEmit follow-ups") | Resolution |
|---|---|
| Bare `(x1 + x2)` on i32 `add` — no `HAdd I32 I32 (Result I32)` shim | `f23a6175` adds the instance (Add/Sub/Mul) |
| Brace-decorated `def {constants.Wrap<T>}.new` | `e03f1aa5` rewrites `sanitizeCallName` to balanced-brace, applied to both call heads and def names |
| `Pair`-typed record literal `ok`-applied as a scalar (S3) | `c59c91ed` adds `placeholderPExprOfWith tdm` (ADT-aware) + a body-tail post-walk substitution; S3 now emits `ok { x := 0#u32, y := 0#u32 }` (typechecks; value still placeholder pending cert-walker fix) |
| `V` struct length `Array T 0#usize` + V.LEN body | `c59c91ed`'s body-tail typedDefault picks Usize via `localTypes[0]`; V.LEN now emits `ok 0#usize` (was `ok 0#u32`). The struct decl `structure V (T : Type) where x : Array T 0#usize` is unchanged (const-generic `N` still dropped); the cert-walker doesn't surface const-generic params today |

Plus the topological-sort fix `c59c91ed` discovered along the way: the cert emits decls in source order, which put `def Y` (line 42) before `def Wrap.new` (line 55) in the emit; Lean rejected the call as an unknown constant. `topoSortCallerDecls` in `LeanEmit.lean` now DFS-emits each caller decl after its sibling-decl deps. Self-recursive defs (`partial_fixpoint`) are not treated as self-dependencies; mutual recursion is out of scope (would need `mutual` blocks — no fixture exercises it yet).

constants.lean now compiles cleanly against the shim and is wired into the lean-diff harness via `LeanDiff.ConstantsRunner` (29 vectors: 9 incr + 8 add + 5 mk_pair0 + 7 nullary const/static). G_lean total: 119 / 119 byte-identical.

### Phase 4b outcome (partial)
Sweep of the 89 cert fixtures via `aeneas-check --rust-model + rustc --crate-type=lib --emit=metadata`:
- 7 fixtures pass rustc standalone (the originally-wired set: incr_cert, compare_simple, calls, bitwise; plus `issue-815-...`, `mutually-recursive-traits`, `names`, `switch_test` — those three have empty / placeholder-only models, so they're not differential-testable).
- 82 fixtures fail rustc standalone, mostly due to (a) emitter quirks like `u32::default` (missing parens) or `SharedWrapper<'a, T>::create` (lifetime in path) or `NumOrZero.Variant` (instead of `::Variant`), or (b) the rust-model referencing the source crate's qualified path (`<crate>::<fn>`) which doesn't resolve in the standalone differential crate.

Hand-curated 15 new differential-testable functions across 2 new fixtures (`scalars` + `demo`):
- scalars: 13 fns (wrapping_add/sub × {u32,i32}, shift_left/right × {u32,i32}, add_and, rotate_left/right × {u32,i32}). Skipped: casts, `_default`, match-on-usize, `_use_bits`.
- demo: 2 fns (`mul2_add1`, `incr`). Skipped: closure-returning `choose`/`list_nth`, intra-fixture-call `use_*` (would need `mod demo` wrap in harness).

G_rust total: 18 → 33 proptests across 9 fixtures.

### Coverage matrix snapshot

| Fixture | G_rust | G_lean | C_lean (against shim) |
|---|---|---|---|
| incr_cert | ✓ 1/1 | ✓ 16/16 | ✓ |
| compare_simple | ✓ 3/3 | ✓ 22/22 | ✓ |
| calls | ✓ 2/2 | ✓ 22/22 | ✓ |
| bitwise | ✓ 5/5 | ✓ 30/30 | ✓ |
| constants | ✓ 5/5 | ✓ 29/29 | ✓ (S3 / V.LEN compile via placeholder) |
| aggregates_basic | ✓ 2/2 | (skip, ADT runner) | n/a |
| reborrows | ✓ 1/1 | (skip, ADT runner) | n/a |
| scalars | ✓ 13/13 | (skip — shim) | partial |
| demo | ✓ 2/2 | (skip — shim) | partial |
| **Total** | **33 proptests / 9 fixtures** | **119 vectors / 5 fixtures** | 5/89 |

### Carry-forward into Session 4

The two highest-leverage items (each unblocks ≥1 fixture's G_lean wire-up):

1. **scalars G_lean shim work.** Add `HShiftRight U32 I32 (Result U32)` and `HShiftRight I32 I32 (Result I32)` (and the `Shl` counterparts) to RuntimeShim. The cert emits `2#i32` as the shift rhs even though Rust's `>> 2` parses as a `usize` shift (Charon's IR uses isize/i32 for the shift constant). After the shim adds, `scalars.lean` can be wired into `LeanDiff.ScalarsRunner`. Budget: ~40 LOC.

2. **demo G_lean shim work.** Same pattern — the pure-bitwise `let t0 ← (x2 &&& x1)` shape in `add_and` (and elsewhere) binds a pure-typed expression via `←` against a Result-monadic let; either add a `Result`-typed shim instance for `HAnd U32 U32 (Result U32)` (would shadow the existing pure form — see the Std.lean comment block; opt for a `pure_lift` wrapper in the cert emitter instead) or relax the cert emitter to render bare `let t0 := ...` for pure binops. Decide which.

Then a follow-up:

3. **Cert-walker fix for `S3`-class placeholders.** The cert events for `static X = Y` (where Y is itself a static) should write `vm[0] := <Y's pure expr>`, not leave it empty / fall back to a placeholder. The right side has already been computed by the time the assignment is executed; the walker just isn't threading it through. Tracking down the Forward.lean event for "EvAssign from a global initializer" is the entry point. Budget: half a day; needs a careful look at the cert JSON for constants.

4. **Continue Phase 4b sweep.** Three fixtures the standalone-rustc sweep skipped but that probably work with a small `mod <crate>` wrap in the harness: `demo::use_*`, `no_nested_borrows::cast_*`, `paper::ref_incr`. Budget: ~1 hour per fixture (model copy + per-fn proptest).

### Operational notes (Session 3 specifics)
- **No agent dispatches this session.** All work was done inline in the diff-test worktree. Worktree HEAD stayed on `aeneas-lean-certificate-diff-test`; no contamination of the parent or any of the 7 still-locked `agent-*` worktrees.
- **`aeneas-check` rebuilt from this worktree's source** at the start of each Phase 4a sub-task. The Phase-2 lesson ("pre-built binaries can lie") was honoured — never trusted the May 18 10:02 timestamp on the worktree's `.lake/build/bin/aeneas-check`.
- **No files under `aeneas-lean-soundness/` or `aeneas-lean-checker/AeneasCheck/Theorems/` touched.** Files modified live in `RuntimeShim/`, `Backends/{LeanEmit, Pretty}.lean`, `Translate/Forward.lean`, and the test-harness tree. The M10 agent's parent-branch work was not disturbed.

---

## Session 4 (2026-05-18) — Phase 4b Items 1 + 4

### What landed (top 3 commits over `ea642bdd`)
```
644e4336 Phase 4b Item 4a: scale G_rust — demo intra-crate calls (+2 proptests)
c84781e4 Phase 4b Item 4b: RustEmit Type.Ctor → Type::Ctor + enum fixtures
6539a087 Phase 4b Item 1: scale G_lean — add scalars fixture (+105 vectors)
```
Plus one merge of `aeneas-lean-certificate` mid-session (M10.x.3/4/5 axiom-drop commits from the parent).

### Item 1 outcome — `scalars.lean` wired into G_lean

Two emit-side changes + a batch of shim fills:

| Layer | Change | File |
|---|---|---|
| LeanEmit | Detect pure-binop heads (`BitXor`/`BitAnd`/`BitOr` + comparisons) on `letIn` RHS; emit `let t := …` instead of `let t ← …`. Pure bitwise resolves to Lean's `HXor UInt32 UInt32 UInt32` etc.; the `←` bind otherwise fails to elaborate against the shim. | `Pure/Pretty.lean` |
| Shim | `HShift{L,R} {U32,I32} I32 (Result …)` — Charon types short-literal shift rhs as `i32`, not `usize`. | `RuntimeShim/Aeneas/Std.lean` |
| Shim | `core.num.I32.wrapping_{add,sub,mul}`, `core.num.{U32,I32}.rotate_{left,right}`. | same |
| Shim | `HAdd/Sub/Mul Isize Isize (Result Isize)` (match_isize), `core.default.{U32,I32}.default` (`Default::default` lowering). | same |
| Shim | `CoeHead U32→U16 / U16→U32 / U32→I16 / I16→U32` — cast placeholders so the file imports; the runner does NOT exercise these (cert drops the cast op). | same |

`LeanDiff.ScalarsRunner` exercises 13 differential-testable fns × ~5 vectors (wrapping_add/sub × {u32,i32}; shift_left/right × {u32,i32}; add_and; rotate_left/right × {u32,i32}) = 105 new vectors. G_lean: 119 → 224, all byte-identical.

### Item 2 deferred — demo.lean

The Session-3 handoff predicted Item 2 in ~1 hour, but `demo.lean` regen surfaces several emit gaps beyond the let-bind fix:

- `@[discriminant isize]` attribute on the `CList` inductive (Lean doesn't know `discriminant` as a registered attr).
- `Std.Usize.Insts.DemoCounter.incr` is declared returning `Result (Std.Usize × (Unit → Std.Usize))` but the `Counter` trait field expects `Self → Result Std.Usize` — declarer/field signature mismatch.
- `list_nth` / `list_nth_mut` / `list_tail` / `list_nth1_loop.body` emit broken bodies (`ok ()` where `T` expected, `if x1` on a non-bool scrutinee, undefined free variable `s33` / `t3`, `partial_fixpoint` on a non-recursive body).
- `choose` returns a closure (M12.2a placeholder territory).

The five differential-testable fns (`mul2_add1`, `incr`, `use_mul2_add1`, `use_incr`, `mod_add`) can't be wired in until the surrounding broken defs compile. Defer to a future session — would need a per-decl skip list in the emit pipeline, or a per-fixture include-only filter.

### Item 4 outcome — Phase 4b G_rust sweep (+6 proptests)

**Item 4b — enum-ctor path fix:** `PExpr.toRust`'s `.var` and `.app` head cases were not rewriting Lean-style `Sign.Pos` / `NumOrZero.Num` to Rust's `Sign::Pos` / `NumOrZero::Num`. `matchE` already handled the arm-pattern side; the value-construction side was missed. New `rustifyPath` helper: `sanitizeRustPath` (brace strip) then `.` → `::`. Safe because the only synthesised `.` in head strings come from `Forward.variantPExpr`'s `s!"{adtName}.{variantName}"`.

Unblocked fixtures (4 new proptests in `enums_basic` + `enums_payload`):
- `enums_basic::flip` (3-variant nullary enum, match-arm round trip).
- `enums_payload::value` (payload-bearing match arm).
- `enums_payload::wrap` (payload ctor call).
- `enums_payload::zero` (nullary ctor ref).

**Item 4a — demo intra-crate calls:** Wrapped the demo model fns in `pub mod demo { ... }` (mirrors the `aggregates_basic` / `reborrows` pattern). Inside-the-module call `self::mul2_add1` substitutes for the cert's `demo::mul2_add1` (Rust scoping; semantic logic untouched). Two new proptests:
- `demo::use_mul2_add1` — intra-crate call resolution.
- `demo::mod_add` — Aeneas modular-add via wrapping_sub + shift mask (exercises `>> 16i32` on `u32` via Rust's `Shr<i32> for u32` impl).

**Item 4c (cast keyword) deferred.** The cast emit gap is deeper than the prompt suggested: `cast_u32_to_i32_model(x1: u32) -> i32 { x1 }` is *syntactically* wrong Rust (can't return `u32` as `i32` without coercion). Adjacent fn `get_max_model` has another emit bug — uses `if x1 { … }` on a `u32` scrutinee where the cert should have piped the precomputed `t0 : bool`. Both need cert-walker fixes, not just RustEmit polish.

### Coverage matrix snapshot (post-Session 4)

| Fixture | G_rust | G_lean | C_lean (against shim) |
|---|---|---|---|
| incr_cert | ✓ 1/1 | ✓ 16/16 | ✓ |
| compare_simple | ✓ 3/3 | ✓ 22/22 | ✓ |
| calls | ✓ 2/2 | ✓ 22/22 | ✓ |
| bitwise | ✓ 5/5 | ✓ 30/30 | ✓ |
| constants | ✓ 5/5 | ✓ 29/29 | ✓ (S3 / V.LEN compile via placeholder) |
| aggregates_basic | ✓ 2/2 | (skip, ADT runner) | n/a |
| reborrows | ✓ 1/1 | (skip, ADT runner) | n/a |
| scalars | ✓ 13/13 | ✓ 105/105 | ✓ (casts compile via Coe; runner skips them) |
| demo | ✓ 4/4 | (skip — see Item 2 deferral) | partial |
| enums_basic | ✓ 1/1 | — | n/a |
| enums_payload | ✓ 3/3 | — | n/a |
| **Total** | **39 proptests / 11 fixtures** | **224 vectors / 6 fixtures** | 6/89 |

### Bugs found by the differential pipeline (Session 4)

The harness as a whole has so far surfaced one *real* backend bug and several emit gaps requiring shim or emit-side patches. No "model returns wrong value for differential-testable input" bugs detected — every wired proptest / vector passes.

| Class | Bug | Fix layer |
|---|---|---|
| Real backend bug | `PExpr.toRust` left Lean-style `Sign.Pos` / `NumOrZero.Num` paths untouched in `.var` and `.app` head; Rust requires `::`. Blocked enum fixtures from G_rust. | RustEmit (`rustifyPath`) |
| Emit-side gap | Cert walker emits monadic-let bind on pure-binop RHS; bind fails to elaborate (`HXor U32 U32 U32` is pure, not Result-lifted). | LeanEmit (`Pure/Pretty.lean`) |
| Shim gaps | 13 missing instances (HShift U32/I32 I32, HAdd Isize, wrapping_/rotate_ helpers, default::, Coe casts). | `RuntimeShim/Aeneas/Std.lean` |
| Known cert-walker gaps (not fixed this session) | `S3`-class statics emit placeholder value rather than reading the dependent static; `match_isize` body fold; `_use_bits` lowering; `cast_*` op drops; `get_max`-class branch variable confusion. | Forward.lean / cert event walker |

### Carry-forward into Session 5

Priority order:

1. **Cert-walker `S3`-class fix** (~half day): the EvAssign-from-EvGlobal walker drops the RHS. Item 3 of the Session-4 handoff carries over verbatim; the cert JSON for `constants` is the canonical source.

2. **demo.lean wire-in** (~half day, was Item 2): needs an emit-side per-decl skip list (or a `--only` CLI flag) so the 5 well-emitted fns can be exported without dragging the broken ones along. Alternative: a per-fixture include-only Lake setup, which keeps the emitter unmodified.

3. **More mod-crate wraps** (~1 hour per fixture): `nested_borrows::call_inner_mut` (skipping closure-returning callees), `no_nested_borrows::test2` / `test3` (skipping the assertion bodies); `paper::ref_incr`.

4. **Cast keyword fix** (~half day): `RustEmit` needs a cast-head detection in `.app`. Same shape as the `binopRustOp` table — add `binopRustCast : String → Option (String × String)` or similar — and emit `(<inner> as <target>)` instead of dropping the op.

5. **Phase 2 (G_byte sweep)**: lowest-effort highest-signal next gate. Extend `scripts/compare-backends.sh` from single-fixture interactive to sweep-mode with per-fixture allowed-divergence list.

### Operational notes (Session 4 specifics)
- **No agent dispatches.** Inline work in `/Users/karthik/aeneas/.claude/worktrees/diff-test`. Worktree HEAD stayed on `aeneas-lean-certificate-diff-test`.
- **One mid-session merge** of `aeneas-lean-certificate` (`04b675ff` `M10.x.5`) — pure soundness territory; clean merge, no conflicts in diff-test files.
- **Pre-built binaries lesson honoured.** Rebuilt `aeneas-check` from this worktree's source at every regen point.
- **No files under `aeneas-lean-soundness/` or `AeneasCheck/Theorems/` touched.** Changes localised to `RuntimeShim/`, `Backends/{RustEmit,Pretty}.lean`, the lean-diff harness, the differential proptest harness, and the docs.
