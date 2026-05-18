## Plan: Four-artifact differential testing rollout (Phases 0 + 1)
## Started: 2026-05-18 (Session 2)
## Last action: Phase 0 + Phase 1A + Phase 1B + Phase 1C landed on `aeneas-lean-certificate-diff-test`. Both harnesses green: G_rust 18/18 proptests; G_lean 90 == 90 byte-identical.
## Phase: Phases 0+1 DONE; Phases 2–5 remain.
## Next commit: Phase 2 (G_byte sweep extension) — separate session.

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
