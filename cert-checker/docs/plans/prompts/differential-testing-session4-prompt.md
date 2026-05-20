# Handoff prompt — Session 4: finish Phase 4b + start Phase 2 (G_byte sweep)

Paste into a fresh Claude Code session at `/Users/karthik/aeneas`.

---

You are continuing the four-artifact differential testing rollout for
Aeneas on branch `aeneas-lean-certificate-diff-test`. Phases 0 + 1 +
4a are complete; Phase 4b is partial (G_rust scaled to 33 proptests /
9 fixtures, G_lean still at 5 fixtures). Your job is the next
increment along the same axis: scale G_lean to match G_rust, then
close out Phase 4b by sweeping a few more `mod <crate>`-wrappable
fixtures into G_rust.

Work in the worktree at `/Users/karthik/aeneas/.claude/worktrees/diff-test`,
NOT in the parent tree.

## Boot sequence — read in order

1. **Plan**:
   `documentation/plans/differential-testing-plan.md` — read §"Gates"
   and §"Phased rollout". The Session 3 commits closed all four
   Phase-4a carry-forward LeanEmit gaps; §G_lean "Known unblockers"
   now lists the new remaining work for *next* session.
2. **Progress note**:
   `documentation/plans/differential-testing-progress.md` —
   §"Session 3 (2026-05-18)" has the per-commit summary, the coverage
   matrix snapshot, and §"Carry-forward into Session 4" with the four
   prioritised items.
3. **Recent commits on the branch**:
   ```
   git log --oneline aeneas-lean-certificate-diff-test -10
   ```
   Top of the log should show `ea642bdd docs: Phase 4c — …`
   then the five Session-3 fix commits (`f23a6175`, `e03f1aa5`,
   `c59c91ed`, `fede2492`, `a1daa9c5`). Below those: the Phase 0+1
   stack from Session 2 and the M10 commits from the parent merge.
4. **Existing harnesses**:
   - G_rust: `tests/lean-checker/differential/` — 33 proptests / 9 fixtures
   - G_lean: `tests/lean-checker/lean-diff/` — 119 vectors / 5 fixtures

## Critical operational constraints

Same as Session 2/3. Re-stated verbatim because they keep mattering:

- **The M10 soundness agent commits to `aeneas-lean-certificate` (the
  parent branch).** All your work belongs on
  `aeneas-lean-certificate-diff-test`. Do NOT touch any file under
  `aeneas-lean-soundness/` or `aeneas-lean-checker/AeneasCheck/Theorems/`.
  The parent gets merged into your branch every now and then; never
  the other way without explicit user say-so. Treat the parent as
  read-only input.

- **Worktree isolation is fragile.** Three of four agents dispatched
  in Session 2 found their isolated worktrees pinned to a stale
  release-nightly commit (`004e11fe`) predating
  `aeneas-lean-checker/`. **For every agent dispatch with
  `isolation: worktree`**: the FIRST Bash call must be
  `echo "[status] boot" && pwd && git log -1 --oneline && git branch --show-current`.
  If HEAD is `004e11fe` or any commit not in the diff-test ancestry,
  the agent MUST abort with a clear report — NOT fall back to editing
  the live worktree. Session 3 did all work inline (no agent
  dispatches), so the issue didn't recur; if you choose to
  parallelise, this guard is still mandatory.

- **Pre-built binaries can lie.** Session 3 rebuilt aeneas-check from
  the diff-test worktree's source before every regen. Do the same —
  the May-18 timestamp on `.lake/build/bin/aeneas-check` is no
  evidence that the binary contains diff-test-only fixes.

- **Cert JSON v6 is the current format.** `bin/aeneas -emit-cert`
  emits v6; the cert parser
  (`aeneas-lean-checker/AeneasCheck/Json/Parser.lean`) has full v6
  support after Phase 0's `235d8753`.

- **Streaming-watchdog guard**: every Bash call should be preceded by
  an `echo "[status] ..."` line so the 600s no-stream-output watchdog
  doesn't kill long builds.

- **Pre-built binaries that are safe to use by absolute path**
  (assuming you don't need a diff-test-only fix):
  - `/Users/karthik/aeneas/bin/aeneas`

## Scope of Session 4

Four items, in priority order. Land #1 + #2 (the two G_lean shim
fixes) in the first half-day; #3 + #4 if time permits.

### Item 1 — `scalars.lean` shim adds + wire-in (~2 hours)

`scalars.lean` (regenerated from `tests/llbc/scalars.cert.json`) fails
to typecheck against the RuntimeShim on these patterns:

  - `(x1 >>> 2#i32)` / `(x1 <<< 2#i32)` — applied to *both* `U32` and
    `I32` operands. The cert types the shift rhs as `i32` (not
    `usize`), so the existing `HShiftRight U32 Usize` instance
    doesn't fire.
  - `let t0 ← (x2 &&& x1)` — pure bitwise on `U32` (the shim's
    "M9.5h" comment block explains why this is *not* shimmed as a
    `Result`-returning instance: the standard Aeneas backend uses
    `ok (x1 ^^^ x2)` in tail position, not `let t0 ← ...` mid-block).

For the shift side, add to `aeneas-lean-checker/RuntimeShim/Aeneas/Std.lean`:

  ```lean
  instance : HShiftLeft U32 I32 (Result U32) :=
    ⟨fun a n => .ok (UInt32.shiftLeft a (UInt32.ofNat n.toNat))⟩
  instance : HShiftRight U32 I32 (Result U32) :=
    ⟨fun a n => .ok (UInt32.shiftRight a (UInt32.ofNat n.toNat))⟩
  instance : HShiftLeft I32 I32 (Result I32) :=
    ⟨fun a n => .ok (Int32.shiftLeft a (Int32.ofInt n.toInt))⟩
  instance : HShiftRight I32 I32 (Result I32) :=
    ⟨fun a n => .ok (Int32.shiftRight a (Int32.ofInt n.toInt))⟩
  ```

(Note: `n.toInt` if `n : Int32` — confirm via `lean_hover_info`.)

For the let-bind side, two paths:
  (a) **Cheap**: in `aeneas-lean-checker/AeneasCheck/Backends/LeanEmit.lean`
      (or `Pretty.lean`), detect the `let t0 ← <pure binop>` shape and
      emit `let t0 := <pure binop>` instead (non-monadic let). Pure
      binops are recognisable by their `binopInfix` lookup. This is
      cosmetic — the cert is putting a pure value through `←` because
      the walker doesn't distinguish.
  (b) **Heavier**: add `Result`-typed instances for `HAnd`/`HOr`/`HXor`
      on `U32 U32 (Result U32)`. The shim comment warns this shadows
      the pure form used by `ok (x1 ^^^ x2)` in tail position — would
      regress the bitwise fixture's byte-identity. Don't do this
      unless you also add the dual emit path.

Recommend approach (a). Once both fixes land, regen
`tests/lean-checker/lean-diff/generated/scalars.lean`, wire it into
`tests/lean-checker/lean-diff/lakefile.lean` and `LeanDiff/Main.lean`,
create `LeanDiff.ScalarsRunner` mirroring `LeanDiff.BitwiseRunner`'s
shape (it has the closest fixture surface — scalar in, scalar out,
mostly `U32`/`I32`), and add matching Rust-oracle vectors in
`tests/lean-checker/lean-diff/rust-runner/src/main.rs`.

Target: +60 vectors from scalars (13 fns × ~5 vectors each minus the
ADT/closure ones already skipped).

### Item 2 — `demo.lean` wire-in (~1 hour)

`demo.lean` has the same `let t0 ← (x1 + x1)` pure-let-bind issue as
scalars (this time on arithmetic, not bitwise). If approach (a) from
Item 1 lands (recognise pure binops at the let-bind site), demo's
`mul2_add1` and `incr` should compile against the shim with no
further changes.

Wire `demo.lean` in. Skip the closure-returning `choose` and
`list_nth` per Session 3 (M12.2a-placeholder territory). For the
intra-fixture calls (`use_mul2_add1`, `use_incr` reference
`demo::mul2_add1`), the standard backend's emit would route through
the surrounding namespace — verify the cert pipeline does the same
after Item 1's let-bind fix lands.

Target: +15 vectors from demo (mul2_add1 × 5, incr × 5, use_* × 5 if
they emit cleanly).

### Item 3 — Cert-walker fix for `S3`-class placeholders (~half day)

This is a different layer of fix than Items 1+2 — at the
**translator** (Forward.lean) layer, not the emitter or shim.

Symptom: `const Y = Wrap::new(2)` emits the correct call shape
`(constants.Wrap.new 2#i32)`, but `static S3: Pair<u32, u32> = P3`
emits `ok { x := 0#u32, y := 0#u32 }` — typechecks (after Session 3's
Phase 4a-3 fix) but the value is wrong (P3 is `{ x: 0, y: 1 }`).
The cert walker is dropping the right-hand side for static-from-static
assignments.

Where to look: `aeneas-lean-checker/AeneasCheck/Translate/Forward.lean`'s
event walker. The `EvAssign` case has several sub-branches for
different LHS/RHS shapes. The S3-class is "EvAssign where RHS is a
read of a global". Trace through the cert JSON for the constants
fixture (`/tmp/sweep-rust-models/constants.rs` was generated this
session — the corresponding `.cert.json` is at
`tests/llbc/constants.cert.json` and is the source-of-truth). Look
for the S3 def's events and figure out why `vm[0]` is being set to
the U32 placeholder instead of `(constants.P3)`.

Hypothesis: the cert has a `EvGlobal` or `EvCall(global-getter)`
event that the walker isn't handling. Confirm by inspecting the
events for X1 (`const X1: u32 = u32::MAX`) and Q2 (`const Q2: i32 =
Q1`) — both are simpler than S3 and exhibit the same pattern (their
emit is `ok 0#u32` / `ok 0#i32` placeholders despite the source
having concrete values).

Target: when this lands, the constants harness's skipped fns from
Session 3 (X1, YVAL, mk_pair1, P1, P3, S3, S4, Q2, Q3, S2,
get_z1/get_z1.Z1/get_z2, use_v/V.LEN) become differentially testable.
Likely adds +30 vectors to the constants harness.

### Item 4 — Continue Phase 4b sweep (~3-4 hours)

The Session-3 sweep found 7 standalone-rustc-passing fixtures, of
which only 4 are differentially useful (the other 3 are
placeholder-only). Three categories of additional fixtures look
within reach:

  (a) **`mod <crate>` wrap candidates**: fixtures whose model
      references `<crate>::<fn>` for intra-fixture calls. Adding a
      tiny `mod <crate>` block at the top of the per-fixture include
      lets the call resolve. Candidates from the Session-3
      classification: `demo::use_mul2_add1`, `demo::use_incr`,
      `nested-borrows::call_inner_mut` (if you skip the
      closure-returning callees), `no_nested_borrows::test2` /
      `test3` (if you skip the assertion bodies).

  (b) **Enum fixtures**: `enums_basic`, `enums_payload`. The current
      cert emit uses `NumOrZero.Num` instead of `NumOrZero::Num` in
      RustEmit (a known emitter gap). Fix in
      `aeneas-lean-checker/AeneasCheck/Backends/RustEmit.lean` —
      `.matchE` already converts `.` to `::` for the ctor; the
      `.app head` case in PExpr.toRust may need the same treatment
      for constructor application. After the fix, `enums_payload`'s
      `value`, `wrap`, `zero` become testable.

  (c) **Cast fixtures**: `no_nested_borrows::cast_*` and
      `scalars::*_as_*`. The current emit drops the `as` keyword
      (`x1 as u16` becomes `x1`, which doesn't compile when the
      source / model types differ). Fix in
      `aeneas-lean-checker/AeneasCheck/Backends/RustEmit.lean`'s
      `PExpr.toRust` `.app` head case — detect a cast head and emit
      `(<inner> as <target_ty>)`.

Pick (a) for the quickest win; (b) and (c) each unblock multiple
fixtures and might be worth dispatching to subagents in parallel.

Land each fixture as its own commit so a regression on one doesn't
block the others.

Target: +5-8 fixtures, +20-30 proptests in G_rust.

## What's NOT in this handoff

- **Phase 2** (G_byte sweep extension) — still deferred.
- **Phase 3** (G_rfl harness) — still deferred.
- **Phase 5** (single-command sweep + CI integration) — still
  deferred.

These are subsequent sessions. If by end-of-Session-4 you've cleared
Phase 4b to ≥25 fixtures in G_rust, the next Session should pick
Phase 2 (G_byte sweep) since that's the lowest-effort highest-signal
gate after Phase 4 stabilises.

## Done condition for this session

- Item 1 complete: scalars.lean wired into lean-diff, ≥30 new
  vectors passing byte-identical.
- Item 2 complete: demo.lean wired into lean-diff, ≥10 new vectors
  passing byte-identical.
- Either Item 3 OR Item 4 complete (your choice based on the
  morning's progress). Item 3 is higher impact long-term; Item 4 is
  faster to land.
- `differential-testing-plan.md` §Gates fixture counts updated.
- `differential-testing-progress.md` appended with a Session 4 note.
- Branch ready to merge back to parent. Periodic merge of parent
  into your branch (`git merge aeneas-lean-certificate`) keeps the
  eventual merge-back cost low — do it at least once mid-session.

## Push policy

Local commits only. Do NOT push to origin. The user pushes manually
when ready, after running `/lean4:checkpoint` to satisfy the Lean
guardrail hook.
