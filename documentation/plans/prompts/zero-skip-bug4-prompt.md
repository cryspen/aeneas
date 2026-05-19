# Bug 4 — per-local type tracking (drive c_lean from 36/89 to ~46/89)

Paste into a fresh Claude Code session at
`/Users/karthik/aeneas/.claude/worktrees/diff-test` on branch
`aeneas-lean-certificate-diff-test`. Execute autonomously: commit
between sub-bugs, only stop on the documented hard-stop conditions.

---

You are resuming the zero-skip campaign. The 2026-05-19 translator-
fixes session closed Bugs 1, 2, 3, 5 + two small wins (Aggregate-array
propagation, Array placeholder), moving the **`c_lean` gate** from
**30/89 → 36/89 fixtures** (**329/3143 → 451/3143 decls**). See
`documentation/plans/zero-skip-plan.md` §"Translator-fixes session"
for the commit-by-commit log.

The remaining 53 failing fixtures share a single dominant root cause:
**the cert walker's per-local type tracking is wrong**. Local types
get stale on EvAssign re-bindings, trait-bound `Self` parameters fall
through to the generic-type-var without resolving to the impl's
ground type, and `lookupSymExpr` returns expressions whose inferred
types don't match the call-site context. Symptoms across fixtures:
`Application type mismatch`, `Type mismatch`, `failed to synthesize
HSub U32 Enum`-style errors.

Your job is to fix the walker — not paper over the symptoms with
shim casts.

## Boot sequence

1. ```bash
   cd /Users/karthik/aeneas/.claude/worktrees/diff-test
   pwd && git log -1 --oneline && git branch --show-current
   ```
   HEAD should be `3f8d660f` (Aggregate-array propagation + Array
   placeholder) or later. Abort if not.

2. Read `documentation/plans/zero-skip-plan.md` §"Translator-fixes
   session — close" — the prior session's commit log and the
   carry-forward notes that scope Bug 4.

3. Read `documentation/plans/prompts/zero-skip-translator-fixes-prompt.md`
   §"Bug 4 — Per-local type tracking returns wrong type at call sites"
   — the original framing that landed in the carry-forward.

4. Read `documentation/plans/prompts/zero-skip-relaunch-prompt.md`
   §"Operational rules" for worktree isolation, gate-measurement
   protocol, local-commits-only.

5. Rebuild + baseline:
   ```bash
   (cd aeneas-lean-checker && lake build aeneas-check)
   cargo build --manifest-path tools/meta-harness/Cargo.toml --release
   ./tools/meta-harness/target/release/meta-harness \
     --sweep tests/llbc --gates c_lean --report-json /tmp/cl-before.json
   ```
   Expected: `c_lean per-fixture pass: 36  fail: 53`,
   `per-decl pass: 451  fail: 2692`.

## The three sub-bugs

Bug 4 decomposes into three independently-attackable surfaces. Order
by `(fixtures unlocked) / (fix size)`. Each ends with one surgical
commit.

### Sub-bug 4a — `localTypes` goes stale on EvAssign re-bind

**Symptom.** `joins::call_choose` emits:
```lean
def call_choose (b : Bool) (x : Std.U32) (y : Std.U32) : Result (Std.U32 × Std.U32) := do
  let t0 ← b + 1#u32   -- Bool + 1#u32 — nonsense
  ok (x, y)
```
The cert's pre-call binop walks `local 4 := Add(local 1, 1)` where
`local 1` is `b : Bool` per the function signature, but in MIR layout
the locals shift: the binop should be on a *different* local that
was previously rebound to a `U32`. The walker is reading
`localTypes[1]` (the original Bool type) instead of the rebound
`U32` type.

`joins::use_enum`'s `x + e` (with `e : Enum`) is the mirror: the
walker emits a binop with an Enum operand because the local that
held a U32 was overwritten by an Enum-typed EvAssign and `localTypes`
never updated.

**Fix surface.** `aeneas-lean-checker/AeneasCheck/Translate/Forward.lean`:

* `walkEvent` for `.assign d rhs` (around line 913) — when `d.local_`
  has no projection (whole-local rebind) and the rhs has a known
  type that differs from `localTypes[d.local_]`, update `localTypes`.
  The rhs's type is recoverable from the `SymExpr` shape:
  `.symLit (.scalar k _)` → `litTy (.int k)`; `.symCopy p` /
  `.symMove p` → `localTypes[p.local_]` projected through
  `p.projection`; `.symVariant adtId _ _ _` → `tAdt adtId args`
  (args from the variant's struct decl). `lookupSymExpr` doesn't
  return the type, but the SymExpr itself carries enough info.

* `walkEvent` for `.copy s d` / `.move s d` (lines 894–912) — same
  rebind detection: when `d.local_`'s prior `localTypes[d.local_]`
  differs from `localTypes[s.local_]` (after projecting through
  `s.projection`), update.

**Unlocks.** Probably `joins`, plus several `loops-issues`-family
fixtures whose pre-loop binops bind into shifted temps.
Estimate: 2–4 hours. Expected: +3 to +5 fixtures.

### Sub-bug 4b — Trait-bound `Self` parameter resolution at call sites

**Symptom.** `static::read` emits:
```lean
def read {S : Type} (WithSliceInst : WithSlice S) (x1 : S) (i : Std.Usize) : Result Std.U16 := do
  (Slice.index_usize x1 i)
```
The Rust source is `s.get_slice()[i]` — the `s.get_slice()` call was
flattened into the cert as a direct call returning `Slice U16`, but
the walker resolved its result through `lookupPlace` and got `x1`
(the input local 1 = `s : S`) instead of the call's binding.

**Fix surface.**

* `Forward.lean::EvCall` handling — when a callee is a trait method
  (recognised by the `fn_name` containing `::{...}::` impl-pretty
  shape or by an `EvCallTrait` event variant if one exists), the
  return type at the call site should come from the trait method's
  declared signature *as instantiated for the impl's Self type*, not
  from the generic trait declaration's `Self` placeholder.

* `Driver.lean::traitImplOfLlbcTraitImpl` already carries the
  impl-method's substituted signatures (via Bug 1's
  `backSigOfLlbcWithVars` plumbing). Thread that signature through
  to the call-site type resolution — e.g. via a per-call-id map
  populated when the impl is processed and consulted by EvCall.

* `Forward.lean::lookupSymExpr` and `lookupPlace` may need a new
  per-call "this expression is the call's return value, not the
  fallback root-local" hint so the call's binding name is used
  even when the dst local doesn't match a simple `vm[L]` lookup.

**Unlocks.** `static`, plus the trait-impl-heavy fixtures `traits`,
`default`, `defaulted_method`, `blanket_impl`, `demo`. Estimate:
3–6 hours. Expected: +4 to +6 fixtures.

### Sub-bug 4c — Multi-element array aggregates

**Symptom.** Fixtures with `[a, b, c]`-style literals (≥2 elements)
emit `ok 0#u32` against `Result (Array T n)` because
`propagateRefsFromBlock` only handles the single-operand case and
`placeholderPExprOfWith` only handles `.tArray _ 1`.

Easy extension: emit `Aeneas.Std.Array.ofList #[<vm[op_0]>, …,
<vm[op_{n-1}]>]` (or equivalent). Add the shim helper alongside
`Array.singleton`.

**Unlocks.** Probably 1–2 fixtures (smaller arrays in
`arrays_basic`-class fixtures). Estimate: 1–2 hours. Expected:
+1 to +2 fixtures.

## Sequencing

Order by `(c_lean fixtures unlocked) / (fix size)`:

1. **Sub-bug 4a** (`localTypes` stale) — cheap, isolated to walker.
2. **Sub-bug 4c** (multi-element arrays) — tiny extension of prior
   session's small win.
3. **Sub-bug 4b** (trait-bound resolution) — biggest, hits the most
   fixtures, but the walker plumbing is the most invasive.

After EACH sub-bug fix, re-run the c_lean sweep, confirm per-fixture
count strictly increases, and commit. Do not batch into one commit.

## Per-sub-bug protocol

1. **Re-probe the canonical failing fixture** — run aeneas-check
   then `lake env lean` on the regen'd `.lean` and confirm the error
   matches the description above. If the error has changed, note it
   in `zero-skip-plan.md` before proceeding.

2. **Read the implicated translator code.** Don't guess at the fix;
   read the function's existing logic. Most paths have detailed
   comments referencing M9.5x / Session 7 / Bug N etc. — the
   comments often spell out the constraints the next change must
   honor.

3. **Implement the fix.** Touch only the files the sub-bug
   description identifies. If a fix needs broader plumbing,
   document and stop.

4. **Rebuild + sweep + diff.**
   ```bash
   (cd aeneas-lean-checker && lake build aeneas-check)
   ./tools/meta-harness/target/release/meta-harness --sweep tests/llbc \
     --gates c_lean --report-json /tmp/cl-after.json
   bash tests/lean-checker/lean-diff/scripts/run-diff.sh
   cargo test --manifest-path tests/lean-checker/differential/Cargo.toml --release
   ```
   Acceptance:
   - c_lean per-fixture count strictly increases vs the pre-sub-bug
     baseline.
   - Diff harness still PASS at 275 lines byte-identical.
   - 44 hand + 42 auto = 86 proptests all pass.

5. **Commit.** One sub-bug, one commit. Message format:
   ```
   aeneas-check: <sub-bug summary> (c_lean A→B)

   <one paragraph: what was wrong>

   <one paragraph: how the fix resolves it>

   c_lean per-fixture: A → B.
   c_lean per-decl:    AD → BD.
   Diff harness: PASS at 275 lines byte-identical.

   Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
   ```

6. **Update `zero-skip-plan.md`** under §"Translator-fixes session"
   with a new sub-entry describing the sub-bug + fix + delta.

## Hard stops

- **c_lean per-fixture count drops.** Revert the commit, investigate.
- **Diff harness FAIL** (Lean lines ≠ Rust lines, or byte-divergent).
  Revert. A translator change can regress this if it flips the emit
  shape for a fixture already in the diff harness.
- **A sub-bug takes 2x its estimate.** Stop, commit what's working,
  document the carry-forward in `zero-skip-plan.md`. Move to the
  next sub-bug.
- **Sub-bug 4b's plumbing turns out to require >2 file refactors.**
  Stop, scope a finer-grained next prompt, document the
  intermediate state, and return for next session.

## Operational constraints (unchanged)

- **Worktree isolation.** Always at
  `/Users/karthik/aeneas/.claude/worktrees/diff-test`. Never `cd` to
  `/Users/karthik/aeneas`. Every Bash call starts with
  `echo "[status] ..."` to feed the no-stream watchdog.
- **Parent-branch read-only.** Don't touch `aeneas-lean-soundness/`
  or `aeneas-lean-checker/AeneasCheck/Theorems/`.
- **Local commits only.** No push.

## "Done" looks like

- All 3 sub-bugs fixed and committed.
- c_lean per-fixture ≥ 46 / 89.
- c_lean per-decl ≥ 800 / 3143.
- A session-end entry in `zero-skip-plan.md` summarising deltas.

## "Almost done" looks like

- 2 of the 3 sub-bugs fixed.
- c_lean per-fixture in the low 40s.
- The remaining sub-bug has an updated carry-forward note.
- Stop and write a status report. Don't push.
