# Zero-skip continuation — fix the translator bugs that block c_lean 30→~60

Paste into a fresh Claude Code session at
`/Users/karthik/aeneas/.claude/worktrees/diff-test` on branch
`aeneas-lean-certificate-diff-test`. Execute autonomously: commit
between bugs, only stop on the documented hard-stop conditions.

---

You are resuming the zero-skip campaign. The 2026-05-19 relaunch
session moved the **`c_lean` gate** from **25/89 → 30/89 fixtures**
(**146/3143 → 329/3143 decls**) via shim/keyword-escape infrastructure
and two opportunistic fixes (`adt` collision, `Range` defaulted
start). See `documentation/plans/zero-skip-plan.md` § "Relaunch
session — 2026-05-19" for the commit-by-commit log.

The remaining 59 failing fixtures fail because of **translator bugs
in `aeneas-lean-checker/AeneasCheck/Translate/Forward.lean`** (and a
couple of sibling files). They are *not* shim gaps; they are real
emit-shape mistakes the cert walker is making. Your job is to fix
them — not paper over them, not skip them.

## Boot sequence

1. ```bash
   cd /Users/karthik/aeneas/.claude/worktrees/diff-test
   pwd && git log -1 --oneline && git branch --show-current
   ```
   HEAD should be the docs commit at the top of the relaunch
   session (`76caae48` or later). Abort if not.

2. Read `documentation/plans/zero-skip-plan.md` § "Relaunch session
   — 2026-05-19" — the prior session's summary. Skim the original
   `zero-skip-plan.md` Steps 1–7 too; many translator bugs share
   roots with those step's "BLOCKED" notes.

3. Read the relaunch prompt at
   `documentation/plans/prompts/zero-skip-relaunch-prompt.md` for
   the operational constraints — worktree isolation, parent-branch
   read-only zones, gate-measurement protocol, local-commits-only,
   etc. They all still apply.

4. Rebuild both binaries (the prior session's binaries may be
   stale relative to your changes):
   ```bash
   (cd aeneas-lean-checker && lake build aeneas-check)
   cargo build --manifest-path tools/meta-harness/Cargo.toml --release
   ```

5. Capture a fresh baseline before any change:
   ```bash
   ./tools/meta-harness/target/release/meta-harness \
     --sweep tests/llbc --gates c_lean \
     --report-json /tmp/cl-before.json
   ```
   Expected today: `c_lean per-fixture pass: 30  fail: 59`,
   `per-decl pass: 329  fail: 2814`.

## The remaining bugs, by translator-file fix surface

### Bug 1 — Trait `&mut self` impl-method shape (Cluster B / Step 4)

**Symptom.** For `trait Counter { fn incr(&mut self) -> usize; }`, the
emit produces:
```
def Std.Usize.Insts.DemoCounter.incr (self : Std.Usize)
    : Result (Std.Usize × (Unit → Std.Usize)) := do
  let t0 ← self + 1#usize
  ok (self, fun ret => t0)
```
but the trait declaration is:
```
structure Counter (Self : Type) where
  incr : Self → Result Std.Usize
```
So the impl method's return shape `Result (Self × (Unit → Self))` does
not match the trait's `Result Std.Usize`. Two things are wrong:

- The trait's method signature `Self → Result Std.Usize` is itself
  wrong — Aeneas's value-style translation of `&mut self -> usize`
  produces `Self -> Result (Usize × (Unit -> Self))`. Mainline
  aeneas's `Adt.lean` / similar show the correct shape.
- The impl-method body's `ok (self, fun ret => t0)` puts `self` in
  the forward slot, but the forward should be `t0` (the
  post-increment value) and the backward should be `fun ret => t0`
  (the new Self).

**Fix surface.**
- `aeneas-lean-checker/AeneasCheck/Translate/Driver.lean` —
  `traitDeclOfLlbcTraitDecl` (around the trait method's `ty`
  construction). The method's `ty` needs to reflect the
  forward+backward reshape, not the raw Rust signature.
- `aeneas-lean-checker/AeneasCheck/Translate/Forward.lean` —
  `translateFunWith`'s `retTy` and `buildBackwardTail`. When the
  function is identified as a trait-impl method body, consult the
  trait method's pretty-printed signature and shape the body's
  `ok ...` tail to match. The `fnPrettyByName` lookup already
  identifies impl methods; thread the trait method's `ty` alongside.

**Unlocks.** `demo` (`Counter` + `DemoCounter` + `DemoCounter.incr` +
`use_counter`), plus `traits`, `default`, `defaulted_method`,
`blanket_impl` if their compounds resolve. Estimate: 4–6 hours.
Expected: +4 to +6 fixtures.

### Bug 2 — Uninitialised local references (`xN`, `xN_post`, `tN`, `sN`)

**Symptom.** Body references a local like `x1`, `x1_post`, `t3`,
`s33` that was never bound by a prior `let`. Examples:
- `drop.lean:41`: `... { start := 0#usize, «end» := x1_post }` — but
  no `let x1_post ← ...` precedes.
- `arrays.lean:82`: `let s_post ← (ArrayIndexShared s i)\n  ok x1`
  — `x1` not bound.
- `arrays_defs.lean:28`: same family.
- `issue-803-self-in-array.lean`: `Unknown x1`.
- `demo.lean:98`: `Unknown s33` in a loop body.
- `demo.lean:135`: `Unknown t3` after a recursive call's tail is
  dropped.

**Root cause.** The forward walker's seed pass (`seedGlobalRefsFromBlock`
+ `seedGlobalRefsFromStatement` in `Forward.lean`) seeds locals
referenced by certain RvRef / Assign patterns, but misses several
cases:
- Post-state slots for `&mut`-borrowed inputs (`<param>_post`) aren't
  seeded when the cert's EvCall sequence produces them implicitly.
- Recursive-call return-value temps that the cert references as a
  read-only tail aren't bound when `pickBranchTail`'s heuristics
  return a local that wasn't itself written.

**Fix surface.** `aeneas-lean-checker/AeneasCheck/Translate/Forward.lean`:
- For `_post` slots: extend the EvCall path (around line 1276 where
  `postBindName` is computed) so the binding emit also records the
  name in `st.vm` for the caller-side input local.
- For tail-call temps: the `pickBranchTail` heuristic (used by the
  Assert-pair handler and arm-walker, around line 1956) needs to
  detect when a sub-walk's `lastWrite` points to a parent-scope
  local that the parent walk hasn't bound yet, and synthesise a
  binding rather than emitting the bare name.

**Unlocks.** `drop`, `arrays_defs`, `issue-803-self-in-array`,
`demo` (the `list_nth_mut`, `i32_id`, `list_tail` parts already
blocked per Step 3's BLOCKED notes — many share this root).
Estimate: 4–8 hours; expected: +3 to +6 fixtures.

### Bug 3 — Loop body emits `cont i` with unbound `i` (Step 5 second half)

**Symptom.** For loops where the body is match-bearing (not the
`while`-shaped Assert-pair), the wrapper emits:
```
def AVLNode.find_loop.body (self : AVLNode) : Result (ControlFlow () Bool) := do
  ok (cont i)
```
but `i` was never bound — the loop counter parameter was dropped
during body translation. Also `ControlFlow ()` has `()` (the value)
where `Unit` (the type) was expected: the cert walker is emitting
`()` as a type argument.

**Fix surface.**
`aeneas-lean-checker/AeneasCheck/Translate/Loops.lean::buildLoopBody`.
The prior session's Step 5 PARTIAL landed the wrapper-signature half;
the body-rewrite half is the carry-forward (see the `BLOCKED`
subsection of Step 5 in `zero-skip-plan.md`). The scaffold at
`aeneas-lean-checker/tests/Walker/loop_body_scaffold.py` documents
the expected body shape.

The `ControlFlow ()` issue: `Unit` is being lowered as the *value*
`()` instead of the *type* `Unit` in PTy → toLean. Find the call-
arg constructor in Forward.lean's loop-body emit (search for
`ControlFlow` or `cont`/`done`) and ensure the type argument uses
`PTy.unit` (which `toLean`s as `"Unit"`), not the value-level `()`.

**Unlocks.** `issue-134-loop-shared-borrows`, `issue-270-loop-list`,
`mini_tree`, `demo` (list_nth1), `loops-issues`, several others.
Estimate: 4–8 hours; expected: +4 to +6 fixtures.

### Bug 4 — Per-local type tracking returns wrong type at call sites

**Symptom.** Lots of `Application type mismatch` errors where the
expected type is correct but the *argument*'s inferred type is
nonsense:
- `static.lean:36`: `Slice.index_usize x1` with `x1 : S` (the
  generic type parameter) instead of `x1 : Slice U16`.
- `joins.lean:57`: `HAdd U32 Enum ?m` — adding a U32 to an Enum.
- `arrays.lean:102`: `Prod.mk s` with `s : Array T (Usize.ofNat 32)`
  but expects `T`.
- `iterators-scalar.lean`: similar shape errors.

**Root cause.** `Forward.lean::lookupSymExpr` (and the chain into
`localTypes`/`tdm` resolution) is returning the wrong PExpr when:
- The cert's `EvCopy` / `EvMove` propagated a place's type but a
  later EvAssign re-bound the local to a different-typed value
  without updating `localTypes`.
- A trait-bounded function's `Self` parameter is being passed
  through call sites that expect the trait method's actual `Self`
  ground type (the `WithSliceInst` indirection).

**Fix surface.** `Forward.lean`:
- `localTypes` updates need to happen on every EvAssign that
  changes the local's effective type, not just the initial bind.
- Trait-bound parameter resolution at call sites should consult
  the trait method's signature (overlaps with Bug 1's plumbing).

**Unlocks.** `static`, `joins`, `iterators-scalar`, `arrays`
(post-Bug-1 cleanup), `slices`, others. Estimate: 6–12 hours;
expected: +6 to +10 fixtures. This is the largest cluster.

### Bug 5 — Option / String type-emit gap

**Symptom.** `options.lean:24`:
```
def test_expect {T : Type} (x : Option T) (msg : Std.U32) : Result T := do
  (core.option.Option.expect x x)
```
- The Rust `msg : &str` is being lowered to `Std.U32` — fallback
  type when the translator doesn't know how to lower `&str`.
- The body call `expect x x` passes `x` twice instead of `(x, msg)`.

**Fix surface.** `Forward.lean::llbcTyToPTyWithVars` — add a case for
`TStr` / `&str` → `String`. Then the param's type changes to
`String`, the call's args resolve correctly via the standard
`lookupSymExpr` chain.

**Unlocks.** `options`, `paper` (which references String formatting),
several smaller fixtures. Estimate: 2–4 hours; expected: +1 to +3.

### Bug 6 — Field/method collision beyond `adt`

The prior session fixed `adt::Struct.len` (field/method name shared).
There may be additional collisions in other fixtures. The
`collisionRenames` map in `Driver.lean::translateCrate` handles the
detection; if no other fixture surfaces the same collision-shape, no
work is needed here. Confirm before declaring done.

## Sequencing

Order by `(c_lean fixtures unlocked) / (fix size)`:

1. **Bug 5** (Option/String) — cheap, isolated.
2. **Bug 3** (loop body second half) — scoped scaffold exists,
   ~4 hours.
3. **Bug 2** (uninitialised locals) — touches one walker file.
4. **Bug 1** (trait `&mut self` reshape) — half-day, but unlocks
   trait-heavy fixtures.
5. **Bug 4** (per-local type tracking) — largest, do last; many
   compounds with Bug 1's plumbing.

After EACH bug fix, re-run the c_lean sweep, confirm per-fixture
count strictly increases, and commit. Do not batch bugs into one
commit — keep them surgical.

## Per-bug protocol

For each numbered bug:

1. **Re-probe the canonical failing fixture** — run aeneas-check
   then `lake env lean` on the regen'd `.lean` and confirm the
   error matches the description above. If the error has changed,
   note it in `zero-skip-plan.md` before proceeding.

2. **Read the implicated translator code.** Don't guess at the
   fix; read the function's existing logic. Most of these
   translator paths have detailed comments referencing M9.5x /
   Session 7 / Step 3 etc. — the comments often spell out the
   constraints the next change needs to honor.

3. **Implement the fix.** Touch only the files the bug description
   identifies. If a fix needs broader plumbing, document it and
   stop.

4. **Rebuild + sweep + diff.**
   ```bash
   (cd aeneas-lean-checker && lake build aeneas-check)
   ./tools/meta-harness/target/release/meta-harness --sweep tests/llbc \
     --gates c_lean --report-json /tmp/cl-after.json
   bash tests/lean-checker/lean-diff/scripts/run-diff.sh
   cargo test --manifest-path tests/lean-checker/differential/Cargo.toml --release
   ```
   Acceptance:
   - c_lean per-fixture count strictly increases vs the pre-bug
     baseline.
   - Diff harness still PASS at 275 lines byte-identical.
   - 44 hand + 42 auto = 86 proptests all pass.

5. **Commit.** One bug, one commit. Message format:
   ```
   aeneas-check: <bug summary> (c_lean A→B)

   <one paragraph: what was wrong>

   <one paragraph: how the fix resolves it>

   c_lean per-fixture: A → B.
   c_lean per-decl:    AD → BD.
   Diff harness: PASS at 275 lines byte-identical.

   Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
   ```

6. **Update `zero-skip-plan.md`** under § "Relaunch session" with
   a new sub-entry describing the bug + fix + delta. Mark the
   matching Step (1–7) DONE/PARTIAL as appropriate.

## Hard stops

- **c_lean per-fixture count drops.** Revert the commit, investigate.
- **Diff harness FAIL** (Lean lines ≠ Rust lines, or byte-divergent).
  Revert. The shim fixes from the prior session shouldn't regress
  this, but a translator change might. Iterate.
- **A bug takes 2x its estimate.** Stop, commit what's working,
  document the carry-forward in `zero-skip-plan.md`. Move to the
  next bug.
- **3 fixtures cascade into the same DEEPER walker bug** beyond the
  ones described above. Stop, scope the new bug, document, and
  return for next session.

## Operational constraints (unchanged)

- **Worktree isolation.** Always at `/Users/karthik/aeneas/.claude/
  worktrees/diff-test`. Never `cd` to `/Users/karthik/aeneas`.
  Every Bash call starts with `echo "[status] ..."` to feed the
  no-stream watchdog.
- **Parent-branch read-only.** Don't touch `aeneas-lean-soundness/`
  or `aeneas-lean-checker/AeneasCheck/Theorems/`.
- **Local commits only.** No push.

## "Done" looks like

- All 6 bugs above fixed and committed.
- c_lean per-fixture ≥ 50 / 89.
- c_lean per-decl ≥ 1500 / 3143.
- A session-end entry in `zero-skip-plan.md` summarising deltas.

## "Almost done" looks like

- 3–4 of the 6 bugs fixed.
- c_lean per-fixture in the 40s.
- The remaining bugs have updated carry-forward notes.
- Stop and write a status report. Don't push.
