# Upstream Plan: Extract Cert Generation as Interpreter Observer

## Goal

Refactor the inline cert-event emission currently smeared across
`src/interp/` into a generic interpreter-observer pattern, so the cert
work can be upstreamed as two independent pieces: a small
observability hook on its own merits, and `src/cert/` as one optional
downstream consumer.

The mainline-visible diff today is dominated by ~1,150 LOC of inline
`CertEvent.*` payload construction at 25 emit sites plus 4
cert-specific fields on `eval_ctx`. The target shape replaces that
with ~250 LOC of generic primitives (`Event.t`, `Observer.t`,
`Observer.notify`) in interpreter-native types and moves all cert
translation into `src/cert/CertObserver.ml` as a registered consumer.
A maintainer adding a new interpreter rule writes one `Observer.notify`
in interpreter vocabulary; they never see `CertEvent`.

## Current state

LOC of affected files on `aeneas-lean-certificate`:

| File | LOC |
|---|---|
| `src/cert/CertEvent.ml` | 708 |
| `src/cert/CertEvent.mli` | 301 |
| `src/cert/CertGen.ml` | 301 |
| `src/cert/CertJson.ml` | 608 |
| `src/cert/LlbcJson.ml` | 697 |
| `src/interp/InterpStatements.ml` | 2352 |
| `src/interp/InterpBorrows.ml` | 2751 |
| `src/interp/InterpExpressions.ml` | 1550 |
| `src/interp/InterpLoops.ml` | 616 |
| `src/interp/InterpExpansion.ml` | 828 |
| `src/llbc/Contexts.ml` | 835 |

`ctx_emit_event` call sites by file (25 total — the old plan's "96"
counted every `CertEvent.*` reference, of which there are 219 in
helpers + payload construction):

| File | Sites |
|---|---|
| `src/interp/InterpStatements.ml` | 14 |
| `src/interp/InterpExpressions.ml` | 4 |
| `src/interp/InterpBorrows.ml` | 2 |
| `src/interp/InterpLoops.ml` | 2 |
| `src/interp/InterpExpansion.ml` | 1 |
| `src/llbc/Contexts.ml` | 2 (definition + comment) |

`eval_ctx` cert fields (`src/llbc/Contexts.ml:159–192`):

* `cert_event_buffer : (CertEvent.event list ref[@opaque])`
* `cert_events_suppressed : (bool ref[@opaque])`
* `cert_loop_id_stack : (loop_id list ref[@opaque])` — pushed at
  `EvLoopInv`, popped after `EvLoopEnd`; read by
  `eval_rvalue_ref` to tag `MbkLoopOwned`.
* `cert_ended_loans : (BorrowId.Set.t ref[@opaque])` — dedupe set for
  the post-join redundant `EvEndBorrow` drops.

The old plan only enumerated two of these; `cert_loop_id_stack` and
`cert_ended_loans` are M9.6/M9.5x additions and matter for the
refactor — both encode ordering- or state-sensitive cert logic that
must move into the observer's closure state.

`CertEvent` vocabulary (`src/cert/CertEvent.mli`):

* 18 event variants (`Ev…`): `EvMutBorrow`, `EvSharedBorrow`,
  `EvAssign`, `EvMove`, `EvCopy`, `EvEndBorrow`, `EvAssert`, `EvPanic`,
  `EvReturn`, `EvBinop`, `EvReborrow`, `EvCall`, `EvEndAbs`, `EvProj`,
  `EvSymExpandMutBorrow`, `EvJoin`, `EvLoopInv`, `EvLoopEnd`,
  `EvMatchArm` (19 — `EvProj` exists in `.mli` but is currently
  emitted nowhere; confirm before porting).
* Auxiliary cert vocabulary: `cert_place`, `cert_sym_expr`,
  `cert_state_summary`, `cert_restore_info`, `cert_source_span`,
  `cert_mut_borrow_kind`, `cert_abs_role`, `cert_abs_shape`,
  `cert_join_rule`, `cert_join_entry_delta`, `cert_join_entry`,
  `cert_stmt_ref`.
* `cert_fmt_version = 6` (M10.x.0).

Cert v6 additions (M10.x.0):

* `ri_holder_local : local_id option` on `cert_restore_info`. Computed
  inline at `src/interp/InterpBorrows.ml:1062–1075` by walking
  `ctx.env` for the `VMutLoan loan_bid` holder *before* `give_back_concrete`.
* `je_delta : cert_join_entry_delta` on `cert_join_entry`. Computed
  alongside `je_rule` in `src/interp/InterpStatements.ml:1616–1725`;
  the two share constructor selection (Same / Symbolic / MutBorrows /
  Var / BottomOther / OtherBottom).
* `fc_stmt_refs : cert_stmt_ref option list` on `fun_cert`. Currently
  populated as a length-matched array of `None` sentinels in
  `src/cert/CertGen.ml:128–129`; the per-event population at the 23
  emit sites is deferred to M10.x.0b.

Main.ml wiring: `src/Main.ml:96` (`-emit-cert` flag), `src/Main.ml:748`
(`CertGen.emit filename m marked_ids` dispatch).

## Target shape

Three files. Sizes are estimates; LOC of `CertObserver.ml` is the
~1,150 LOC of inline construction currently inside `src/interp/`
collected into one place plus the closure-state moved off `eval_ctx`.

### `src/interp/Event.ml{,i}` (~200 LOC)

Event vocabulary in interpreter-native types only:
`Place.t`, `BorrowId.t`, `SharedBorrowId.t`, `LoopId.t`, `AbsId.t`,
`FunDeclId.t`, `FunCallId.t`, `LocalId.t`, `SymbolicValueId.t`,
`tvalue`, `binop`, `operand`, `rvalue`. **No reference to
`CertEvent`**. One variant per rule firing; structure mirrors the 18
`Ev…` variants but the payload uses interpreter types:

| `Event.t` variant | Interpreter-native payload |
|---|---|
| `MutBorrow` | `{ loan : BorrowId.t; place : Place.t; value : tvalue }` |
| `SharedBorrow` | `{ loan : BorrowId.t; sb_id : SharedBorrowId.t; place : Place.t; value : tvalue }` |
| `Assign` | `{ dst : Place.t; rvalue : rvalue; value : tvalue }` |
| `Move` / `Copy` | `{ src : Place.t; dst : Place.t; value : tvalue }` |
| `EndBorrow` | `{ loan : BorrowId.t; given_back : tvalue; holder_local : LocalId.t option }` |
| `Assert` | `{ cond_value : tvalue; expected : bool }` |
| `Panic` / `Return` | `unit` |
| `Binop` | `{ op : binop; lhs : operand; rhs : operand; dst : Place.t }` |
| `Reborrow` | `{ child : BorrowId.t; parent : BorrowId.t; place : Place.t; parent_loan : (AbsId.t option) loan_status }` |
| `Call` | `{ fn : FunDeclId.t; fn_name : string; call_id : FunCallId.t; args : operand list; arg_values : tvalue list; dst : Place.t; region_abs : AbsId.t list; freshened_abs : abs list }` |
| `EndAbs` | `{ abs : AbsId.t; final_values : tvalue list; released_loans : BorrowId.t list; token_clear_locals : LocalId.t list }` |
| `SymExpandMutBorrow` | `{ sv : SymbolicValueId.t; bid : BorrowId.t; inner_sv : SymbolicValueId.t; parent_abs : AbsId.t option; subst_locals : LocalId.t list; subst_loans : BorrowId.t list }` |
| `Join` | `{ ctx_left : eval_ctx; ctx_right : eval_ctx; ctx_joined : eval_ctx }` |
| `LoopInv` | `{ loop_id : LoopId.t; fp_ctx : eval_ctx; loan_registry : (BorrowId.t * AbsId.t) list }` |
| `LoopEnd` | `{ loop_id : LoopId.t }` |
| `MatchArm` | `{ scrutinee_value : tvalue; adt_id : TypeDeclId.t; variant_id : VariantId.t }` |
| `Proj` (if needed) | `{ abs : AbsId.t; place : Place.t; value : tvalue }` |

The `Call`, `EndAbs`, `LoopInv`, `Join` payloads pass the relevant
slice of the eval-ctx (`freshened_abs`, `fp_ctx`, left/right/joined)
rather than precomputing `cert_abs_shape` / `cert_state_summary`.
The cert v6 derivations (`ri_holder_local`, `je_delta`,
`token_clear_locals`, `loan_registry`) are *not* on `Event.t` —
`CertObserver` re-derives them. Exception: `EndBorrow.holder_local`,
which must be computed *pre*-give-back; the observer fires before
`give_back_concrete` so this is fine, but the helper that walks
`ctx.env` for the holder is shared and lifts cleanly into
`src/cert/CertObserver.ml`.

### `src/interp/Observer.ml{,i}` (~50 LOC)

```
type observer = { on_event : eval_ctx -> Event.t -> unit }
val default : observer            (* no-op *)
val current : observer ref
val notify : eval_ctx -> Event.t -> unit
val notify_lazy : eval_ctx -> (unit -> Event.t) -> unit
val with_suppressed : eval_ctx -> (unit -> 'a) -> 'a
```

`notify_lazy` is for `Call` / `Join` / `LoopInv`, whose payloads
require non-trivial walks of `eval_ctx` (region-abs role extraction,
loan-registry collection, state-summary build). The default observer
short-circuits the thunk; the cert observer always forces it.

`with_suppressed` replaces `Contexts.ctx_with_cert_events_suppressed`;
the suppression state moves to a closure-local `ref` inside the
observer, but the wrapping function stays on the interpreter side
because the call sites (`InterpLoops.ml:361,391`) are interpreter
logic, not cert logic.

### `src/cert/CertObserver.ml` (~700 LOC)

Implements `Observer.observer`. Owns:

* `cert_event_buffer : CertEvent.event list ref`
* `cert_events_suppressed : bool ref` (consulted by
  `Observer.with_suppressed`; the observer is the suppression
  authority)
* `cert_loop_id_stack : LoopId.t list ref` (pushed inside `on_event`
  on `LoopInv`, popped on `LoopEnd`)
* `cert_ended_loans : BorrowId.Set.t ref` (consulted inside `on_event`
  on `EndBorrow` for the M9.5x post-join dedupe)

All `CertEvent.cert_*_of_*` translation helpers move from
`src/cert/CertEvent.ml` (the trailing `let cert_…` functions, ~150
LOC) and the inline payload computation at the 25 emit sites
(~1,000 LOC) into a single `event_to_cert : eval_ctx -> Event.t ->
CertEvent.event option` dispatch in `CertObserver.ml`. `option`
because the existing inline logic already elides events whose
operands can't be lifted (e.g. globals).

Cert v6 logic in `CertObserver.ml`:

* `ri_holder_local` derivation from `Event.EndBorrow.holder_local`.
  Direct pass-through.
* `je_rule` + `je_delta` derivation from `Event.Join`'s
  `ctx_left` / `ctx_right` / `ctx_joined`. Re-derived inside the
  observer; the constructor selection logic at
  `InterpStatements.ml:1616-1725` moves verbatim.
* `fc_stmt_refs` stays in `CertGen.ml` (it's parallel to events, not
  per-event; populated at trace flush time, not at emit time).

### `src/llbc/Contexts.ml`

Remove: `cert_event_buffer`, `cert_events_suppressed`,
`cert_loop_id_stack`, `cert_ended_loans`, `ctx_emit_event`,
`ctx_with_cert_events_suppressed`, `ctx_take_events`.
The `eval_ctx` record loses ~35 LOC of cert-specific fields and
docstrings. `src/interp/InterpUtils.ml:817-820` (the cert-field
initialiser) shrinks correspondingly.

## Migration sequence

12 commits, sequenced so each is independently verifiable against
gate `G_cert`. The cert wire format never changes during this
refactor.

| # | Commit | Files | Gate |
|---|---|---|---|
| 1 | Land `Event.ml{,i}` + `Observer.ml{,i}` with no-op default. | `src/interp/Event.{ml,mli}`, `src/interp/Observer.{ml,mli}`, `src/dune` | `G_build` |
| 2 | Land `CertObserver.ml` skeleton: registers as `Observer.current`, owns the four state refs, implements an empty `event_to_cert`. Wire `Main.ml:748` to register it under `-emit-cert`. Cert output drops to empty until commit 3+. | `src/cert/CertObserver.{ml,mli}`, `src/cert/dune`, `src/Main.ml` | `G_build` |
| 3 | Migrate `InterpExpressions.ml`'s 4 sites (`EvCopy`, `EvMove`, `EvReborrow`, `EvMutBorrow`). Extend `event_to_cert` with the matching cases. After this commit, certs for fixtures exercising only copy/move/borrow/reborrow restore byte-equality. | `src/interp/InterpExpressions.ml`, `src/cert/CertObserver.ml` | `G_cert` (partial: copy-only fixtures), `G_build` |
| 4 | Migrate `InterpExpansion.ml`'s 1 site (`EvSymExpandMutBorrow`). | `src/interp/InterpExpansion.ml`, `src/cert/CertObserver.ml` | `G_cert` (partial) |
| 5 | Migrate `InterpBorrows.ml`'s 2 sites (`EvEndBorrow`, `EvEndAbs`). The `cert_ended_loans` dedupe state moves into the observer's `on_event` for `EndBorrow`. The `ri_holder_local` env-walk runs inside the observer (the observer fires pre-`give_back_concrete`). | `src/interp/InterpBorrows.ml`, `src/cert/CertObserver.ml` | `G_cert` (partial) |
| 6 | Migrate `InterpLoops.ml`'s 2 sites (`EvLoopInv`, `EvLoopEnd`) + 2 `ctx_with_cert_events_suppressed` calls. The `cert_loop_id_stack` push/pop moves into the observer's `on_event` for `LoopInv`/`LoopEnd`. The loan-registry walk runs inside the observer. | `src/interp/InterpLoops.ml`, `src/cert/CertObserver.ml` | `G_cert` (partial) |
| 7 | Migrate the 11 simple sites in `InterpStatements.ml` (`EvAssert`×3, `EvPanic`, `EvReturn`, `EvMatchArm`, the 5 `EvAssign`/`EvBinop` rvalue cases). | `src/interp/InterpStatements.ml`, `src/cert/CertObserver.ml` | `G_cert` (partial) |
| 8 | Migrate `InterpStatements.ml`'s `EvCall` site (line 2213) + the `cert_abs_shape` extraction (lines 2138–2204). The role-walk visitor moves verbatim into `CertObserver`. | `src/interp/InterpStatements.ml`, `src/cert/CertObserver.ml` | `G_cert` (partial) |
| 9 | Migrate `InterpStatements.ml`'s `EvJoin` site (lines 1728-1735) + the `cert_witnesses` derivation (lines 1616-1725). Both `je_rule` and `je_delta` constructor selection moves into `CertObserver`. | `src/interp/InterpStatements.ml`, `src/cert/CertObserver.ml` | `G_cert` (full sweep) |
| 10 | Strip `cert_event_buffer` / `cert_events_suppressed` / `cert_loop_id_stack` / `cert_ended_loans` / `ctx_emit_event` / `ctx_with_cert_events_suppressed` / `ctx_take_events` from `Contexts.ml`; strip the corresponding init from `InterpUtils.ml`. Move `CertGen.ml:62` (which reads `ctx.cert_event_buffer`) to read from `CertObserver.flush`. | `src/llbc/Contexts.ml`, `src/interp/InterpUtils.ml`, `src/cert/CertGen.ml` | `G_eval_ctx`, `G_cert` |
| 11 | Move the `CertEvent.cert_*_of_*` helpers from `CertEvent.ml` to `CertObserver.ml` (close-of-life relocation; `CertEvent.ml{,i}` becomes a pure vocabulary file). | `src/cert/CertEvent.{ml,mli}`, `src/cert/CertObserver.ml` | `G_cert`, `G_build` |
| 12 | Verify `grep -rn 'CertEvent\.' src/ | grep -v '^src/cert/'` is empty. Final `G_perf` measurement against pre-refactor tag. | (no source changes) | `G_perf`, `G_build` |

**Rollback story per commit.** Commits 3–9 are revertible
file-by-file: each restores the inline emit at the corresponding
sites and leaves the (smaller) `event_to_cert` partial. The pre-commit
gate is the same as the post-commit gate — `G_cert` for that file's
fixtures.

Commits 1–2 and 10–12 are revertible as units. The risky commit is
#10 (the `Contexts.ml` strip); land it only after commit #9 cleared
the full `G_cert` sweep.

## Gates

The cert pipeline's gates are described in
[`documentation/certificate-pipeline.md`](certificate-pipeline.md#other-gates)
(§"Other gates"). The refactor's gates are a strict subset plus a
perf budget:

* **`G_cert`** — every cert in `tests/llbc/*.cert.json` is byte-equal
  pre vs. post refactor. Baseline at HEAD-before-refactor, diff after:
  ```bash
  for src in tests/src/*.rs; do
    ./bin/aeneas -emit-cert "$src" -dest /tmp/cert-baseline/
  done
  # After refactor:
  for cert in /tmp/cert-baseline/*.cert.json; do
    diff -q "$cert" "tests/llbc/$(basename $cert)" || echo "REGRESSION"
  done
  ```
* **`G_lean`** — the 89-fixture sweep stays 89/0 (pipeline doc §G4).
* **`G_perf`** — no-op observer overhead is <1% wall-clock on
  `curve25519` (or whichever fixture is largest):
  ```bash
  hyperfine 'pre-refactor: aeneas -borrow-check curve25519.rs' \
            'post-refactor: aeneas -borrow-check curve25519.rs'
  ```
* **`G_build`** — `make bin/aeneas` clean; no new warnings;
  `grep -rn 'CertEvent\.' src/ | grep -v '^src/cert/'` empty;
  `grep -rn 'ctx_emit_event' src/` empty.
* **`G_eval_ctx`** — `grep -n 'cert' src/llbc/Contexts.ml` empty
  after commit #10.

## Open design questions

* **`notify` vs `notify_lazy`.** The old plan suggested exposing both.
  Recommendation: expose both. `notify` is the common case (cheap
  payloads — `Place.t`, `BorrowId.t`, `tvalue`). `notify_lazy` is
  required for `Event.Call` (region-abs role walk over `abs.avalues`,
  ~30 LOC of iterator boilerplate), `Event.Join` (re-derivation of
  rule + delta from three state summaries), and `Event.LoopInv`
  (loan-registry walk over fixpoint-context abs values). Forcing all
  three into eager `notify` makes the no-op observer pay for cert-only
  payload work; collapsing both into `notify_lazy` makes every cheap
  emit site allocate a thunk. The two-API surface is one extra
  function, not a maintenance burden.

* **`Event.Join` payload: pass full eval_ctxs or pre-flatten.** The
  inline derivation at `InterpStatements.ml:1616-1725` reads
  `left_summary.cs_env`, `right_summary.cs_env`,
  `result_summary.cs_env` — those are `cert_state_summary` values
  already pre-built before the witness loop. Recommendation: the
  observer receives `(left, right, result : eval_ctx)` and builds
  the summaries inside `event_to_cert`. This keeps `Event.t` free of
  cert vocabulary. Confirm by reading lines 1500–1615 (the summary
  construction site) — if those summaries are *only* used for cert
  emission, lifting them into the observer is clean; if they're used
  for non-cert interpreter logic, the `Event.Join` payload should
  pass them through. Read-only audit could not resolve.

* **`EndBorrow` ordering.** `cert_ended_loans` was on `eval_ctx` so
  the dedupe set survived ctx copies under joins. After the move to
  the observer's closure state, the set is module-global and
  monotonic — the borrow-id allocator is per-fun-decl-monotonic, so
  global is fine *within* a function, but the observer must reset
  the set at function boundary. The current `CertGen.ml` runs
  `collect_for_fun` per `fdef` with a fresh `eval_ctx`; the
  `CertObserver.make` constructor should clear the state on each
  function entry. Confirm by reading `CertGen.ml:54-147` — the
  per-function setup at line 60 (`initialize_symbolic_context_for_fun`)
  is the natural reset point.

* **`EvProj` enumeration.** The `.mli` declares `EvProj` but
  `grep` finds no emit site in `src/interp/`. Either it's emitted
  through a path the audit missed, or it's a dead variant left over
  from an earlier milestone. Resolve by checking
  `src/cert/CertGen.ml` and the Lean replayer — if no producer
  exists, the refactor can drop the variant from `Event.t` (and
  `CertEvent.ml`).

* **New emit sites since the old plan.** M10.x.0's three v6
  additions did not add emit sites — they added payload fields to
  existing `EvEndBorrow` (`ri_holder_local`), existing `EvJoin`
  (`je_delta` per-entry), and the per-function `fc_stmt_refs` (not
  per-event). Audit confirms 25 emit sites today, all enumerated
  above.

## Risks

* **Hot-path overhead.** Observer dispatch is one indirection per
  rule firing. Default `on_event = fun _ _ -> ()` inlines well in
  OCaml. `G_perf` settles this empirically; if the no-op observer
  costs more than 1%, gate `Observer.notify` on a module-level
  `enabled` flag set at `-emit-cert` parse time so the dispatch
  becomes a literal no-op in the un-instrumented binary.

* **Vocabulary churn coupling.** Every new interpreter rule still
  requires one `Event.t` variant + one `event_to_cert` case. This is
  unavoidable — the cert is a shadow of rule-firing — but the
  observer pattern moves the per-new-rule cost from "edit the cert
  vocabulary" (cross-team) to "add a case in your own observer"
  (downstream).

* **Payload computation cost.** `Event.Call`, `Event.Join`,
  `Event.LoopInv` carry whole-context references; the observer pays
  the walk cost. `notify_lazy` lets the no-op observer short-circuit,
  but the cert observer pays it once per fixture. Profile on
  `curve25519` to confirm <5% emit-time overhead vs. the current
  inline-payload path.

* **Upstream-PR shape.** Audit every `Event.t` variant for "would I
  add this if cert didn't exist?". `Event.MutBorrow`, `Event.Call`,
  `Event.EndBorrow`, `Event.Return`, `Event.Panic` clearly pass.
  `Event.Join`, `Event.LoopInv`, `Event.SymExpandMutBorrow` are
  borderline — they fire at points the interpreter would not
  otherwise advertise. Pitch them as "useful for tracing /
  debugging" — the symbolic interpreter's join and fixpoint logic
  is exactly what mainline contributors most want trace points on.

* **Cert-v6 field leakage check.** Confirmed: `ri_holder_local`
  (env walk), `je_delta` (re-derivable from ctxs),
  `token_clear_locals` (abs-walk), `loan_registry` (abs-walk),
  `kind_hint = MbkLoopOwned` (reads `cert_loop_id_stack` — moves to
  observer closure), `parent_live`/`parent_abs` (single
  `ctx_lookup_loan_opt` call) — all derivable inside
  `CertObserver` from interpreter-native inputs. No cert-format
  leakage into `Event.t`.

## What this plan does NOT cover

* **The Lean checker side** (`aeneas-lean-checker/`) — unchanged. The
  cert wire format is identical pre/post; the replayer is unaware.
* **The cert wire format** (`src/cert/CertJson.ml`, schema) —
  unchanged. `cert_fmt_version` stays at 6.
* **The soundness proof** (`aeneas-lean-soundness/`) — unchanged.
* **Differential testing** — orthogonal stream
  (`documentation/differential-testing-plan.md`).
* **`fc_stmt_refs` per-event population (M10.x.0b deferred work).**
  When that lands, it adds threading at the 23 emit sites — but
  through the observer's `event_to_cert`, not back into the
  interpreter. The refactor in this plan is the *precondition* that
  makes M10.x.0b a single-file change in `CertObserver.ml`.
* **`-backend coq` / `-backend fstar` cert support.** Separate
  multi-backend plan; the observer pattern is the shared substrate
  any future backend-specific observer would register against.
