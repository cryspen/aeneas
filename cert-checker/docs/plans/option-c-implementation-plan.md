# Option C Implementation Plan — Add Rule-Choice Hints to Cert Format

## Executive summary

This plan stages Option C (hint-augmented JSON cert) into seven incremental phases. Each phase ships green against the four gates, the cert parser stays back-compat with pre-hint certs, and the OCaml emitter only forwards data the interpreter already computes. The end state: every M9.5x/y/z/aa/w/s/r pragmatic shortcut in the Lean checker either becomes a *strict* check against a hint field, or is dropped because the hint makes the underlying choice deterministic. The proof skeleton in `cert-format-and-soundness.md` §4.5 ("pragmatic ≤ check" caveats) collapses to "the cert names the rule, so case-analysis is immediate."

Total effort estimate: **~16–22 working days** of single-developer focus, split as Audit/Schema 2 d, OCaml emitter 4–6 d, Lean parser 1 d, Lean checker tightening 5–7 d, Migration 2 d, Soundness prep 1 d, Sequencing buffer 1–2 d.

---

## Phase 0: Audit of pragmatic shortcuts

Every `M9.5*` comment in `aeneas-lean-checker/AeneasCheck/{Typecheck,LLBCSharp}/`, classified.

### 0.1 The full inventory

| Tag | Location(s) | What it does today | Phase 1 hint (or other disposition) |
|---|---|---|---|
| **M9.5r** | `LLBCSharp/State.lean:24-28`, `Step.lean:268-300`, `Typecheck/Stmts.lean:199-208`, `Replay.lean:43-44` | Substitutes `.sym svId → .mutLoan bid` across env *and* every existing loan's `given` value, scanning to find which locals/loans to rewrite. Adds the new loan as `.lazyExpand` so it may leak past exit. | **`EvSymExpandMutBorrow.parentAbs : Option Nat`** + **`EvSymExpandMutBorrow.substLocals : Array Nat`** + **`EvSymExpandMutBorrow.substLoans : Array Nat`**. Eliminated by hints. |
| **M9.5s** | `Step.lean:302-329`, `Typecheck/Stmts.lean:109-124`, `CertEvent.lean:99-100` (`releasedLoans`) | `released_loans` already exists. Step scans env to clear any local whose value is `.mutLoan bid` for a released loan. | Strengthen: **`EvEndAbs.tokenClearLocals : Array Nat`** — explicit list of locals whose mutLoan tokens must be cleared. (Already half-hinted; complete the cycle.) |
| **M9.5w** | `Step.lean:82-93`, `Typecheck/Stmts.lean:62-77` | `&mut (*x).f` (`projection.any (· == .deref)`) is classified as `.reborrow`-class instead of `.direct` so it may leak. *Only* the immediate-outer-Deref shape is `EvReborrow` from OCaml; the rest are inferred. | **`EvMutBorrow.kindHint : MutBorrowKind`** (`Direct | InAbsReborrow absId | LoopOwned loopId`). Eliminated by hint. |
| **M9.5x** | `State.lean:52-59` (`joinDedupe`), `Step.lean:170-179`, `Typecheck/Env.lean:53-61`, `Stmts.lean:32-55`, `Stmts.lean:135-141`, `Stmts.lean:181-190` | OCaml emits a `EvEndBorrow` inside each arm and then a redundant post-join `EvEndBorrow` on the same loan. Lean silently no-ops the duplicate. | **Drop the redundant emit on the OCaml side** rather than add a hint. The Lean checker becomes strict (every `EvEndBorrow` must end a live loan). This is a *structural invariant the cert format itself should enforce* — there should be exactly one end per loan id. |
| **M9.5y** | `Step.lean:423-431` (`isFreshSym` accepts `symMutBorrowTok n`) | Join admits a `SymMutBorrowTok n` in the result as a fresh form (the `Collapse-Dup-MutBorrow` rule of Fig. 11 introducing a fresh borrow id). | **`EvJoin.witnesses : Array JoinRule`** with explicit `JoinMutBorrows ℓ_0 ℓ_1 absId` carrying the fresh region-abstraction id. Eliminated by hint. |
| **M9.5z** | `Replay.lean:54-72`, `Typecheck/Stmts.lean:152-172` | `EvLoopInv` registers loop-introduced borrow ids found via scanning `invariant.liveLoans` + walking `invariant.env` for `SymMutBorrowTok n` tokens. | **`EvLoopInv.loanRegistry : Array (Nat × Nat)`** — `(borrowId, parentAbsId)` pairs declaring exactly which loans the fixpoint introduces. Eliminated by hint. |
| **M9.5aa** | `State.lean:60-66` (`loopDepth`), `Step.lean:97-103`, `Typecheck/Env.lean:62-68`, `Stmts.lean:71-77`, `Stmts.lean:143-147`, `Stmts.lean:186-190`, `Replay.lean:61-76` | `&mut local` issued while `loopDepth > 0` is classified as `.lazyExpand` so it may leak (loop's region abstraction owns the lifetime). | Folded into **`EvMutBorrow.kindHint = LoopOwned loopId`** (same field as M9.5w). The `loopDepth` counter goes away. |
| **M9.5d** (variant tag) | `Step.lean:43-51`, `Stmts.lean:191-198` | `.symVariant` evaluates to `.sym variantId` — abstract state doesn't model ADT structurally. | **Out of Option C scope.** This is a Tier-3 concern (formalising LLBC value grammar in Lean); the cert already carries the right info, the replayer simply chooses a coarse abstraction. |
| **M9.5f** | `Step.lean:49` | Payload fields of `.symVariant` don't update abstract state. | **Out of Option C scope** — same rationale as M9.5d. |
| **M9.5p** | `Step.lean:53-64`, `Step.lean:391-395`, `Typecheck/Places.lean:41-46` | `.symTuple` / `.symRecord` evaluate to `.sym 0` placeholder. | **Out of Option C scope** — coarse abstraction; Tier-3 (or a separate "value grammar refinement" milestone). |
| **Reborrow implicit parent** | `Step.lean:140-149` ("treat as an implicit input borrow… pre-adding it here") | `stepReborrow` invents a `.reborrow` parent loan on-the-fly if the parent isn't in state. | **`EvReborrow.parentLiveness : Bool`** + **`EvReborrow.parentAbs : Option Nat`** (the spec). Eliminated by hint. |
| `lazyExpand` end without token | `Step.lean:200-206` ("Lazy expansions may have substituted the token through intermediate locals that the cert subsequently overwrote") | `stepEndBorrow` for `.lazyExpand` silently succeeds if no env entry holds the token. | Eliminated when **M9.5r's `substLocals` hint** is added — the Lean side then *knows* which locals were substituted and can validate every step. |
| Join "live loans verbatim" | `Step.lean:474-487` ("rebuild loans with liveLoans, … kind defaults to `.reborrow`") | `stepJoin` invents loan info for ids in `result.liveLoans` not already tracked. | Eliminated by **`EvJoin.witnesses`** — the per-entry rule directly names borrow ids and abs ids. |
| `EvProj` rejected | `Stmts.lean:125`, `Replay.lean:42` | Hard-errors. | **Out of Option C scope** (M10+ work: requires sub-borrow modelling). |

### 0.2 Classification summary

| Bucket | Items |
|---|---|
| **Eliminated by a hint field (Option C)** | M9.5r (substitution scope), M9.5s (token-clear), M9.5w (kind), M9.5y (join collapse), M9.5z (loop loan registry), M9.5aa (loop kind, folded into w), reborrow implicit-parent invention, lazyExpand silent end, join loan invention |
| **Structural invariant the cert format itself should enforce** | M9.5x (redundant `EvEndBorrow` after join) — solution: fix the OCaml emitter to not emit the duplicate, and tighten Lean to reject it |
| **Out of Option C scope (Tier 3 / value-grammar formalisation)** | M9.5d, M9.5f, M9.5p (coarse ADT/tuple/record abstraction); `EvProj` |

The hints in the user's prompt (`EvJoin.witnesses`, `EvCall.absSig`, `EvSymExpandMutBorrow.parentAbs`, `EvReborrow.parentLiveness`) cover most of this; the audit additionally surfaces:

* **`EvMutBorrow.kindHint`** (subsumes M9.5w + M9.5aa, eliminates `SymState.loopDepth`)
* **`EvSymExpandMutBorrow.substLocals` / `substLoans`** (eliminates the scan in `stepSymExpandMutBorrow`)
* **`EvEndAbs.tokenClearLocals`** (strengthens existing `released_loans`)
* **`EvLoopInv.loanRegistry`** (eliminates the env-scan for `SymMutBorrowTok` in `Replay.stepEvent`)

The M9.5x dedupe is *not* a hint — it's a bug-fix on the OCaml emitter; Lean simply stops tolerating it (a Phase-7 commit, gated by Phase 2 dropping the redundant emit).

---

## Phase 1: Schema design

The contract. Bumps `fmt_version: 1 → 2`. All new fields are *optional* in JSON; the parser substitutes a back-compat default that preserves today's pragmatic behaviour.

### 1.1 `EvJoin.witnesses : Array JoinEntry`

**Lean type** (in `aeneas-lean-checker/AeneasCheck/Raw/CertEvent.lean`):

```lean
inductive JoinRule
  | joinSame                                              -- both branches agreed
  | joinSymbolic (freshSv : Nat)                          -- result is fresh σ
  | joinMutBorrows (l_left l_right l_fresh : Nat)         -- collapse to fresh borrow
                   (abs : Nat)                            -- in fresh region abstraction
  | joinVar                                               -- variable-only differ
  | joinBottomOther (abs : Nat)                           -- left=⊥, right wrapped in abs
  | joinOtherBottom (abs : Nat)                           -- mirror
  deriving Repr, Inhabited

structure JoinEntry where
  localId : Nat
  rule : JoinRule
  deriving Repr, Inhabited

-- inside Event:
| join (left right result : StateSummary)
       (witnesses : Array JoinEntry := #[])              -- new, defaults to empty
```

**JSON shape** (one entry per result-env local, in declaration order):

```json
"EvJoin": {
  "left":  {...},
  "right": {...},
  "result": {...},
  "witnesses": [
    {"local": 3, "rule": {"JoinSame": {}}},
    {"local": 5, "rule": {"JoinSymbolic": {"fresh_sv": 12}}},
    {"local": 7, "rule": {"JoinMutBorrows":
                          {"left": 0, "right": 2, "fresh": 3, "abs": 4}}}
  ]
}
```

**OCaml type** (`src/cert/CertEvent.ml`):

```ocaml
type cert_join_rule =
  | JoinSame
  | JoinSymbolic of symbolic_value_id
  | JoinMutBorrows of { l_left: borrow_id; l_right: borrow_id;
                        l_fresh: borrow_id; abs: abs_id }
  | JoinVar
  | JoinBottomOther of abs_id
  | JoinOtherBottom of abs_id

type cert_join_entry = { je_local: local_id; je_rule: cert_join_rule }
```

**Backward-compat default**: `witnesses = #[]`. When empty, `stepJoin` falls back to the pragmatic `joinEntryOk` it does today.

### 1.2 `EvCall.absSig : Array AbsShape`

```lean
inductive AbsRoleEntry
  | mutBorrow (argIdx : Nat) (loanId : Nat)              -- abs holds an input mut borrow
  | mutLoan (loanId : Nat)                               -- abs owns the loan side
  | sharedBorrow (argIdx : Nat) (sharedBorrowId : Nat)   -- shared borrow
  deriving Repr, Inhabited

structure AbsShape where
  absId : Nat
  parentAbs : Array Nat        -- ancestor abs ids (for nested-borrow contracts)
  roles : Array AbsRoleEntry   -- exactly the `A_in(ρ)` content per paper Fig. 9
  deriving Repr, Inhabited

-- inside Event.call:
| call (fn callId : Nat) (fnName : String) (args : Array SymExpr)
       (dst : Place) (regionAbs : Array Nat)
       (absSig : Array AbsShape := #[])                  -- new
```

**JSON**:

```json
"abs_sig": [
  {"abs_id": 4, "parent_abs": [],
   "roles": [{"MutBorrow": {"arg_idx": 0, "loan": 1}},
             {"MutBorrow": {"arg_idx": 1, "loan": 2}},
             {"MutLoan": {"loan": 3}}]}
]
```

**Source on the OCaml side**: `compute_abs_avalues` (`InterpStatements.ml:1931-1966`) already constructs each abstraction's `avalues`. We classify each `tavalue` as it's built. **No new analysis** — purely shadowing existing work.

**Default**: `absSig = #[]` → fall back to today's behaviour (region abs ids tracked as opaque tokens, `EvEndAbs.released_loans` drives the release).

### 1.3 `EvSymExpandMutBorrow.parentAbs / substLocals / substLoans`

```lean
| symExpandMutBorrow (svId bid innerSv : Nat)
                     (parentAbs : Option Nat := none)
                     (substLocals : Array Nat := #[])
                     (substLoans : Array Nat := #[])
```

**JSON**:

```json
"EvSymExpandMutBorrow": {
  "sv_id": 5, "bid": 7, "inner_sv": 6,
  "parent_abs": 4,
  "subst_locals": [3, 9],
  "subst_loans": [2]
}
```

**OCaml source**: `replace_symbolic_values` in `InterpExpansion.ml:514` already touches every binding; the visitor returns the touched-binding list with a one-line change. `parent_abs` is read off the abstraction that owns the symbolic id (look up via `expand_symbolic_value_borrow`'s caller context).

**Default**: `parentAbs = none`, `substLocals/Loans = #[]` → today's scan-everything behaviour.

### 1.4 `EvReborrow.parentLiveness : Bool`, `EvReborrow.parentAbs : Option Nat`

```lean
| reborrow (child parent : Nat) (place : Place)
           (parentLive : Bool := false)                  -- explicit witness
           (parentAbs : Option Nat := none)              -- which abs owns parent
```

**Default**: `parentLive = false`, `parentAbs = none` → today's "invent the parent as a fake `.reborrow` if missing".

### 1.5 `EvMutBorrow.kindHint : MutBorrowKind`

```lean
inductive MutBorrowKind
  | direct                                               -- in-body; must be ended
  | inAbsReborrow (absId : Nat)                          -- caller-abs-owned
  | loopOwned (loopId : Nat)                             -- loop-abs-owned
  deriving Repr, Inhabited

| mutBorrow (loan : Nat) (place : Place) (symval : Nat)
            (kindHint : MutBorrowKind := .direct)
```

**JSON**: `"kind_hint": {"Direct": {}}` / `{"InAbsReborrow": {"abs": 4}}` / `{"LoopOwned": {"loop": 0}}`.

**Default**: `.direct` — matches today's default. The M9.5w/aa logic stays as a *fallback* until Phase 4 promotes the hint to authoritative.

### 1.6 `EvLoopInv.loanRegistry : Array (Nat × Nat)`

```lean
| loopInv (loopId : Nat) (invariant : StateSummary)
          (loanRegistry : Array (Nat × Nat) := #[])     -- (borrowId, parentAbsId)
```

**Default**: `#[]` → scan-env fallback.

### 1.7 `EvEndAbs.tokenClearLocals : Array Nat`

```lean
| endAbs (abs : Nat) (finalValues : Array SymExpr)
         (releasedLoans : Array Nat := #[])
         (tokenClearLocals : Array Nat := #[])          -- new
```

**Default**: empty → today's scan-env behaviour (scan for `.mutLoan b` tokens).

### 1.8 Version bumping

* `CertEvent.cert_fmt_version : int = 2` (was 1).
* Lean parser accepts `fmt_version ∈ {1, 2}`; when 1, every hint field is treated as absent. When 2, fields are still optional (omitted = none), but the JSON shape is allowed.
* `cc_crate_hash` semantics unchanged.

### 1.9 Per-field summary table

| Hint | Lean type | JSON key | Default | OCaml source | Eliminates |
|---|---|---|---|---|---|
| `EvJoin.witnesses` | `Array JoinEntry` | `witnesses` | `#[]` | `InterpJoin.join_ctxs_list` already computes the merged abs structure | M9.5y, `valOfSymExpr` fallback in join |
| `EvCall.absSig` | `Array AbsShape` | `abs_sig` | `#[]` | `compute_abs_avalues` (`InterpStatements.ml:1931`) | "abstraction ids are opaque tokens" weakness (§3.2.1 of cert-format doc) |
| `EvSymExpandMutBorrow.parentAbs` | `Option Nat` | `parent_abs` | `none` | `expand_symbolic_value_borrow` caller's abs ctx | M9.5r scan logic |
| `EvSymExpandMutBorrow.substLocals/Loans` | `Array Nat` | `subst_locals`/`subst_loans` | `#[]` | `replace_symbolic_values` return | M9.5r scan + lazyExpand silent-end |
| `EvReborrow.parentLive` | `Bool` | `parent_live` | `false` | OCaml has the parent borrow in scope when emitting | implicit parent invention in `stepReborrow` |
| `EvReborrow.parentAbs` | `Option Nat` | `parent_abs` | `none` | same as above | precise A_in modelling |
| `EvMutBorrow.kindHint` | `MutBorrowKind` | `kind_hint` | `Direct` | OCaml knows whether place projects through Deref / loop ctx | M9.5w, M9.5aa, `loopDepth` counter |
| `EvLoopInv.loanRegistry` | `Array (Nat × Nat)` | `loan_registry` | `#[]` | `compute_loop_entry_fixed_point` output | M9.5z |
| `EvEndAbs.tokenClearLocals` | `Array Nat` | `token_clear_locals` | `#[]` | `give_back_value` knows the target slot | env scan in `stepEndAbs` |

### 1.10 Risks (Phase 1)

* **Schema lock-in**: once `fmt_version=2` ships, downgrading requires re-bumping. Mitigation: ship Phase 1 only after Phase 2 emits at least one hint correctly (so we know the shape works).
* **JSON bloat**: per-event hints multiply cert size. `EvJoin.witnesses` is one entry per env local — typical body has 5-30 locals, ~10 joins per fn ⇒ ~200 extra entries per fn. Estimated cert size +20-30%. Mitigation: encode `JoinSame` as the bare string `"JoinSame"` rather than `{"JoinSame": {}}` (one-byte form).

---

## Phase 2: OCaml emitter changes

Goal: emit every hint defined in Phase 1, *without* adding new analyses. Each hint must shadow data the interpreter already computes.

### 2.1 Site-by-site

| Hint | File:line | Change |
|---|---|---|
| `EvMutBorrow.kindHint` | `src/interp/InterpExpressions.ml:1283` | At emit time we know `p.projection` (Deref-or-not) and the surrounding ctx has the open-loop registry. Read `ctx.loop_id_stack` (already maintained by `InterpLoops.ml`) and emit `LoopOwned` / `InAbsReborrow` / `Direct`. ~15 LOC. |
| `EvReborrow.parentLive` / `parentAbs` | `src/interp/InterpExpressions.ml:1280` | `parent_v` is in scope (already read at L1269). `parentLive := true` iff the borrow id is in `ctx`'s live-borrow set; `parentAbs := Some abs_id` iff a single abstraction owns the parent borrow. Look up via existing `ctx_lookup_abs_of_borrow_id` (or equivalent). ~10 LOC. |
| `EvCall.absSig` | `src/interp/InterpStatements.ml:1931-1972` (`compute_abs_avalues`) | After `args_projs` is constructed, walk each `tavalue` and classify as `MutBorrow` / `MutLoan` / `SharedBorrow`. Parent ids come from `abs.regions.ancestors`. Emit alongside the `EvCall` constructor at L1894-1901. ~40 LOC. |
| `EvSymExpandMutBorrow.parentAbs` | `src/interp/InterpExpansion.ml:519-529` | The abstraction that holds `original_sv`'s aproj is found via existing iteration. `parent_abs := Some that_abs_id`. ~5 LOC. |
| `EvSymExpandMutBorrow.substLocals/Loans` | `src/interp/InterpExpansion.ml:514` (`replace_symbolic_values`) | Wrap the visitor to log every binding it touches. Currently the call is a one-liner; add a small ref-cell pair that the visitor populates, then read it at the emit site. ~20 LOC. |
| `EvJoin.witnesses` | `src/interp/InterpStatements.ml:1547-1566` and `src/interp/InterpJoin.ml` | This is the most invasive. The join algebra in `InterpJoin.ml` decides each local's rule but currently doesn't surface it. Refactor `join_ctxs_list` to return `(joined_ctx, per_local_witnesses)`. The per-local decision is already made internally — it just needs to be recorded. ~100 LOC. **(Risk: this is the only hint that requires non-trivial plumbing.)** |
| `EvLoopInv.loanRegistry` | `src/interp/InterpStatements.ml` (loop emission, ~L1240) | The fixpoint context's `borrow_id → abs_id` map is computed by `compute_loop_entry_fixed_point`. Capture it next to the existing `invariant` emission. ~30 LOC. |
| `EvEndAbs.tokenClearLocals` | `src/interp/InterpBorrows.ml:1283-1338` | `give_back_value` knows the destination local slot for each loan. Capture into a `local_id list` alongside `released_loans`. ~15 LOC. |

**Total OCaml LOC: ~235**, plus ~80 LOC of CertEvent/CertJson serialisation. Affects 5 files in `src/interp/`, `src/cert/CertEvent.ml`, `src/cert/CertEvent.mli`, `src/cert/CertJson.ml`.

### 2.2 New OCaml types

Add to `src/cert/CertEvent.mli` and `.ml`:

```ocaml
type cert_mut_borrow_kind =
  | MbkDirect
  | MbkInAbsReborrow of abs_id
  | MbkLoopOwned of loop_id

type cert_abs_role =
  | ArMutBorrow of { arg_idx: int; loan: borrow_id }
  | ArMutLoan of { loan: borrow_id }
  | ArSharedBorrow of { arg_idx: int; sb_id: shared_borrow_id }

type cert_abs_shape = {
  as_abs_id: abs_id;
  as_parent_abs: abs_id list;
  as_roles: cert_abs_role list;
}

type cert_join_rule = ...   (* as in §1.1 *)
type cert_join_entry = { je_local: local_id; je_rule: cert_join_rule }
```

Add corresponding fields to the existing event constructors.

### 2.3 Risks (Phase 2)

* **`EvJoin.witnesses` plumbing**: `InterpJoin.ml` is dense; the per-local decision currently flows through `match_ctx_with_target`. Plumbing it out *cleanly* (without refactoring the join algebra) requires careful threading. **Mitigation**: ship `JoinSame` and `JoinSymbolic` first (the two trivial cases); the harder `JoinMutBorrows` collapse rule lands in a second commit. The Lean side stays back-compat (no witnesses → pragmatic check) until all join rules are emitted.
* **`abs.regions.ancestors`**: confirm this is already populated at emit time. If not (i.e. ancestors are computed lazily later), the `AbsShape.parentAbs` field requires fixing up the emit order. Likely safe — `create_push_abstractions_from_abs_region_groups` (called at L1969-1972) sets ancestors eagerly.
* **Backward-compat sanity**: a Phase-2 commit that adds emission but not parsing of a field must still produce a valid old-shape cert by default (gate via `cert_fmt_version`).

---

## Phase 3: Lean parser changes

Update `AeneasCheck/Raw/CertEvent.lean` and `AeneasCheck/Json/Parser.lean` to recognise the new fields. Strictly back-compat: missing field → default.

### 3.1 `Raw/CertEvent.lean` additions

* Add `MutBorrowKind`, `JoinRule`, `JoinEntry`, `AbsRoleEntry`, `AbsShape` inductives/structures.
* Extend the existing `Event` constructors with the new optional fields (with `:= ...` defaults). The Lean parser tolerates `Inhabited` defaults via existing pattern in `EvEndAbs.releasedLoans`.

LOC: ~60 in `Raw/CertEvent.lean`.

### 3.2 `Json/Parser.lean` additions

For each new hint field, follow the established back-compat pattern at `Json/Parser.lean:228-232`:

```lean
let kindHint : MutBorrowKind ← match (payload.getObjVal? "kind_hint").toOption with
  | some kj => parseMutBorrowKind kj
  | none => pure .direct
```

LOC: ~90 in `Json/Parser.lean` (one block per hint, plus parsers for `JoinRule` and `AbsShape`).

### 3.3 Version handling

```lean
let fmtVersion ← asNat (← field j "fmt_version")
if fmtVersion ≠ 1 ∧ fmtVersion ≠ 2 then
  fail s!"unsupported cert fmt_version {fmtVersion}"
```

LOC: ~5.

### 3.4 Risks (Phase 3)

* Minimal. Pattern is well-established (see existing `releasedLoans`, `typeParams`, `traitClauses` back-compat handling). Main risk is *forgetting* a field — caught immediately by tests.

---

## Phase 4: Lean checker tightening

Replace each pragmatic shortcut with a strict check using the hint field — but only when the hint is *present*. When absent (old cert / unset on OCaml side), fall back to today's pragmatic behaviour. Each shortcut gets a dedicated commit so regressions can be bisected.

### 4.1 Per-shortcut commit plan

#### 4.1.1 Commit M9.5w/aa → `kindHint`

* `LLBCSharp/Step.lean:73-103`: replace `if place.projection.any (·==.deref) then ... else if loopDepth>0 then ... else .direct` with:
  ```lean
  let kind := match kindHint with
    | .direct => .direct
    | .inAbsReborrow _ => .reborrow
    | .loopOwned _ => .lazyExpand
  ```
  When `kindHint = .direct` and the projection actually has a `Deref`, this becomes a *strict cert violation* — but only after Phase 2 emits `.inAbsReborrow` for those cases. Phase 4a commit lands the back-compat branch; Phase 4b commit (separate) removes the fallback.
* `Typecheck/Stmts.lean:62-77`: same restructuring; `reborrowLoans` set membership becomes hint-driven.
* `State.lean:60-66`: deprecate `loopDepth` field (keep for back-compat until M9.5x is fully retired).
* LOC: ~40 net (mostly deletions). Risk: low — the hint is a *strict superset* of the inferred classification.

#### 4.1.2 Commit M9.5y → `EvJoin.witnesses`

* `Step.lean:343-488` (`stepJoin`): when `witnesses` is non-empty, drive per-entry by `JoinRule` case:
  ```lean
  for entry in witnesses do
    match entry.rule with
    | .joinSame =>
        validate l[entry.localId] == r[entry.localId] == result[entry.localId]
    | .joinSymbolic freshSv => ...  -- check result is .symVal freshSv & fresh wrt left/right
    | .joinMutBorrows l_left l_right l_fresh abs => ...
        -- check l[localId] = .symMutBorrowTok l_left, r[localId] = .symMutBorrowTok l_right
        -- check result[localId] = .symMutBorrowTok l_fresh
        -- register fresh abs in (future) AbsRegistry
    | .joinBottomOther abs | .joinOtherBottom abs => ...
  ```
* When `witnesses` is empty, fall back to today's `joinEntryOk` + `isFreshSym`.
* `isFreshSym` keeps the `symMutBorrowTok` clause until M9.5y deprecation lands.
* LOC: +80 (new strict path), ~20 deletions when fallback retired.

#### 4.1.3 Commit M9.5z → `EvLoopInv.loanRegistry`

* `Replay.lean:54-72`: when `loanRegistry` is non-empty, drive the loan-registration directly:
  ```lean
  for (b, parentAbs) in loanRegistry do
    if !st.loans.contains b then
      st := st.addLoan b .bottom .reborrow
      -- (future) record (b, parentAbs) in an abs-registry
  ```
* When empty, fall back to today's scan-env.
* `Typecheck/Stmts.lean:152-172`: mirror the change.
* LOC: ~25 net.

#### 4.1.4 Commit reborrow → `parentLive` / `parentAbs`

* `Step.lean:131-156`: when `parentLive = true`, *require* `st.loans.contains parent` (no more invention). When `parentLive = false`, keep today's pre-add behaviour.
* LOC: ~10 net.

#### 4.1.5 Commit M9.5r → `parentAbs` / `substLocals` / `substLoans`

* `Step.lean:281-300`: when `substLocals` is non-empty, replace the env scan with a direct iteration over the hint:
  ```lean
  for l in substLocals do
    match st.env[l]? with
    | some (.sym k) when k == svId => st := st.setLocal l (.mutLoan bid)
    | _ => fail s!"E-SymExpandMutBorrow: subst hint claims local {l} held .sym {svId}, found otherwise"
  -- analogous for substLoans
  ```
* The `lazyExpand` "silent end if no token" fallback at `Step.lean:200-206` becomes a hard error when the original expand carried `substLocals` and a subsequent overwrite is unaccounted for.
* LOC: ~20 net.

#### 4.1.6 Commit M9.5x → no more `joinDedupe`

This is the structural-invariant fix:

* OCaml change first (Phase 2 bonus commit): in `InterpJoin.ml` / `InterpStatements.ml`, drop the redundant `EvEndBorrow` emission. The interpreter already knows which loans are ended per-branch vs post-join; emit only the canonical one (post-join for joined cases, per-branch for non-joined). ~20 LOC OCaml.
* Lean side: delete `joinDedupe` field from `State.lean` and `Env.lean`, delete `recentlyEnded`, delete the M9.5x branches in `removeLoan` and `stepEndBorrow`. ~40 LOC net deletion.
* This commit will *regress* old cert fixtures (they carry the redundant ends); must be paired with Phase 5 cert regeneration.

#### 4.1.7 Commit `EvEndAbs.tokenClearLocals`

* `Step.lean:318-329`: when `tokenClearLocals` is non-empty, drive directly. When empty, today's scan-env fallback.
* `Typecheck/Stmts.lean:109-124`: mirror.
* LOC: ~15 net.

#### 4.1.8 Commit `EvCall.absSig`

This one doesn't tighten today's checks — it *enables* future ones. Add an `AbsRegistry : HashMap Nat AbsShape` field to `SymState`; `stepCall` populates it from `absSig`. `stepEndAbs` validates that the released loans match the abs's recorded `MutBorrow` / `MutLoan` roles. ~50 LOC.

### 4.2 LOC summary for Phase 4

* Net additions: ~250 LOC (strict paths).
* Net deletions: ~100 LOC (when fallbacks retired in a follow-up "remove pragmatic shortcuts" commit, post-Phase 5).
* Final delta: ~+150 LOC, with the *kind* of code shifting from "guess what the OCaml side did" to "validate the explicit hint".

### 4.3 Risks (Phase 4)

* **Hint-vs-fallback divergence**: while both paths coexist, a buggy hint emit silently passes (fallback masks). Mitigation: a per-event "hint coverage" counter logged in `replayCrate` output, so we can see when hints are/aren't reaching the strict path. CI fails if hint-coverage drops below a threshold after a phase claims to have shipped hints.
* **`EvJoin` strict mode**: the strict join witness check is genuinely complex (Fig. 11 has 6 rules); ship it as a *gated* check (env var or CLI flag) for the first commit so we can A/B against the pragmatic check on every fixture. Once green for a week, gate is removed.

---

## Phase 5: Migration & test strategy

### 5.1 Fixture inventory

Two fixture trees use cert.json files:

* `tests/llbc/*.cert.json` — 27 files (`find -name '*.cert.json'`), the "comprehensive" suite, regenerated from the standard test crate set by `scripts/check-charon-install.sh` / by hand via `aeneas -emit-cert`. Workflow rule (per CLAUDE.md cert-regen rule): regenerated certs are committed **only when the cert schema actually changes** — which it does here.
* `aeneas-lean-checker/tests/Direct/*.cert.json` — ~20 files, hand-pinned fixtures referenced by `tests/Direct/*.lean` smoke tests.
* `aeneas-lean-checker/tests/Generated/` — autogenerated; rebuilt by `lake build GeneratedTests`.
* `aeneas-lean-checker/tests/Golden/` — golden-file comparisons.

Total cert-fixture footprint: ~50 files needing regen attention. The `89 existing cert fixtures` from the prompt likely refers to the union (including Generated and Golden).

### 5.2 Strategy: regen-once, parse-old-tolerantly

Two-track:

1. **Track A: tolerate missing hints** (Phase 3 deliverable). Old certs parse and run identically. This keeps CI green throughout Phases 1-4.
2. **Track B: regen** after Phase 2 ships the emitter changes. This happens **between Phase 4 and Phase 7**. Order:
   * Phase 2 lands → OCaml side emits hints.
   * Phase 3 lands → Lean side parses hints (default-empty for old certs).
   * Phase 4 lands hint-by-hint, each commit keeping the fallback alive.
   * **Phase 5 commit**: regenerate all 27+ `tests/llbc/*.cert.json` via `aeneas -emit-cert`. Per CLAUDE.md cert-regen rule, this is a *single* committed regen (because schema changed). All 89 fixtures (Direct + Generated + Golden) get refreshed in one PR.
   * Phase 7 follow-up commits: retire the back-compat fallback for each hint individually (gated on "all in-tree fixtures have the hint").

### 5.3 Fixtures most affected (regen blast radius)

Predicted, based on which events appear:

| Fixture | Affected by | Reason |
|---|---|---|
| `paper.cert.json` | All hints | call_choose pattern (M9.5s/r/y all active) |
| `iterators.cert.json` / `iterators-scalar.cert.json` | `EvLoopInv.loanRegistry`, `EvMutBorrow.kindHint` | heavy loop use |
| `hashmap.cert.json` | `EvJoin.witnesses`, `EvCall.absSig` | branch-heavy, many calls |
| `list-borrows.cert.json` | `EvReborrow.parent*` | nested mut borrows |
| `traits.cert.json` / `defaulted_method.cert.json` | `EvCall.absSig` | trait-method dispatch |
| `reborrows.cert.json` | `EvMutBorrow.kindHint` (`InAbsReborrow`) | M9.5w trigger fixture |
| `loops_simple.cert.json` (Direct/) | `loanRegistry`, `kindHint(LoopOwned)` | M9.5z/aa triggers |
| Small/simple fixtures (`incr`, `compare_simple`, `bitwise`, etc.) | None directly | unaffected by hints (no joins, no calls, no loops) |

The "no hint" subset (about half of all fixtures) is unchanged by regen — useful gate that the parser back-compat actually works.

### 5.4 Workflow rule check

Per CLAUDE.md (skill `aeneas-compiler-dev` → "build rules", and the inline cert-regen rule cited in the prompt):

* Cert regen is committed only when the schema changes. This phase's commit message must explicitly call out "cert fmt_version 1 → 2; all fixtures regenerated" so reviewers see the regen is intentional.
* The regen commit MUST come *after* the OCaml emitter commit and *before* any Lean strict-path commit that depends on the new hints.

### 5.5 Risks (Phase 5)

* **Charon pin drift**: cert regen depends on the upstream Charon binary. The vertical-slice script (`scripts/check-vertical-slice.sh:12`) hardcodes `/Users/karthik/charon/charon/target/release/charon`. Regen needs a matching Charon version. Mitigation: pin Charon version in `charon-pin` *before* regenerating; do not bump in the same PR.
* **Diff noise**: regenerating 27 cert files produces a huge PR diff. Mitigation: separate regen PR from the strict-path PR. Reviewer can sanity-check schema by sampling 2-3 fixtures.

---

## Phase 6: Soundness-proof prep

Goal: ensure the hints are sufficient for `stepEvent_sound` (per `cert-format-and-soundness.md` §4.2) to be proved by case-analysis on `ev`, with each event's hint giving the case discrimination.

### 6.1 Hint → proof-case correspondence

| Event | Hint that drives case-analysis | Sound? |
|---|---|---|
| `EvMutBorrow` | `kindHint` | **Yes** — three cases, one per `MutBorrowKind` constructor, each maps to a paper rule (`E-MutBorrow` for `.direct`; `Le-Reborrow-MutBorrow-Abs` for `.inAbsReborrow`; loop-fixpoint borrow rule for `.loopOwned`). |
| `EvSharedBorrow` | — | Single rule; no hint needed. |
| `EvEndBorrow` | (kind read from `LoanInfo` already in state) | **Yes** if M9.5x is fixed (no dedupe path). |
| `EvJoin` | `witnesses` | **Yes** — each `JoinRule` constructor maps to one Fig. 11 rule. **But** see §6.2 below. |
| `EvCall` | `absSig` | **Yes** — `AbsShape.roles` directly encodes the `A_in(ρ)` content from paper §4.1 / Fig. 9. |
| `EvEndAbs` | `releasedLoans + tokenClearLocals` | **Yes** — Reorg-End-Abs side condition reads the held loans; both fields name them explicitly. |
| `EvSymExpandMutBorrow` | `parentAbs + substLocals + substLoans` | **Yes** — paper's lazy-expansion rule needs (i) the parent abs, (ii) the substitution scope; both hinted. |
| `EvReborrow` | `parentLive + parentAbs` | **Yes** — `Le-Reborrow-MutBorrow-Abs` requires parent-live as a side condition. |
| `EvLoopInv` | `loanRegistry` | **Partially.** See §6.2. |
| `EvLoopEnd` | — | Marker only; no rule fires. |
| `EvMatchArm` | — | Marker only; translator-only. |
| `EvProj` | — | Out of Option C. |
| `EvMove` / `EvCopy` / `EvAssign` / `EvAssert` / `EvBinop` / `EvPanic` / `EvRetn` | — | Single rule each; no hint needed. |

### 6.2 Hints where extra design is still needed

* **`EvJoin.witnesses` (`JoinVar`)**: The paper's `Join-Var` rule (paper Fig. 11 lower-half) folds a *whole region abstraction* into the result. Our `JoinVar` constructor is currently a marker. For the soundness proof we'll need to either (a) add a payload listing the absorbed abstraction's contents, or (b) restrict cert validity to require `JoinVar` to be preceded by an `EvEndAbs` for the absorbed abs (cleaner). Recommendation: (b), no extra hint.
* **`EvLoopInv.loanRegistry`**: gives us *which* loans the fixpoint introduces but not the fixpoint's full `≤` witness. The soundness theorem at `cert-format-and-soundness.md` §4.5 already flags loop-leak tolerance as needing the loop's region abstraction to discharge residual loans. The `loanRegistry`'s `parentAbsId` field gets us most of the way; for the *full* fixpoint side condition (paper §5.2's `Ω ≤ Ω'` after one body run) we'll later want an `EvLoopInv.fixpointWitness : Array (Nat × Nat)` mapping invariant locals to body-final locals. Flag this as "Phase 6 follow-up if needed".
* **`EvCall.absSig`**: encodes `A_in(ρ)` but not `inst_sig`'s instantiation of region variables. For the proof we'll want to verify that the instantiation matches the callee's signature. This is a *static* check (signature lookup) so it doesn't need a per-event hint; the soundness lemma carries it as a `wellFormedAbsSig` predicate.

### 6.3 Per-event proof-skeleton sketch

```lean
theorem stepEvent_sound :
  ∀ (ev : Event) (st st' : SymState) (Ω : LLBCState),
    ⟦st⟧ = Ω → stepEvent st ev = .ok st' →
    ∃ Ω', Valid(ev, Ω) ∧ Step Ω ev Ω' ∧ ⟦st'⟧ = Ω' := by
  intro ev st st' Ω hRep hStep
  cases ev with
  | mutBorrow loan place sv kindHint =>
    cases kindHint with
    | direct => exact stepMutBorrow_direct_sound ...
    | inAbsReborrow abs => exact stepMutBorrow_inAbsReborrow_sound abs ...
    | loopOwned loop => exact stepMutBorrow_loopOwned_sound loop ...
  | join l r res witnesses =>
    -- per-entry induction driven by witnesses
    exact stepJoin_witnessed_sound l r res witnesses ...
  ...
```

The structure is mechanical for every hinted event. The remaining manual work is the per-paper-rule lemma for each case — that's where the paper's §A/B appendix proofs port in.

### 6.4 Risks (Phase 6)

* No code risk (this phase is documentation + design). Risk is *underestimating* the hint surface — if a hint turns out to be insufficient mid-proof, we'll need a v3 cert format. Mitigation: prototype `stepMutBorrow_direct_sound` + `stepJoin_witnessed_sound` (the two trickiest cases) before declaring Phase 1 schema frozen.

---

## Phase 7: Sequencing & dependencies

Each numbered item is a single commit (or tightly-coupled commit pair) keeping all four gates green. Gates:

* **G1**: `bash scripts/check-vertical-slice.sh`
* **G2**: `cd aeneas-lean-checker && for t in tests/Direct/*.lean; do lake env lean --run "$t"; done`
* **G3**: `cd aeneas-lean-checker && lake build GeneratedTests`
* **G4**: `bash scripts/compare-backends.sh` on a representative subset (`paper.rs`, `iterators.rs`, `hashmap.rs`, `reborrows.rs`, `incr_cert.rs`)

### 7.1 Commit-level breakdown

| # | Commit | Phase | Gates expected | Risk notes |
|---|---|---|---|---|
| 1 | Add Lean inductives `MutBorrowKind`, `JoinRule`, `JoinEntry`, `AbsRoleEntry`, `AbsShape` + `Repr/Inhabited` instances; add optional fields with defaults to `Event` constructors. No parser changes yet. | Phase 1+3a | G1 G2 G3 G4 all green (defaults preserve behaviour) | Trivial — just type-level additions. |
| 2 | Extend `Json/Parser.lean` to parse all new fields (with back-compat defaults). | Phase 3b | All green; new fields all default to empty/false/none on existing certs. | Trivial; pattern-matches existing `releasedLoans` handling. |
| 3 | Bump OCaml `cert_fmt_version: 1 → 2`, add new OCaml types in `CertEvent.ml/mli` with empty defaults, extend `CertJson.ml` to emit them (still empty). | Phase 2a | G1 (regen test cert; emit version 2 but no hints) — green. G2/G3/G4 green (parser tolerates new version, no hints to consume). | Verify Lean parser accepts v2 with no hints. |
| 4 | OCaml emit `EvMutBorrow.kindHint` (M9.5w + M9.5aa source). Cert regen in same commit for `tests/llbc/` (this commit's diff is dominated by JSON, but the change is mechanical). | Phase 2b | G1 green. G2/G3 green (Lean still uses fallback). G4 expected diff on `reborrows` / `iterators` fixtures (hint now present but Lean side ignores it). | First "hint actually reaches Lean" commit — verify by logging hint-coverage. |
| 5 | Same pattern: OCaml emit `EvReborrow.parentLive/parentAbs`; regen affected fixtures. | Phase 2c | Same as #4. | |
| 6 | OCaml emit `EvSymExpandMutBorrow.parentAbs/substLocals/substLoans`. | Phase 2d | Same. | The `substLocals/Loans` emission requires modifying `replace_symbolic_values`; verify it doesn't perturb the OCaml side's own behaviour (it shouldn't — pure logging). |
| 7 | OCaml emit `EvCall.absSig`. | Phase 2e | Same. | Verify against `paper.rs::call_choose` — the canonical `A_in` shape. |
| 8 | OCaml emit `EvEndAbs.tokenClearLocals`. | Phase 2f | Same. | |
| 9 | OCaml emit `EvLoopInv.loanRegistry`. | Phase 2g | Same. | |
| 10 | OCaml emit `EvJoin.witnesses` — first half: `JoinSame`, `JoinSymbolic`, `JoinVar`. | Phase 2h | Same. | |
| 11 | OCaml emit `EvJoin.witnesses` — second half: `JoinMutBorrows`, `JoinBottomOther`, `JoinOtherBottom`. | Phase 2i | Same. | This is the M9.5y rule; verify `paper::call_choose` fixture's join now carries `JoinMutBorrows`. |
| 12 | **OCaml**: drop redundant post-join `EvEndBorrow` emission. Regen *all* fixtures (this is the M9.5x structural-invariant fix). | Phase 2j / Phase 5 | G1 green. G2/G3 green only because Lean still has `joinDedupe` fallback. G4 expected diff on every branchy fixture. | Largest cert diff so far; pair with explicit changelog. |
| 13 | **Lean**: strict-path for `kindHint` (Phase 4.1.1) — only fires when hint is present, falls back otherwise. | Phase 4a | All green. | |
| 14 | Lean strict-path for `EvReborrow` (4.1.4). | Phase 4b | All green. | |
| 15 | Lean strict-path for `EvSymExpandMutBorrow` (4.1.5). | Phase 4c | All green. | |
| 16 | Lean strict-path for `EvEndAbs.tokenClearLocals` (4.1.7). | Phase 4d | All green. | |
| 17 | Lean strict-path for `EvLoopInv.loanRegistry` (4.1.3). | Phase 4e | All green. | |
| 18 | Lean strict-path for `EvJoin.witnesses` — gated behind env var `AENEAS_STRICT_JOIN=1` (4.1.2). | Phase 4f | All green (gate off by default). G4 must be run with `AENEAS_STRICT_JOIN=1` on the representative subset before merge. | Largest Lean diff. |
| 19 | Add `AbsRegistry` to `SymState`; populate from `EvCall.absSig`; validate in `stepEndAbs` (4.1.8). | Phase 4g | All green. | |
| 20 | Delete `joinDedupe` / `recentlyEnded` / M9.5x branches from Lean side. Pre-requisite: commit #12 landed, and all in-tree fixtures regenerated. | Phase 4h | All green (no remaining cert carries the redundant end). | If G2 or G3 fails, a fixture wasn't regenerated; the failure points exactly at which one. |
| 21 | Delete `loopDepth` from `SymState` (folded into `kindHint`). | Phase 4i | All green. | |
| 22 | Flip `AENEAS_STRICT_JOIN` to default-on; remove the pragmatic `joinEntryOk` fallback. | Phase 4j | All green. | First commit where the Lean side has no `M9.5y` shortcut. |
| 23 | Retire per-hint fallbacks one-by-one (reborrow, expand, endAbs, loopInv, mutBorrow). Each is its own commit; each deletes ~5-10 lines of fallback code. | Phase 4k-4o | All green (all in-tree certs are now v2 with hints). | Safety net: temporarily keep a `--legacy-cert` CLI flag that re-enables fallbacks for users with v1 cert files in-flight. |
| 24 | Docs + soundness skeleton: update `cert-format-and-soundness.md` §3.2 to mark which weaknesses are now eliminated; add a stub `AeneasCheck/Theorems/StepEventSound.lean` with the per-event case-analysis skeleton (no proofs yet). | Phase 6 | All green. | |

### 7.2 Gate-by-gate expectations across the sequence

| Commit # | G1 (vert. slice) | G2 (Direct) | G3 (GeneratedTests) | G4 (compare-backends) |
|---|---|---|---|---|
| 1-3 | green | green | green | green |
| 4-11 | green | green | green | **EXPECTED**: certs now larger (new fields); compare diff is no-op on Lean output |
| 12 | green | green if joinDedupe still present; else regress | green | regen diff dominates |
| 13-17 | green | green | green | green |
| 18 | green | green (gate off) | green | green when run with gate off; *must* be run with gate on as a pre-merge step |
| 19 | green | green | green | green |
| 20 | green only after commit 12 | green only after commit 12 | green | green |
| 21-23 | green | green | green | green |
| 24 | green (no code change) | green | green | green |

**Temporary regressions allowed**: commit 18 G4-strict (manually run). No other commit is allowed to fail any gate.

### 7.3 Dependency DAG (high-level)

```
1 → 2 → 3 → {4, 5, 6, 7, 8, 9, 10, 11}
              ↓ ↓ ↓ ↓ ↓ ↓ ↓ ↓
              {13, 14, 15, 16, 17, 18, 19} (each strict-path depends on its emit commit)
                                  ↓
                            12 → 20 (M9.5x fix)
                                  ↓
                            18 → 22 (strict join flip)
                                  ↓
                            21, 23 (fallback retirement)
                                  ↓
                                  24
```

### 7.4 Risks (Phase 7)

* **Charon-pin coupling**: commit 4-11's regen requires Charon to be at a stable version. Don't bump `charon-pin` within this sequence.
* **Reviewer fatigue**: 24 commits is a lot. Bundle commits 4-11 as a single "OCaml hint emission" PR (review the schema once), commits 13-19 as a "Lean strict-path" PR (review the strict-vs-fallback pattern once), and reserve standalone PRs for the structural-invariant fix (12+20) and the join flip (18+22).
* **Lake build cache**: `lake build GeneratedTests` is slow; CI must cache `.lake/build`. The plan assumes ~2 min per gate-G3 run; if it's 10 min, throttle the per-commit gates and run G2+G4 always, G1+G3 on PR-final only.

---

## Aggregate effort estimate

| Phase | Days | Notes |
|---|---|---|
| Phase 0 (audit) | 0.5 | This document. |
| Phase 1 (schema) | 1.5 | Type definitions + sample cert by hand to validate JSON shape. |
| Phase 2 (OCaml emitter) | 4-6 | Bulk of the work. `EvJoin.witnesses` (commits 10-11) alone is 1.5-2 days. |
| Phase 3 (Lean parser) | 0.5 | Mechanical. |
| Phase 4 (Lean checker tightening) | 5-7 | 11 commits, most are <1h, but `EvJoin` strict path (commit 18) is 1.5 days. |
| Phase 5 (Migration) | 1.5 | Regen + diff review + Charon coordination. |
| Phase 6 (Soundness prep) | 1 | Docs + skeleton; no proofs. |
| Phase 7 (Sequencing buffer) | 1-2 | Unforeseen bugs, gate flakes. |
| **Total** | **15-20 days** | Single-developer focus, no parallelism. |

Parallelisation: phases 2 and 3 can run concurrently after phase 1; phase 6 can run concurrently with phase 4. With 2 developers and clean handoff, the work compresses to **~10-12 days**.

---

## Cross-cutting risks

1. **Hint-vs-reality drift**: nothing currently prevents OCaml from emitting a wrong hint (e.g. `kindHint = .direct` for a place that has a Deref projection). The Lean side would notice at the strict-path stage and fail. Mitigation: add an OCaml-side sanity check that the emitted hint matches the projection structure (one-line `assert`).
2. **Soundness theorem revisions**: §6 may reveal that one hint is insufficient. Phase 1 should not lock the schema until §6's two prototype proofs (`stepMutBorrow_direct_sound` + `stepJoin_witnessed_sound`) typecheck. If they don't, bump to `fmt_version=3` *before* shipping Phase 2.
3. **OCaml interpreter perturbation**: any change to `InterpJoin.ml` risks altering the join result subtly. Mitigation: each emit-commit must pass `cargo test --release` in `tests/lean-checker/differential/` (already gate G6 of `check-vertical-slice.sh`) and the OCaml self-tests.
4. **Cert size blowup**: with all hints, average cert grows by 20-40%. If user-facing tooling chokes on multi-MB certs (`hashmap.cert.json`, `iterators.cert.json` will likely double), consider gzipping cert output as a follow-up.
5. **Future Tier-3 work**: this plan deliberately does *not* model abstraction structure in `SymState` (only an `AbsRegistry` for validation). That's correct for Option C, but means M9.5d/f/p stay around. Tier-3 work will eventually replace them with proper structural Val modelling.

---

## Critical Files for Implementation

- `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Raw/CertEvent.lean`
- `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Json/Parser.lean`
- `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/LLBCSharp/Step.lean`
- `/Users/karthik/aeneas/aeneas-lean-checker/AeneasCheck/Typecheck/Stmts.lean`
- `/Users/karthik/aeneas/src/cert/CertEvent.ml` (with `.mli` and `src/cert/CertJson.ml` as companions)

Secondary (Phase 2 emit-site touchpoints): `/Users/karthik/aeneas/src/interp/InterpStatements.ml`, `/Users/karthik/aeneas/src/interp/InterpBorrows.ml`, `/Users/karthik/aeneas/src/interp/InterpExpansion.ml`, `/Users/karthik/aeneas/src/interp/InterpExpressions.ml`, `/Users/karthik/aeneas/src/interp/InterpJoin.ml`.
