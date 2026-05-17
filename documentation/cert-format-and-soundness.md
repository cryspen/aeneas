# LLBC# Certificates: Format, Semantics, and Soundness

This document describes the *certificate* format consumed by the Aeneas
Lean checker (`aeneas-lean-checker`), maps each cert construct to the
LLBC# semantics from Ho/Fromherz/Protzenko's *"Sound Borrow-Checking for
Rust via Symbolic Semantics (Long Version)"* (arXiv:2404.02680v2, Jul
2024), and sketches the soundness theorem we intend to prove in Lean.

The cert is produced by the OCaml Aeneas interpreter (`src/cert/` in the
Charon/Aeneas tree) and consumed by the Lean checker
(`aeneas-lean-checker/AeneasCheck/`). Section numbers in citations refer
to the paper.

---

## 1. The OCaml ⇄ Lean pipeline

```
                               aeneas (OCaml)                                lake/Lean
   ┌──────────┐    Charon    ┌──────────────────┐   cert.json   ┌─────────────────────────┐
   │  Rust.rs │ ──────────▶  │  LLBC# interp    │ ────────────▶ │  aeneas-lean-checker    │
   └──────────┘              │  (CertGen hooks) │               │  (parse → tc → replay → │
                             └──────────────────┘               │   translate → emit)     │
                                                                └─────────────────────────┘
                                                                            │
                                                                            ▼
                                                                  Pure Lean .lean module
```

The OCaml side runs the LLBC# symbolic interpreter (paper §4.1) and
records its execution trace. A **certificate** is a per-crate JSON file
listing, for every function reachable from the entry point: its
signature, its source span, an ordered list of *events* witnessing the
LLBC# reductions performed by the interpreter, and a final-state
snapshot. The Lean checker re-runs the trace against an executable
mirror of the LLBC# state machine, fails fast on any inconsistency, and
on success translates the trace into pure Lean source.

The Lean side has three layers (mirroring the paper's `LLBC# ⇒ LLBC ⇒ PL`
hierarchy of Fig. 1):

| Lean module                     | Role                                       | Paper analogue              |
|---------------------------------|--------------------------------------------|-----------------------------|
| `AeneasCheck.Raw`               | Cert parsing (events, places, types, ADTs) | (the cert format itself)    |
| `AeneasCheck.Typecheck`         | Per-event structural well-formedness       | Borrow-graph well-formedness|
| `AeneasCheck.LLBCSharp`         | Step-by-step replay of the LLBC# trace     | LLBC# operational semantics |
| `AeneasCheck.Translate / Pure`  | Cert → pure Lean function lift             | The Aeneas Forward translator|
| `AeneasCheck.Backends`          | Pretty-printers (Lean / Rust)              | —                           |

The cert format is the contract between the OCaml interpreter and the
Lean replayer. Everything downstream — translation, emission, and the
eventual end-to-end soundness theorem — is built on the assumption that
the cert is a *true witness* of an LLBC# execution.

---

## 2. Cert format reference

The authoritative schema lives in
`aeneas-lean-checker/AeneasCheck/Raw/CertEvent.lean`. This section
describes the constructs and the LLBC# rule each one witnesses.

### 2.1 Top-level: `CrateCert` (cert v4)

```
structure CrateCert where
  fmtVersion  : Nat                 -- must be 4 (M9.8 rejects all earlier versions)
  crateHash   : String              -- digest of the source crate
  functions   : Array FunCert       -- the per-function execution traces
  llbcProgram : LlbcProgram         -- the post-pre-pass LLBC subtree
```

The cert v4 format (introduced in M9.8) refines v3's
`JrJoinMutBorrows` rule to carry the full `AbsShape` (id + parents +
roles) of the fresh region abstraction created by the
Collapse-Dup-MutBorrow join rule (paper Fig. 11), so the Lean
replayer can install the abs in `SymState.absRegistry` from cert
data alone — closing the C23 "fresh abs" soundness gap that the
M10 LLBC# soundness campaign had escalated. All other v3 shape is
preserved verbatim.

The cert v3 format (introduced in M9.7d) embeds the
*post-pre-pass* LLBC program as a structured subtree under
`llbcProgram`. This replaces the flat `typeDecls` / `traitDecls` /
`traitImpls` / signature-string mirrors that v1 and v2 carried.

```
structure LlbcProgram where
  typeDecls   : Array LlbcTypeDecl    -- struct / enum / alias / union ADTs
  funDecls    : Array LlbcFunDecl     -- per-function signatures + locals + body
  traitDecls  : Array LlbcTraitDecl
  traitImpls  : Array LlbcTraitImpl
  globalDecls : Json                  -- opaque until a future milestone
  charonVersion : String
```

The crate-level lookup tables (now `llbcProgram.{typeDecls, traitDecls,
traitImpls}`) are *static*: they describe the program, not its
execution. They have no direct counterpart in the LLBC# operational
semantics but are necessary for the translator to lift abstract Rust
types into Lean inductive / structure / class declarations.

Function signatures, type-parameter names, trait obligations, and
the per-local LLBC type table all live inside `llbcProgram.funDecls`
(matched to each `FunCert` by `fnName` / `itemMeta.name`). The pre-v3
`FunCert.signature : FnSignature` opaque-string mirror was retired in
M9.7o-E5b; the translator consumes the structured `LlbcSignature` /
`LlbcTy` directly.

### 2.2 Per-function: `FunCert`

```
structure FunCert where
  fnId        : Nat
  fnName      : String
  sourceSpan  : Option SourceSpan
  events      : Array Event        -- the LLBC# trace
  finalState  : StateSummary
  prettyName  : Option String
```

The function's input/output types and trait obligations are *not*
carried on `FunCert` directly — they live in the matching
`LlbcProgram.funDecls` entry as a structured `LlbcSignature`. The
match is by `fnName` (which equals the Charon `itemMeta.name` of the
corresponding `LlbcFunDecl`). The translator threads each
`(FunCert, LlbcFunDecl)` pair into `translateFunWith`. This
corresponds to the `f⟨ρ⟩(x: τ)(y: τ′)(xret: τret){s}` binder shape used
by **E-Call-Symbolic** (paper Fig. 9). The lifetime parameters `ρ` are
not materialised explicitly: they are recoverable from the region
abstractions emitted by `EvCall` and closed by `EvEndAbs`.

`events` is the witness proper: an ordered list of LLBC# reductions
the interpreter performed while evaluating the function body.
`finalState` carries the post-state snapshot used by the translator to
bind output value names.

### 2.3 Events

Every event constructor maps to one LLBC# / LLBC#-extension rule from
the paper. The table below uses the paper's rule names; figure
references are to the long-version PDF.

| Cert event                                          | Paper rule(s)                              | Where in Lean                                  |
|-----------------------------------------------------|--------------------------------------------|------------------------------------------------|
| `EvMutBorrow loan place sv`                         | **E-MutBorrow** (Fig. 3)                   | `Step.stepMutBorrow`                           |
| `EvSharedBorrow loan sbId place sv`                 | **E-SharedBorrow** (Fig. 3)                | `Step.stepSharedBorrow`                        |
| `EvEndBorrow loan {givenBack}`                      | **Reorg-End-MutBorrow** (Fig. 3) + E-Reorg | `Step.stepEndBorrow`                           |
| `EvMove src dst`                                    | **E-Move** (Fig. 3)                        | `Step.stepMove`                                |
| `EvCopy src dst`                                    | E-Copy (paper omits the rule for brevity)  | `Step.stepCopy`                                |
| `EvAssign dst rhs`                                  | **E-Assign** (Fig. 3)                      | `Step.stepAssign`                              |
| `EvAssert cond expected`                            | E-Assert (sugar for `if not cond then panic`) | `Step.stepAssert`                            |
| `EvBinop op lhs rhs dst`                            | E-BinaryOp (rvalue reduction)              | `Step.stepBinop`                               |
| `EvPanic`                                           | **E-Panic** (Fig. 3)                       | `Replay.stepEvent` (passthrough)               |
| `EvRetn`                                            | **E-Step-Return** (Fig. 7)                 | `Replay.stepEvent` (passthrough)               |
| `EvReborrow child parent place`                     | Le-Reborrow-MutBorrow-Abs (Fig. 8) on entry | `Step.stepReborrow`                           |
| `EvCall fn callId fnName args dst regionAbs`        | **E-Call-Symbolic** (Fig. 9)               | `Step.stepCall`                                |
| `EvEndAbs abs finalValues releasedLoans`            | **Reorg-End-Abs** (paper §4.1, Fig. 8)     | `Step.stepEndAbs`                              |
| `EvSymExpandMutBorrow svId bid innerSv`             | Lazy mut-borrow expansion (§4.1, no named rule) | `Step.stepSymExpandMutBorrow`             |
| `EvJoin left right result`                          | **Join-Same / Join-Symbolic / Join-MutBorrows / Join-Var / Collapse-***  (Fig. 11) | `Step.stepJoin` |
| `EvLoopInv loopId invariant`                        | Loop fixpoint snapshot (§5.2)              | `Replay.stepEvent` (registers fixpoint loans)  |
| `EvLoopEnd loopId`                                  | End of loop body (§5.2)                    | `Replay.stepEvent` (closes loop scope)         |
| `EvMatchArm scrutinee adtId variantId variantName`  | Variant-arm marker (extension to E-IfThenElse-Symbolic, generalised to enums) | `Replay.stepEvent` (no-op; translator uses it) |
| `EvProj abs place sv`                               | Projection into a region abstraction        | (stub; rejected pre-M10)                       |

#### 2.3.1 Detailed mapping

##### `EvMutBorrow loan place sv`

LLBC# **E-MutBorrow** (Fig. 3) reads:

```
⊢ Ω(p) ⇒ v       ⊥, loan^{s,m} ∉ v        ℓ fresh
─────────────────────────────────────────────────
Ω ⊢ &mut p ⇓  (borrow^m ℓ v, Ω')
```

The cert event records the fresh loan id `ℓ` (`loan`), the place `p`
being borrowed (`place`), and the symbolic value `v` that flows into
the borrow body (`sv`). `Step.stepMutBorrow` checks freshness, parks a
`mutLoan` token in the place's root local, and registers the loan in
`SymState.loans`. Two pragmatic refinements are layered on top:

* **M9.5w** — a `&mut (*x).f` whose projection contains any `Deref` is
  classified as a `reborrow`-class loan rather than a direct one. Its
  lifetime is owned by the parent input abstraction (which the cert
  does not explicitly end), so `checkFnPost` tolerates it leaking past
  function exit.
* **M9.5aa** — a `&mut local` issued while a loop body is open
  (`loopDepth > 0`) is classified as `.lazyExpand` so the leaked-loan
  check tolerates it. The OCaml interpreter does not emit an explicit
  end for these; the loop's region abstraction owns their lifetime.

##### `EvEndBorrow loan {givenBack}`

LLBC# **Reorg-End-MutBorrow** (Fig. 3) reads:

```
hole of Ω[loan^m ℓ, .] not inside a borrow         loan^{s,m} ∉ v
─────────────────────────────────────────────────────────────────
Ω[loan^m ℓ, borrow^m ℓ v] ↪ Ω[v, ⊥]
```

The cert event names the loan id being ended (`loan`) and carries the
symbolic value that flows back through the loan side (`givenBack`).
`Step.stepEndBorrow` looks up the loan, evaluates the restoration value
in the current state, and writes it back into whichever local currently
holds the `mutLoan ℓ` token.

Two refinements:

* **Reorg** is implicit. The paper's `E-Reorg` rule lets the
  interpreter apply ↪ rewrites *anywhere* in evaluation. The cert
  doesn't carry a separate "reorg" event; instead, every
  `EvEndBorrow` *is* a witness that the OCaml interpreter chose to
  apply Reorg-End-MutBorrow at that point.
* **M9.5x branch-dedupe** — the OCaml interpreter linearises each
  branch's cleanup separately and then emits a redundant
  post-reconciliation `EvEndBorrow` on the same loan. The Lean replayer
  records every successful end in a `joinDedupe` set and silently
  no-ops any subsequent end of an already-ended loan. This does **not**
  weaken double-end detection — a genuine bug must re-`EvMutBorrow` the
  same id first, which still fails the `reused after being ended` check
  in `Typecheck.addLoan`.

##### `EvCall fn callId fnName args dst regionAbs`

LLBC# **E-Call-Symbolic** (Fig. 9) summarises the entire callee body in
a single step: lifetimes `ρ` are freshened, fresh region abstractions
`A_in(ρ)` are introduced for the input contract, arguments are mapped
to `⊥` (their ownership flows into the abstraction), and the
destination is bound to a fresh symbolic value drawn from the callee's
`out_sig`.

The cert event carries the callee's qualified name (`fnName`, used by
the translator to resolve the Lean callee), a stable `callId` (used to
correlate with subsequent `EvEndAbs` events), the symbolic argument
expressions (`args`), the destination place (`dst`), and the list of
freshly-allocated region-abstraction ids (`regionAbs`). The Lean
replayer doesn't (yet) model the contract algebra of `inst_sig`; it
binds the destination to a fresh symbolic placeholder, mirroring the
LLBC# rule's `pz ↦ σ`.

##### `EvEndAbs abs finalValues releasedLoans`

LLBC# **Reorg-End-Abs** (Fig. 8): a region abstraction can be
terminated provided it contains no live loans. Doing so "hands all the
borrows being held back to the caller, inside fresh anonymous variables"
(paper §4.1).

The cert event carries the abstraction id (`abs`), one symbolic value
per `[AEndedMutBorrow]` the abstraction held (`finalValues`, used by
the translator to bind post-state names), and the loan ids the
abstraction owned and is now releasing (`releasedLoans`).
`Step.stepEndAbs` mirrors the side effect: drop each released loan from
`SymState.loans` and clear any local still holding its `mutLoan` token.

This is the cert's witness for the `paper.rs::call_choose` pattern
(paper §4.1, lines 5–8): the `&mut x` and `&mut y` borrows that flowed
into `choose`'s region abstraction `A(ρ)` are implicitly ended when the
abstraction closes, without an explicit `EvEndBorrow` for each.

##### `EvSymExpandMutBorrow svId bid innerSv`

The OCaml interpreter sometimes leaves the **`pz ↦ σ`** result of an
`E-Call-Symbolic` opaque until the caller actually dereferences the
returned borrow. At that point it expands `σ` into a concrete
mut-borrow `borrow^m bid σ'`. The paper does not call out this lazy
expansion as a separate rule (it is implicit in the rewriting
discipline), but the cert needs an explicit event so the replayer can
keep its state machine in sync.

`Step.stepSymExpandMutBorrow` substitutes every occurrence of
`.sym svId` (in `env` and in loan-given values) with `.mutLoan bid`,
then registers loan `bid` with `given := .sym innerSv` and kind
`.lazyExpand`. The `.lazyExpand` kind has the same end-borrow semantics
as `.direct` but is allowed to leak past function exit (its lifetime is
owned by the caller's abstraction).

##### `EvJoin left right result`

LLBC# join is the centrepiece of the paper's §5. The cert serialises
the witness as three state summaries: the two branch end-states (`left`,
`right`) and the joined result (`result`). Each `StateSummary` is a
pair of `(env, liveLoans)`.

The paper's join is the transitive closure of the rules in Fig. 11:

* **Join-Same** — when both branches agree on a value, the result is
  that value.
* **Join-Symbolic** — when they differ on a value containing no
  borrows/loans, the result is a fresh symbolic value `σ`.
* **Join-MutBorrows** — when both branches hold a mut borrow but with
  different loan ids `ℓ_0`, `ℓ_1`, the join introduces a fresh
  borrow id `ℓ_2` and a fresh region abstraction `A' { borrow^m ℓ_0 _,
  borrow^m ℓ_1 _, loan^m ℓ_2 }`.
* **Join-Bottom-Other / Join-Other-Bottom** — `⊥` propagates upwards;
  the surviving side is abstracted away.
* **Collapse-Merge-Abs / Collapse-Dup-MutBorrow** — flatten duplicated
  borrow/loan structure across abstractions.

`Step.stepJoin` does a *pragmatic* check rather than re-running the
full join algebra: for each entry in `result.env`, it accepts the
witness when either (a) both branches agree by `symExprBeq` (Join-Same),
or (b) the result is a "fresh-sym form" — either `SymVal n` (Join-Symbolic)
or `SymMutBorrowTok n` (Join-MutBorrows/Collapse-Dup-MutBorrow, M9.5y).
This is sound modulo the cert promise that the OCaml interpreter
already discharged the side conditions; the full ≤-algebra is the
subject of the soundness theorem (§4 below).

**M9.8 (cert v4): `JoinMutBorrows` carries the fresh abs's shape.**
Each `JrJoinMutBorrows` rule in the witnesses array now carries a
full `AbsShape` (id + parents + roles) for the fresh region
abstraction created by Collapse-Dup-MutBorrow. The OCaml emitter
populates this with `parents = []` and `roles = [(MutBorrow,
l_left), (MutBorrow, l_right), (MutLoan, l_fresh)]` (paper Fig. 11
canonical content). `Step.stepJoin` installs the shape in
`SymState.absRegistry` via `SymState.addAbsShape`, mirroring how
`stepCall` already installs `EvCall.abs_sig` shapes. On the
soundness side the paper's `JoinEntryStep.mutBorrows` lifts this
same `AbsShape` via `liftAbsShape`, so `concretise st' = Ω'`
follows by construction (no axiomatic-abs-creation needed).

##### `EvLoopInv loopId invariant` and `EvLoopEnd loopId`

The paper extends LLBC# with loop support in §5.2 by computing a
**fixpoint** of the state on entry to the loop. The fixpoint witnesses
the invariant: starting from it and running the body once yields a
state ≤-related back to the invariant (up to substitution of fresh
borrow/abstraction ids).

The cert serialises one `EvLoopInv` event at the entry of each loop's
canonical body, carrying the fixpoint state as a `StateSummary`. A
paired `EvLoopEnd` marks the end of the body.

In the Lean replayer:

* **M9.5z** — `EvLoopInv` registers loop-introduced borrow ids (those
  appearing as `SymMutBorrowTok n` in `invariant.env` or in
  `invariant.liveLoans`) as `.reborrow`-class loans so subsequent
  in-body `EvEndBorrow` events resolve and so the function-exit leak
  check tolerates them.
* **M9.5aa** — `EvLoopInv` also bumps `loopDepth`; `EvLoopEnd`
  decrements it. While `loopDepth > 0`, `stepMutBorrow` classifies
  direct `&mut local` borrows as `.lazyExpand` so they too may leak.

##### `EvMatchArm scrutinee adtId variantId variantName`

This event has no direct paper analogue. The paper handles control flow
through `E-IfThenElse-Symbolic` (paper §5, mentioned in passing); the
`match` case generalises this to an arbitrary enum scrutinee. The cert
event is a *translator marker*, not a state mutation: the replayer
treats it as a no-op, and the translator uses the markers to partition
the event sequence into per-arm bodies which it lifts into a Lean
`match` expression.

### 2.4 State summary (`StateSummary`)

```
structure StateSummary where
  env       : Array (Nat × SymExpr)
  liveLoans : Array Nat
```

A `StateSummary` is an abstraction of an LLBC# state `Ω`: per-local
symbolic values and the set of live loan ids. It appears in
`EvJoin`, `EvLoopInv`, and the cert's `finalState`. It does **not**
carry region-abstraction structure (the cert assumes the OCaml side
has already discharged the relevant ≤ algebra).

### 2.5 Symbolic expressions (`SymExpr`)

```
inductive SymExpr
  | symVal (id : Nat)                                  -- σ_n
  | symLit (l : Lit)                                   -- n, true, false, …
  | symCopy (p : Place)                                -- copy p
  | symMove (p : Place)                                -- move p
  | symMutBorrowTok (borrowId : Nat)                   -- borrow^m ℓ _
  | symVariant adtId variantId variantName fields      -- Ctor x1 … xK
  | symTuple fields                                    -- (x1, …, xK)
  | symRecord adtId fields                             -- { f1 := x1, … }
```

`SymExpr` is the cert's surface syntax for the *rvalues* the OCaml
interpreter feeds into `EvAssign` and friends. It is a strict superset
of LLBC's `rv` grammar (paper Fig. 2) plus the symbolic value
constructors that distinguish LLBC# from LLBC. `symMutBorrowTok ℓ`
corresponds exactly to the value `borrow^m ℓ _` (with the inner value
abstracted away).

---

## 3. The Lean replayer as a partial executable LLBC# semantics

`AeneasCheck.LLBCSharp.SymState` is the Lean mirror of an LLBC# state
`Ω`:

```
structure SymState where
  env        : Std.HashMap Nat Val            -- locals → symbolic values
  loans      : Std.HashMap Nat LoanInfo       -- live borrow ids (with kind + given-back value)
  numLocals  : Nat
  joinDedupe : Std.HashSet Nat                -- M9.5x: redundant-end tolerance
  loopDepth  : Nat                            -- M9.5aa: open-loop counter
```

`Val` (in `LLBCSharp/Values.lean`) is the symbolic counterpart of
LLBC's value grammar `v ::= n | ⊥ | loan^m ℓ | borrow^m ℓ v | …`,
restricted to the direct-borrow subset the replayer currently models:
`sym n`, `lit l`, `mutLoan b`, `mutBorrow b inner`, `bottom`.

`LoanInfo.kind` distinguishes between
* `.direct` — a borrow created in-body by `EvMutBorrow`; *must* be
  explicitly ended before function exit;
* `.shared` — a shared borrow (E-SharedBorrow);
* `.reborrow` — a borrow whose lifetime is owned by a parent
  abstraction (input parameter, loop fixpoint, `&mut (*x).f`); allowed
  to leak past function exit;
* `.lazyExpand` — a borrow created by `EvSymExpandMutBorrow` or by an
  in-loop direct `&mut`; parks a `mutLoan` token like `.direct` but
  may leak past exit.

`Replay.stepEvent` is the body of the per-event step relation:

```
def stepEvent (st : SymState) (ev : Event) : Except String SymState
```

`Replay.replayFun` folds the events of one `FunCert` and then applies a
function-exit post-condition: no `.direct`-class loan may be live at
exit. `Replay.replayCrate` runs the typechecker first (so structural
errors are flagged before semantic ones), then replays each function.

### 3.1 Direct mapping cert ↔ LLBC# rules

| LLBC# judgement                                  | Lean function                                          | Pre-condition                              |
|--------------------------------------------------|--------------------------------------------------------|--------------------------------------------|
| `Ω ⊢ &mut p ⇓ (borrow^m ℓ v, Ω')`                | `stepMutBorrow`                                        | `ℓ ∉ dom(loans)`, root local in scope      |
| `Ω ⊢ &p     ⇓ (borrow^s ℓ v, Ω')`                | `stepSharedBorrow`                                     | `ℓ ∉ dom(loans)`, root local in scope      |
| `Ω[loan^m ℓ, borrow^m ℓ v] ↪ Ω[v, ⊥]`            | `stepEndBorrow` (`.direct` / `.lazyExpand` branch)     | `ℓ ∈ dom(loans)`, env carries `mutLoan ℓ` |
| `Reorg-End-Abs`                                  | `stepEndAbs`                                           | each released ℓ in `dom(loans)` or absent  |
| `E-Call-Symbolic` (paper Fig. 9)                 | `stepCall`                                             | destination root local in scope            |
| `Ω ⊢ move p ⇓ (v, Ω')`                           | `stepMove`                                             | (no precondition at the replayer)          |
| `Ω ⊢ p := rv ⇓ ((), Ω''')`                       | `stepAssign`                                           | (no precondition at the replayer)          |
| Join algebra (Fig. 11)                           | `stepJoin`                                             | per-entry `Join-Same` or fresh-sym         |
| Loop fixpoint (§5.2)                             | `stepEvent` on `loopInv` (registers loans, bumps depth)| (no precondition)                          |

### 3.2 Where the replayer is intentionally weaker than the paper

Several deliberate simplifications. M9.6 (Option C, see
`option-c-implementation-plan.md`) closed weaknesses 1 and 2 by
adding rule-choice *hints* on `EvCall` / `EvJoin` /
`EvSymExpandMutBorrow` / etc.; the rest remain.

1. ~~**Region abstractions are not first-class.**~~ (M9.6
   eliminated.) `EvCall.absSig : Array AbsShape` now carries
   the paper's `A_in(ρ)` content — for each freshened region
   abstraction, the list of `MutBorrow` / `MutLoan` /
   `SharedBorrow` roles plus ancestor abs ids. The Lean
   replayer's `SymState.absRegistry` indexes these by abs id;
   `stepEndAbs` validates that each released loan appears in
   the recorded role list. Abstraction structure is still not
   tracked at the value-grammar level (the role list is the
   `A_in(ρ)` summary, not the full nested borrow grammar), but
   the abs ids are no longer opaque tokens.
2. ~~**The join algebra is checked pragmatically.**~~ (M9.6
   eliminated.) `EvJoin.witnesses : Array JoinEntry` carries
   one Fig. 11 rule witness per result-env local. The
   `Step.joinEntryStrictOk` check re-runs the rule's side
   conditions per entry (Join-Same / Join-Symbolic /
   Join-MutBorrows / Join-Var / Join-Bottom-Other /
   Join-Other-Bottom). The pragmatic `joinEntryOk` +
   `isFreshSym` shortcuts were retired in commit M9.6v.
3. **`EvProj` is not handled.** The replayer rejects it. Adding it
   requires modelling per-abstraction sub-borrow structure (M10+).
4. **No type checking at the replayer level.** The paper's type-safety
   guarantee is left to the LLBC# semantics; the replayer's only check
   is structural (borrows are paired, loan ids fresh).

Remaining weaknesses (3 and 4) are *load-bearing* for the
soundness theorem: the theorem must say "if the cert passes the
replayer, then there exists an LLBC# derivation that *would have*
satisfied the omitted side conditions". §4 makes this precise.

### 3.2.1 M9.6 hint inventory (Option C — for the proof skeleton)

The following hints (all optional fields on existing event
constructors; defaults preserve v1 behaviour) drive the
strict-only paths the soundness skeleton in
`AeneasCheck/Theorems/StepEventSound.lean` will case-analyse:

| Event | Hint | Eliminates the M9.5 pragmatic shortcut |
|---|---|---|
| `EvMutBorrow` | `kindHint : MutBorrowKind` | M9.5w + M9.5aa |
| `EvReborrow` | `parentLive : Bool`, `parentAbs : Option Nat` | implicit-parent invention |
| `EvSymExpandMutBorrow` | `parentAbs`, `substLocals`, `substLoans` | M9.5r env-scan + lazyExpand silent end |
| `EvCall` | `absSig : Array AbsShape` | "abstraction ids are opaque tokens" |
| `EvEndAbs` | `tokenClearLocals : Array Nat` | M9.5s env-scan |
| `EvLoopInv` | `loanRegistry : Array (Nat × Nat)` | M9.5z |
| `EvJoin` | `witnesses : Array JoinEntry` | M9.5y |

---

## 4. Soundness theorem (sketch)

We aim to prove, *in Lean*, that a successful run of `replayCrate`
implies the existence of a valid LLBC# derivation — and therefore, by
the paper's main result (Theorem 4.1), safe execution at the PL level.

### 4.1 Definitions

Let `ℙ` denote the set of programs (cert + LLBC# source code). Fix a
program `P ∈ ℙ` and let `cc : CrateCert` be its cert.

**LLBC# states.** Let `LLBCState` be the inductive Lean datatype
encoding the paper's `Ω#` from §4. We have a representation function

```
⟦ · ⟧ : SymState → LLBCState
```

that lifts the replayer's restricted state into a full LLBC# state by
materialising trivial (empty) region abstractions for each
`.reborrow` / `.lazyExpand` loan.

**LLBC# trace.** Let `⟶_#` denote the small-step LLBC# reduction
relation derived from the paper's rules (Fig. 9 plus the join, loop
fixpoint, and pragmatic extensions of Fig. 11). Write `Ω ⟶_#* Ω'` for
the reflexive-transitive closure.

**Cert validity.** Define `Valid(ev, Ω#) : Prop` as the conjunction of
the side conditions of the paper rule corresponding to `ev` (e.g. for
`EvMutBorrow loan p sv`: `loan ∉ dom(Ω#.loans)`, `Ω#(p) = some v`,
`⊥, loan^{s,m} ∉ v`). Define `Step#(ev, Ω#, Ω#') : Prop` as the
single-step reduction witnessed by `ev`.

### 4.2 Per-event correspondence lemma

```
lemma stepEvent_sound :
  ∀ (ev : Event) (st st' : SymState) (Ω# : LLBCState),
    ⟦st⟧ = Ω# →
    Replay.stepEvent st ev = .ok st' →
    ∃ Ω#',
      Valid(ev, Ω#) ∧
      Step#(ev, Ω#, Ω#') ∧
      ⟦st'⟧ = Ω#'
```

In words: if the replayer accepts an event in a state that represents
`Ω#`, then there is a valid LLBC# step from `Ω#` to some `Ω#'` whose
representation is the replayer's new state.

This lemma is proved by case analysis on `ev`, mirroring the cert ↔
rule table of §2.3. Each case reduces to (1) reading off the side
conditions the replayer already checked, and (2) constructing the LLBC#
step witness. The cases for `EvJoin` and `EvLoopInv` require the
auxiliary fact that the replayer's pragmatic ≤ check (`symExprBeq` +
`isFreshSym`) implies the existence of a derivation in the full ≤
algebra — this is the most technical part of the proof.

### 4.3 Per-function soundness theorem

```
theorem replayFun_sound :
  ∀ (f : FunCert) (trace : CheckedTrace),
    Replay.replayFun f.signature.numLocals f = .ok trace →
    ∃ Ω#_in Ω#_out,
      borrow_checks# (signatureOf f) ∧                    -- paper Fig. 10
      Initial(Ω#_in, f.signature) ∧
      Ω#_in ⟶_#* Ω#_out ∧
      Final(Ω#_out, f.signature, trace.finalState)
```

In words: a successfully-replayed `FunCert` yields a valid LLBC#
derivation from a signature-compatible initial state to a final state
that matches the cert's `finalState` snapshot. `borrow_checks#` is
the paper's borrow-checking predicate (Fig. 10).

This follows from `stepEvent_sound` by induction on the events array,
plus a `replayFun_post` lemma showing that the exit check
("no `.direct` loan live at exit") matches the paper's `Ω#_1 =
A_sig(ρ), x→⊥, …, xret→v_out` final-state shape.

### 4.4 Crate-level soundness corollary

```
theorem replayCrate_implies_borrow_checks :
  ∀ (cc : CrateCert),
    Replay.replayCrate cc = .ok _ →
    ∀ f ∈ cc.functions, borrow_checks# (signatureOf f)
```

Combined with the paper's **Theorem 4.1** (LLBC# borrow-checking
implies safe LLBC execution) and **Theorem 3.4** (LLBC ↔ PL forward
simulation under step-indexing), we obtain the **end-to-end safety
guarantee**:

```
corollary cert_implies_pl_safety :
  ∀ (cc : CrateCert) (f : FunCert),
    Replay.replayCrate cc = .ok _ →
    f ∈ cc.functions →
    ∀ (Ω_pl : PLState) (n : ℕ),
      Initial_pl(Ω_pl, f.signature) →
      ¬ (Ω_pl ⊢ f.body ⟶_pl^n stuck)
```

i.e. a cert that passes `aeneas-lean-checker` is a witness that the
function's PL execution is safe (no use-after-free, no
out-of-bounds-loan, no double-free).

### 4.5 Subset and limitations

The soundness theorem holds for the **direct-borrow subset** the
replayer currently models. Concretely:

* `EvProj` is excluded (the replayer rejects it). When projection
  support lands, the lemma `stepEvent_sound` must be extended.
* The `EvJoin` pragmatic check is sound only for cert join witnesses
  that the OCaml interpreter actually produces. A *malicious* cert
  could exhibit a "fresh-sym" placeholder that doesn't correspond to
  any real join derivation. The proof discharges this by assuming the
  cert is produced by the OCaml interpreter (i.e., we trust
  `CertGen.ml` as a *trusted base*).
* The replayer's branch-dedupe (M9.5x) and loop-leak tolerance
  (M9.5aa) widen the accepted cert language. The proof must show that
  every accepted cert still corresponds to an LLBC# derivation — for
  branch-dedupe this is immediate (the redundant ends are paper
  no-ops); for loop-leak tolerance it requires invoking the loop's
  region abstraction to discharge the residual loans.

### 4.6 What the proof will and will not establish

| Established by the Lean proof                                        | Trusted base                                  |
|-----------------------------------------------------------------------|-----------------------------------------------|
| Replayer accepts cert → LLBC# borrow-checking derivation exists       | OCaml `CertGen.ml` emits well-formed certs    |
| LLBC# borrow-checking → PL-safe (via paper's theorems, ported to Lean) | Paper's proofs of Thm 3.1, 3.3, 4.1, 4.2     |
| Soundness composes across the crate's call graph                     | Trait-resolution / module-system soundness    |
| Translator preserves observable behaviour (separate theorem)          | The Lean elaborator / kernel                  |

A separate "translator soundness" theorem (out of scope for this
document) will say: the pure Lean function emitted by
`AeneasCheck.Translate` is functionally equivalent to the LLBC#
forward semantics of the source. That theorem is independent of, and
strictly downstream of, the cert-soundness theorem sketched here.

---

## 5. Roadmap

To go from "sketch" to "Lean proof", the following are required, in
order:

1. **Formalise `LLBCState` and `⟶_#`.** A faithful Lean port of paper
   Figs. 3, 7–9 (LLBC and LLBC# reduction rules). This is the bulk of
   the work; ~5kLOC estimated.
2. **Define `⟦·⟧ : SymState → LLBCState`.** Straightforward once
   `LLBCState` exists.
3. **Prove `stepEvent_sound`.** Case analysis, ~20 cases.
4. **Prove the join lemma.** The hardest case: show that the
   replayer's pragmatic ≤ check implies the existence of a derivation
   in the full Fig. 11 algebra.
5. **Prove `replayFun_sound`.** Induction over events.
6. **Port paper Theorems 3.1, 3.3, 4.1, 4.2 to Lean.** This is mostly
   transcription; the proofs in the paper's Appendix A/B should
   carry over modulo notational adaptation.
7. **Compose.** Discharge the crate-level corollary.

Steps 1–5 are independent of the OCaml side; step 6 is independent of
the cert format. Step 7 ties them together.

The current codebase satisfies the *operational* preconditions of the
theorem: 89/89 cert fixtures pass, all three gates green. The
soundness proof itself lives in a yet-to-be-created
`AeneasCheck/Theorems/` namespace.
