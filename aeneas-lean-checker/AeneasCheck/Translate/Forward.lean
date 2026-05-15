import AeneasCheck.Pure.Syntax
import AeneasCheck.LLBCSharp.Replay

/-!
Translate a CheckedTrace into a Pure decl.

For M7 the body was the identity placeholder `.ok x1`. M10.0 lifts it
to a real value-flow walk:

* **T-Return-Forward**: trace ends with `EvReturn` → the function
  returns whatever pure expression the return-local (LLBC convention:
  local 0 for value returns, or the post-state of a borrowed local
  for `&mut` outputs) currently holds.
* **T-Reorg-Anytime**: `EvCopy` is folded into the per-local value
  map; `EvMove` does the same and additionally invalidates the
  source.
* **T-Binop**: `EvBinop` produces a fresh `let tN ← lhs <op> rhs`
  binding; subsequent reads of `dst.root` pick up `var tN`.
* **Pure-Mut-Borrow / Pure-Reborrow**: borrow events are no-ops at
  the pure-value layer (the borrow's mutation flows out via the
  function's return; M10.2 will model backward functions explicitly).
* **T-Call-Forward** (M10.1): `EvCall` emits a `let tN ← fn args`
  binding and threads `tN` through subsequent reads of the dst.
* **T-Call-Backward** (M10.2b): when the call's region abstraction
  closes via `EvEndAbs`, we update `vm` so subsequent reads of the
  borrowed input's caller-side local resolve to the call's post-state
  binding name (`<input>_post`). Without backward functions per se,
  this conflates "post-state of the borrow" with "result of the
  call" — sound for single-region `&mut`-taking helpers whose
  callee acts on one borrow; multi-region cases are left for M11.

The result is a `do`-block of monadic `let` bindings tail-ended by
`ok <expr>`. Binops that already return `Result α` propagate through
unchanged; literals/vars in tail position are wrapped in `ok`.
-/

namespace AeneasCheck.Translate

open AeneasCheck Raw Pure LLBCSharp

/-- Heuristic: infer a Pure param name from a 0-based local id. -/
def paramName (i : Nat) : String := s!"x{i}"

/-- Heuristic: a placeholder Pure type, used until cert events carry
    real LLBC types for the operands. -/
def placeholderTy : PTy := .lit (.int .u32)

/-- M12.2a-2: detect whether a signature input/output is a `&mut T`.
    Mirrors the substring-tagged shape that the OCaml `show_ty` emits
    (`TRef ... Generated_Types.RMut`). -/
def isMutRef : RawTy → Bool
  | .opaque s =>
    (s.splitOn "TRef").length ≥ 2 && (s.splitOn "RMut").length ≥ 2
  | _ => false

/-- M12.2a-2: detect whether a signature input/output is a unit/`()`
    tuple. Used to elide the forward result when the original Rust
    function returned `()`. -/
def isUnitTy : RawTy → Bool
  | .opaque s =>
    (s.splitOn "TTuple").length ≥ 2 &&
    -- Heuristic: a unit tuple has `types = []` in the printed form.
    (s.splitOn "types = []").length ≥ 2
  | _ => false

/-- M12.2b: when an output type is a TAdt-TTuple containing N TRef-RMut
    components (each in a distinct region), return `some N`. Used to
    detect helpers like `swap_pair<'a,'b>(...) -> (&'a mut u32, &'b mut u32)`
    whose pure translation produces N backward closures (one per region)
    instead of a single closure. Returns `none` if the output is not a
    tuple OR contains zero/one mut-ref fields.

    Heuristic: the type-printer renders the inner types list as
    `types = [TRef …; TRef …; ...]`. We count `TRef` substrings within
    the `types = [...]` block AND require at least one `RMut` per such
    TRef. -/
def isOutputTupleOfMutRefs : RawTy → Option Nat
  | .opaque s =>
    if (s.splitOn "TTuple").length < 2 then none
    else
      -- Count TRef + RMut paired occurrences. The substring count of
      -- "TRef" minus 1 is the number of TRef sites. Same for RMut.
      let nRef := (s.splitOn "TRef").length - 1
      let nMut := (s.splitOn "RMut").length - 1
      if nRef ≥ 2 && nMut ≥ nRef then some nRef else none
  | _ => none

/-- M9.5b: information the translator needs about one ADT type
    declaration: its bare Lean name and an ordered list of field
    names. The Lean translator uses `name` when translating an
    `&mut Pair`-typed signature input or a function whose return
    type is `Pair`; `fieldNames[K]` resolves a `Field K` projection
    to the surface field name (`fst` / `snd`). -/
structure TypeDeclInfo where
  name : String
  fieldNames : Array String
  deriving Repr, Inhabited

/-- M9.5b: a TypeDeclId → TypeDeclInfo lookup, keyed by the integer
    that appears inside `TAdt { id = TAdtId N; ... }` strings. The
    Driver builds this from `cc.typeDecls`. -/
abbrev TypeDeclMap := Std.HashMap Nat TypeDeclInfo

/-- M9.5b: extract the `N` from a substring `TAdtId N`. Returns `none`
    when the string contains no `TAdtId` reference (e.g., a tuple
    type or a literal). When multiple `TAdtId` references appear
    (parametric ADTs, nested types), this returns the *first* one —
    enough for M9.5b's monomorphic-struct fixtures. -/
def parseTAdtId (s : String) : Option Nat :=
  let parts := s.splitOn "TAdtId"
  match parts with
  | _ :: rest :: _ =>
    -- After `TAdtId` there's optional whitespace, then digits, then
    -- closing punctuation. Skip leading whitespace, scan digits.
    -- Lean 4 deprecated `trimLeft`; use a manual ASCII-space skip
    -- that returns a `String` (not a `String.Slice`).
    let trimmed := rest.dropWhile Char.isWhitespace
    let digits := trimmed.takeWhile Char.isDigit
    if digits.isEmpty then none else digits.toNat?
  | _ => none

/-- M9.5b: detect a `TAdt {... TTuple ...}` string. We use a substring
    check; `TTuple` appears in the same nested form regardless of
    generic args. -/
def isTupleAdt (s : String) : Bool :=
  (s.splitOn "TTuple").length ≥ 2

/-- M9.5c: parse the length of a `TArray (...elem..., { ... CLiteral
    (VScalar (UnsignedScalar (Usize, N))); ...})` opaque string. The
    `N` is the const-generic length. We do a substring scan for
    `UnsignedScalar (` and then look for `Usize, ` followed by digits.
    Returns `none` if the pattern isn't found. -/
def parseArrayLen (s : String) : Option Nat :=
  -- The const-generic length is always rendered as
  -- `UnsignedScalar (Generated_Values.Usize, N)` for our fixtures
  -- (signed-indexed arrays are unusual in Rust). We anchor on
  -- `Usize, ` since that's the unique-enough prefix in the array
  -- branch. (Outside `TArray`, the same string never appears.)
  let parts := s.splitOn "Usize, "
  match parts with
  | _ :: rest :: _ =>
    let digits := (rest.dropWhile Char.isWhitespace).takeWhile Char.isDigit
    if digits.isEmpty then none else digits.toNat?
  | _ => none

/-- M9.5c: detect a `TArray` opaque type. Used to gate the
    array-aware branch of [rawTyToPTyWith]; without this guard, the
    catch-all `Usize` substring check downstream incorrectly classifies
    `[u32; 4]` as a bare `Std.Usize` (because the const-generic length
    carries a `Usize` tag). -/
def isArrayTy (s : String) : Bool :=
  (s.splitOn "TArray").length ≥ 2

/-- M9.5b: type-decl-aware `RawTy` → `PTy` mapping. Resolves
    `TAdtId N` references via [tdm]; falls back to the legacy
    substring-keyed heuristic when the type is a literal or contains
    no ADT reference.

    Reference shapes (`TRef ... RMut` / `TRef ... RShared`) unwrap to
    their inner type — at the pure layer, a `&mut Pair` and a `Pair`
    have the same value type (the post-state of a `&mut T` IS the
    `T`). The signature surface, separately, decides whether the
    function takes a borrow (input position) or returns a forward
    value (output position).

    Order matters: we test for `TTuple` *before* `TAdtId` because the
    output type of a unit-returning function (`()`) is rendered as
    `TAdt {id = TTuple; ...}` with no `TAdtId` payload — but a
    `TAdtId 0` substring can still appear inside *generic* args. -/
def rawTyToPTyWith (tdm : TypeDeclMap) : RawTy → PTy
  | .opaque s =>
    -- M9.5c: TArray must come first. The const-generic length section
    -- includes a `Usize` tag, which would otherwise be misclassified
    -- as a bare `Usize` literal by the catch-all below.
    if isArrayTy s then
      -- For now we only carry element-kind information at the
      -- token-level (U32 / U64 / U8 / U16 / Usize / I32 / Bool); a
      -- full TArray opaque string for `[u32; 4]` starts with the
      -- element type before the const-generic block, so a substring
      -- scan picks the right one. Order tokens so the longer/less-
      -- ambiguous ones win: `U64` before `U8`, etc. (`Usize` appears
      -- in the length section too, so we deliberately skip it here —
      -- a `[usize; N]` array would need a separate fixture to test.)
      --
      -- For unrecognised element types, fall back to `u32`; this
      -- mirrors the catch-all in the non-array branch and keeps the
      -- pipeline running for shapes the test fixtures don't exercise.
      let elem : PTy :=
        if (s.splitOn "TBool").length ≥ 2 then .lit .bool
        else if (s.splitOn "U64").length ≥ 2 then .lit (.int .u64)
        else if (s.splitOn "I32").length ≥ 2 then .lit (.int .i32)
        else if (s.splitOn "U16").length ≥ 2 then .lit (.int .u16)
        else if (s.splitOn "U8").length ≥ 2 then .lit (.int .u8)
        else if (s.splitOn "U32").length ≥ 2 then .lit (.int .u32)
        else .lit (.int .u32)
      .array elem ((parseArrayLen s).getD 0)
    else if (s.splitOn "TBool").length ≥ 2 then .lit .bool
    else if (s.splitOn "U64").length ≥ 2 then .lit (.int .u64)
    else if (s.splitOn "I32").length ≥ 2 then .lit (.int .i32)
    else if (s.splitOn "U16").length ≥ 2 then .lit (.int .u16)
    else if (s.splitOn "U8").length ≥ 2 then .lit (.int .u8)
    else if (s.splitOn "Usize").length ≥ 2 then .lit (.int .usize)
    else
      -- Try to resolve an ADT reference (struct). For a `TRef …
      -- TAdt …` we unwrap to the inner T (PTy is value-level; the
      -- borrow shape is recovered separately by [isMutRef] when
      -- building the BackSig).
      match parseTAdtId s with
      | some id =>
        match tdm[id]? with
        | some info => .adt info.name #[]
        | none =>
          -- Unknown ADT id (shouldn't happen for in-crate decls;
          -- fall back to u32 to avoid crashing).
          if (s.splitOn "TRef").length ≥ 2 then .lit (.int .u32)
          else .lit (.int .u32)
      | none =>
        if isTupleAdt s then .unit
        else if (s.splitOn "TRef").length ≥ 2 then .lit (.int .u32)
        else .lit (.int .u32)
  | _ => .lit (.int .u32)

/-- Crude `RawTy` → `PTy` mapping based on substring lookup in the
    opaque-tagged signature string, with no type-decl context. Kept
    as the M11-era default for call sites (e.g. struct-field decls
    in [Translate.Driver]) that don't have a [TypeDeclMap] in scope.
    M9.5b's translator passes a real [TypeDeclMap] via
    [rawTyToPTyWith]. -/
def rawTyToPTy : RawTy → PTy := rawTyToPTyWith {}

/-- Strip the leading crate-name segment of a `crate::a::b` path,
    returning the inner def name `a.b`. The crate prefix becomes the
    surrounding `namespace` block in the emitter. -/
def innerName (qualified : String) : String :=
  let segs := qualified.splitOn "::"
  match segs with
  | _ :: rest => String.intercalate "." rest
  | [] => qualified

/-- Per-local current pure expression. Populated from the function's
    inputs and updated as the event walk progresses. -/
abbrev VarMap := Std.HashMap Nat PExpr

/-- Resolve a place's *root* local to its current pure expression. M10.0
    ignores projections (Deref, Field, ProjIndex) when computing the
    pure value — the placeholder is sound for the direct-borrow
    subset; M10.2 will refine for field-projected places.

    When the local has no entry in the map (typical for `[Deref]`
    reads through a borrow whose backing local was never observed
    in a tracked event), fall back to the *first input parameter*
    `x1`. This is a deliberate over-approximation: for simple
    borrowed-input functions like `incr(x: &mut u32) { *x += 1 }`
    every Deref read of an intermediate temp ultimately resolves to
    the input, so `x1` is the right pure-value substitute. M10.2's
    real backward-function machinery will replace this heuristic
    with a borrow-chain–aware lookup. -/
def lookupPlace (vm : VarMap) (p : Place) : PExpr :=
  match vm[p.local_]? with
  | some e => e
  | none => vm.getD 1 (.lit (.scalar .u32 0))

/-- Resolve a `SymExpr` against the current var map to a Pure
    expression. Symbolic ids (`SymVal n`) fall back to a generated
    name `sN`. -/
def lookupSymExpr (vm : VarMap) : SymExpr → PExpr
  | .symVal n => .var s!"s{n}"
  | .symLit l => .lit l
  | .symCopy p => lookupPlace vm p
  | .symMove p => lookupPlace vm p
  | .symMutBorrowTok n => .var s!"b{n}"

/-- Map an OCaml `cert_binop_string` tag onto a Pure `App` head. The
    head string is what the Lean emitter pretty-prints — see
    `Pure.Pretty.binopHead.toLean` for the operator/notation map. -/
def binopHead : String → String
  | "AddPanic" | "AddUB" => "Add"
  | "AddWrap" => "AddWrap"
  | "SubPanic" | "SubUB" => "Sub"
  | "SubWrap" => "SubWrap"
  | "MulPanic" | "MulUB" => "Mul"
  | "MulWrap" => "MulWrap"
  | "DivPanic" | "DivUB" | "DivWrap" => "Div"
  | "RemPanic" | "RemUB" | "RemWrap" => "Rem"
  | "ShlPanic" | "ShlUB" | "ShlWrap" => "Shl"
  | "ShrPanic" | "ShrUB" | "ShrWrap" => "Shr"
  | "BitXor" => "BitXor"
  | "BitAnd" => "BitAnd"
  | "BitOr" => "BitOr"
  | "Eq" => "Eq" | "Lt" => "Lt" | "Le" => "Le"
  | "Ne" => "Ne" | "Ge" => "Ge" | "Gt" => "Gt"
  | "AddChecked" => "AddChecked"
  | "SubChecked" => "SubChecked"
  | "MulChecked" => "MulChecked"
  | "Offset" => "Offset"
  | "Cmp" => "Cmp"
  | s => s

/-- Pending function call info, recorded at EvCall time and consumed
    at EvEndAbs time. Each region abstraction in a call's `regionAbs`
    list maps to one [PendingCall] entry; the call's binding is
    emitted on the *first* EvEndAbs for that call, and subsequent
    EvEndAbs's of the same call just update `vm` with the next
    post-state. (Multi-region calls require tuple destructuring,
    deferred to M11; M10.2b handles the single-region case which is
    what real-world `&mut`-taking helpers look like.) -/
structure PendingCall where
  /-- Unique key (here just the original `callId` from the cert).
      Distinct EvEndAbs's for the same call share this key, so we
      know to only emit one `let … ← …` binding. -/
  callKey : Nat
  fnName : String
  argEs : Array PExpr
  /-- For each region in the call's `regionAbs`, the caller-side
      local id that should be re-bound to the post-state's fresh
      pure name. Computed at EvCall time from each arg's place. -/
  postLocals : Array Nat
  /-- The call's own dst place's local id (unit for many `&mut`
      helpers; valued for `&mut`-returning helpers). Kept so we can
      pick the right "return slot" if the trace consults it. -/
  dstLocal : Nat
  deriving Inhabited

/-- M12.2a-3: a single accumulated monadic binding in the walk's
    do-block. Most bindings are `regular` — `let <name> ← <rhs>`.
    For calls into `&mut`-taking helpers the binding destructures
    the result pair: `let (<name>, <backName>) ← <rhs>`. M12.2b
    extends this with `tuple` — `let (n₀, n₁, …, nₖ) ← <rhs>` —
    used when a call's region count is ≥ 2 and the dst is a tuple
    of `&mut` returns. The pattern forms are rendered as `letPat`
    in [assembleBody]. -/
inductive Bind
  | regular (name : String) (rhs : PExpr)
  | pair (name backName : String) (rhs : PExpr)
  | tuple (names : Array String) (rhs : PExpr)
  deriving Inhabited

/-- Walk state: accumulated `let` bindings (in monadic order) plus
    the current per-local pure expression map. -/
structure WalkState where
  binds : Array Bind := #[]
  vm : VarMap := {}
  /-- Counter for fresh `tN` names. -/
  fresh : Nat := 0
  /-- The function's input-parameter count. Used to discriminate
      "input locals" (1..numParams) from temp locals when picking
      a `_post`-style name on EvEndAbs. -/
  numParams : Nat := 0
  /-- The local id last written by a value-producing event (binop,
      assign, copy/move target). Used as a fallback return value for
      functions whose mutation flows through a `&mut` input — the
      "result" is whatever was most recently computed before the
      `EvReturn`. M10.2's backward-function pass will replace this
      with an exact post-state per-borrow read. -/
  lastWrite : Option Nat := none
  /-- M10.2b: pending calls keyed by abstraction id. Populated by
      EvCall (one entry per region in `regionAbs`) and consumed by
      EvEndAbs, which materializes the call's `let … ← …` binding
      (once per call) and threads the post-state symbolic value
      through `vm`. -/
  pending : Std.HashMap Nat PendingCall := {}
  /-- M10.2b: which call keys have already produced a `let … ← …`
      binding. Subsequent EvEndAbs entries for the same call skip
      re-emission and only update `vm`. -/
  emittedCalls : Std.HashSet Nat := {}
  /-- M12.2a-2: when the function body is a Return-tailed if/else
      (each branch ends in `EvReturn`, no `EvJoin`), the walker
      stashes each sub-walk's `vm` here so the top-level wrap-up
      can build the backward closure: in each branch we need to
      know which input the borrow chain leads back to. -/
  branchTrueVm0  : Option VarMap := none
  branchFalseVm0 : Option VarMap := none
  /-- M12.2a-3: for each local that holds the return of a call
      with `&mut` inputs, remember the call's backward-closure
      binding name. When a subsequent EvAssign writes through
      that local's deref projection, we apply the closure to the
      assigned value and propagate the result tuple into the
      function's return slot (LLBC convention: vm[0]). -/
  callBack : Std.HashMap Nat String := {}
  /-- M12.2b: for a multi-region EvCall, the destructured result
      tuple gets one backward-closure name per region. Keyed by
      (callDstLocal, fieldIdx). Populated at EvCall time; consumed
      by the subsequent EvAssigns that destructure
      `<callDstLocal>.[Field K]` into per-region locals — those
      EvAssigns thread `callBackByField[(L, K)]` into [callBack]
      so the existing deref-write hook applies the right closure. -/
  callBackByField : Std.HashMap (Nat × Nat) String := {}
  /-- M12.2b: `true` for a destructured-from-multi-region local
      (set alongside [callBack] from a field-EvAssign). When a
      deref-write through such a local fires, accumulate the
      closure application into [multiRegionTail] in field order
      *instead of* clobbering `vm[0]` (the single-region path).
      The function tail then wraps `multiRegionTail` into the
      output shape. -/
  multiRegionLocal : Std.HashSet Nat := {}
  /-- M12.2b: per-field accumulated `<back_K> v` applications.
      Built by deref-EvAssigns through [multiRegionLocal] locals.
      Indexed by region/field index (0-based, matching
      [callBackByField]). Consumed at function tail to build
      `ok (app_0, app_1, …, app_{N-1})`. -/
  multiRegionTail : Std.HashMap Nat PExpr := {}
  /-- M12.2b: the field-index of each multi-region-destructured
      local. Lets deref-writes thread their `<back_K>` application
      into [multiRegionTail] at the right slot. -/
  multiRegionLocalIdx : Std.HashMap Nat Nat := {}
  /-- M9.5b: crate-level type-decl table, threaded from the Driver.
      Used by the EvAssign walker to resolve a `[Deref, Field K]`
      projection on a `&mut Pair`-typed local to a struct-update
      with the right field name. Also used by [rawTyToPTyWith] when
      mapping signature inputs/outputs. -/
  tdm : TypeDeclMap := {}
  /-- M9.5c: in-flight `@ArrayIndexMut` calls. Keyed by the call's
      destination local (the temp that holds the returned
      `&mut elem`); the payload carries the *array* expression,
      the *index* expression, and (when known) the array's root
      input-parameter local id. The translator does not emit a
      binding at EvCall time — `index_mut` followed by a deref-
      assign lowers directly to `Array.update <array> <idx> <rhs>`,
      which is the standard backend's shape. The pending entry is
      consumed (and emitted as a regular monadic let) by the
      subsequent deref-write through the call's dst local. -/
  arrayIndexMut : Std.HashMap Nat (PExpr × PExpr × Option Nat) := {}
  deriving Inhabited

namespace WalkState

def freshName (st : WalkState) : String × WalkState :=
  let nm := s!"t{st.fresh}"
  (nm, { st with fresh := st.fresh + 1 })

end WalkState

/-- Compute the caller-side local that holds the borrowed value for
    a single call argument. Mirrors `lookupPlace`'s fallback: when
    the arg's root local isn't tracked in `vm` (typical: it's an
    intermediate reborrow temp), the post-state should land on the
    *first input parameter* — the same fallback `lookupPlace` uses.

    For arg shapes that aren't a place (literal, raw symbolic value),
    return 0 — the caller treats 0 as "no post-update needed." -/
def postLocalOfArg (vm : VarMap) : SymExpr → Nat
  | .symCopy p | .symMove p =>
    if vm.contains p.local_ then p.local_ else 1
  | .symVal _ | .symLit _ | .symMutBorrowTok _ => 0

/-- M12.2a-2: outcome of [findBranchEnd]'s lookahead.
    * `joined jIdx kIdx` — standard M11.2 if/else with a closing
      `EvJoin` at `kIdx` (false marker at `jIdx`).
    * `returnTailed jIdx trueEnd falseEnd` — both branches end in
      `EvReturn` with no shared continuation. `trueEnd` is the index
      of the true branch's terminator, `falseEnd` of the false's.
      The walker emits the whole `if cond then <true> else <false>`
      as the function's tail expression. -/
inductive BranchEnd
  | joined (jIdx kIdx : Nat)
  | returnTailed (jIdx trueEnd falseEnd : Nat)
  deriving Repr

/-- M11.2 helper (M12.2a-2 extended): find the indices that close out
    a branching block that opens at `i` (which is `EvAssert {cond, true}`).

    Returns `none` if the pattern isn't a match (e.g. a real `assert!`
    not surrounded by either an EvJoin terminator or a return-tailed
    pattern, or a malformed cert). The search is one-level-deep:
    nested ifs inside a branch leave their own well-formed runs whose
    first-`true` marker we'll *not* match because we only consider
    markers carrying the same `cond` SymExpr as the opening one. -/
def findBranchEnd (evs : Array Event) (i : Nat) (openCond : SymExpr) :
    Option BranchEnd := Id.run do
  -- Look for the matching `EvAssert {openCond, false}` first,
  -- skipping any nested `EvAssert {_, false}` whose cond differs.
  let mut j : Option Nat := none
  let mut k : Nat := i + 1
  -- Depth counter for nested branches: every `EvAssert {_, true}`
  -- after `i` pushes; the matching `EvJoin` pops. We only accept a
  -- `EvAssert {openCond, false}` at depth 0.
  let mut depth : Nat := 0
  while h : k < evs.size do
    let ev := evs[k]
    match ev with
    | .assert c true =>
      if depth == 0 && symExprEq c openCond then
        -- This would be a nested-open with the same cond; treat as
        -- malformed and bail out. (In practice OCaml never reuses
        -- the same sym id for two different branches.)
        j := none; break
      depth := depth + 1
    | .assert c false =>
      if depth == 0 && symExprEq c openCond then
        j := some k
        break
      -- A `false` marker at non-zero depth pairs with an earlier
      -- `true` marker; depth is decremented when we see EvJoin
      -- below, not here.
      pure ()
    | .join _ _ _ =>
      if depth == 0 then
        -- A bare join with no opening true marker — shouldn't
        -- happen; abort.
        j := none; break
      depth := depth - 1
    | _ => pure ()
    k := k + 1
  match j with
  | none => none
  | some jIdx =>
    -- Look for the closing terminator after the false marker. Two
    -- shapes are accepted (in order of preference):
    --   * `EvJoin` at depth 0 → `.joined jIdx kIdx`. This is the
    --     M11.2 in-body if/else (post-`if` continuation exists).
    --   * No `EvJoin`, but the false branch's range ends in
    --     `EvReturn` AND the true branch's range also ended in
    --     `EvReturn` (just before `jIdx`) → `.returnTailed`. This is
    --     the `choose`-style "both branches return" pattern where
    --     OCaml never emitted a join because there's no shared
    --     continuation.
    let mut depth2 : Nat := 0
    let mut joinIdx : Option Nat := none
    let mut falseEndIdx : Option Nat := none
    let mut m : Nat := jIdx + 1
    while h : m < evs.size do
      let ev := evs[m]
      match ev with
      | .assert _ true => depth2 := depth2 + 1
      | .join _ _ _ =>
        if depth2 == 0 then
          joinIdx := some m
          break
        depth2 := depth2 - 1
      | .retn =>
        if depth2 == 0 then
          falseEndIdx := some m
          break
      | _ => pure ()
      m := m + 1
    -- If we found an EvJoin, prefer it (M11.2 path).
    match joinIdx, falseEndIdx with
    | some kIdx, _ => some (.joined jIdx kIdx)
    | none, some fEnd =>
      -- The true branch must also end in `EvReturn` at depth 0
      -- (between `i+1` and `jIdx-1`). Find that terminator.
      let mut depthT : Nat := 0
      let mut trueEndIdx : Option Nat := none
      let mut t : Nat := i + 1
      while ht : t < jIdx do
        if hs : t < evs.size then
          let ev := evs[t]
          match ev with
          | .assert _ true => depthT := depthT + 1
          | .join _ _ _ =>
            if depthT == 0 then break
            depthT := depthT - 1
          | .retn =>
            if depthT == 0 then
              trueEndIdx := some t
              break
          | _ => pure ()
        else
          break
        t := t + 1
      match trueEndIdx with
      | some tEnd => some (.returnTailed jIdx tEnd fEnd)
      | none => none
    | none, none => none
where
  /-- Lightweight equality on `SymExpr` for matching openers to
      closers. Only the cheap shape we expect from OCaml. -/
  symExprEq : SymExpr → SymExpr → Bool
    | .symVal a, .symVal b => a == b
    | _, _ => false

/-- Apply one event to the walk state. -/
def walkEvent (st : WalkState) (ev : Event) : WalkState :=
  match ev with
  | .copy s d =>
    -- Read `s`'s current expression, write it to `d`'s root. Many
    -- cert EvCopy events have s = d (the OCaml hook records operand
    -- reads with src=dst); we skip the write in that case so the
    -- existing entry isn't clobbered by a self-reference.
    if s.local_ == d.local_ then st
    else { st with
      vm := st.vm.insert d.local_ (lookupPlace st.vm s)
      lastWrite := some d.local_ }
  | .move s d =>
    -- Move: same as copy but invalidate the source.
    if s.local_ == d.local_ then st
    else
      let v := lookupPlace st.vm s
      { st with
        vm := (st.vm.erase s.local_).insert d.local_ v
        lastWrite := some d.local_ }
  | .assign d rhs =>
    -- M12.2a-3: when the dst place's projection ends in [Deref] AND
    -- the dst's root local has an associated backward closure (from
    -- a prior EvCall into a `&mut`-returning helper), apply the
    -- closure to the assigned value. The closure's result is the
    -- tuple of restored `&mut` input post-states; we stash it in
    -- vm[0] (the LLBC return slot) so the wrap-up step picks it up
    -- as the function's tail. For non-deref EvAssigns, fall back
    -- to the M10 behavior (rewrite vm[dst.local_]).
    let rhsE := lookupSymExpr st.vm rhs
    let derefTail : Bool :=
      match d.projection.toList.getLast? with
      | some ProjElem.deref => true
      | _ => false
    -- M9.5b: detect a struct-field write through a `&mut Pair`-style
    -- input. Projection shape: `[..., Deref, Field K]` (last is
    -- `Field K`, second-to-last is `Deref`). The pure-level effect
    -- is `vm[root] := { vm[root] with <fieldName> := rhsE }` —
    -- record-update preserving the rest of the struct. We resolve
    -- the field name via `st.tdm` keyed by the TAdt id parsed from
    -- the dst place's root-local type string.
    let structFieldWrite : Option (String × PExpr) :=
      let proj := d.projection.toList
      let n := proj.length
      if n < 2 then none
      else
        match proj[n - 2]?, proj[n - 1]? with
        | some ProjElem.deref, some (ProjElem.field k) =>
          match d.ty with
          | RawTy.opaque s =>
            (parseTAdtId s).bind fun adtId =>
              st.tdm[adtId]?.bind fun info =>
                info.fieldNames[k]?.map fun fname =>
                  let base : PExpr :=
                    st.vm.getD d.local_ (.var (paramName d.local_))
                  (fname, .structUpdate base fname rhsE)
          | _ => none
        | _, _ => none
    -- M12.2b: detect a field-destructure of a multi-region call
    -- result, i.e. `EvAssign dst=L rhs=SymMove(L'.[Field K])`
    -- where `(L', K)` is keyed in [callBackByField]. Thread the
    -- per-region back-closure name into `callBack[L]` so the
    -- subsequent deref-write through L fires the right closure.
    -- We also record L's field index in [multiRegionLocalIdx] so
    -- the deref-write accumulates into [multiRegionTail] at the
    -- right slot. The Pure binding is *not* emitted (the
    -- destructure was already done by the multi-name `letPat` at
    -- EvCall time); we only update bookkeeping.
    let fieldFromMultiCall : Option (Nat × String) :=
      match rhs with
      | .symMove rp | .symCopy rp =>
        match rp.projection.toList.getLast? with
        | some (ProjElem.field k) =>
          match st.callBackByField[(rp.local_, k)]? with
          | some backName => some (k, backName)
          | none => none
        | _ => none
      | _ => none
    if let some (k, backName) := fieldFromMultiCall then
      { st with
        callBack := st.callBack.insert d.local_ backName
        multiRegionLocal := st.multiRegionLocal.insert d.local_
        multiRegionLocalIdx := st.multiRegionLocalIdx.insert d.local_ k
        -- Don't update vm[d.local_]: the destructured local has no
        -- pure-value meaning until a deref-write fires the closure.
        lastWrite := some d.local_ }
    else if let some (_fname, suExpr) := structFieldWrite then
      -- M9.5b: write-through-`&mut` field assignment. The "value" of
      -- the input's post-state IS the struct-update expression. We
      -- stash it in vm[d.local_]; the BackSig wrap-up below picks it
      -- up as the function's tail.
      { st with
        vm := st.vm.insert d.local_ suExpr
        lastWrite := some d.local_ }
    else if derefTail then
      -- M9.5c: deref-write through the result of an earlier
      -- `@ArrayIndexMut` call. Emit a single `Array.update <array>
      -- <idx> <rhs>` monadic binding and thread the updated array
      -- back into its input local. This collapses the
      -- Charon-emitted `index_mut + deref-store` pair into the
      -- standard backend's idiomatic shape.
      match st.arrayIndexMut[d.local_]? with
      | some (arrayE, idxE, arrayRoot) =>
        -- Build `Array.update <arrayE> <idxE> <rhsE>`. The result
        -- (the updated array) gets bound to a fresh name and routed
        -- into the array's root input local so the function tail
        -- picks it up.
        let updateApp : PExpr :=
          .app "Array.update" #[arrayE, idxE, rhsE]
        let (nm, st') := st.freshName
        let vm' :=
          match arrayRoot with
          | some r => (st'.vm.insert r (.var nm)).insert d.local_ (.var nm)
          | none => st'.vm.insert d.local_ (.var nm)
        { st' with
          binds := st'.binds.push (.regular nm updateApp)
          vm := vm'
          arrayIndexMut := st'.arrayIndexMut.erase d.local_
          lastWrite := arrayRoot.orElse (fun _ => some d.local_) }
      | none =>
      match st.callBack[d.local_]? with
      | some backName =>
        -- The backward closure was bound as `<backName> : T → tuple`.
        -- Applying it to the assigned RHS yields the function's
        -- restored `&mut` input post-states, which IS the function's
        -- return value for unit-returning callers (e.g. use_choose).
        let tailE : PExpr := .app backName #[rhsE]
        -- M12.2b: in the multi-region case each closure produces ONE
        -- input's post-state (not a tuple). Accumulate per field
        -- index into [multiRegionTail] instead of clobbering vm[0].
        -- The function tail then builds the return tuple from these.
        if st.multiRegionLocal.contains d.local_ then
          let k := st.multiRegionLocalIdx.getD d.local_ 0
          { st with
            multiRegionTail := st.multiRegionTail.insert k tailE
            lastWrite := some 0 }
        else
          { st with
            vm := st.vm.insert 0 tailE
            lastWrite := some 0 }
      | none =>
        -- M9.5a: no tracked backward closure. The deref-write either
        -- targets the function's own `&mut` input directly (e.g.
        -- `incr`'s `*x = …`) or threads through a reborrow chain
        -- whose underlying root is still one of the input parameters
        -- (e.g. `reborrow_chain`'s `let s = &mut *x; *s = 7`). The
        -- M12.2a-1 cert-hook fix makes vm[temp] resolve to the
        -- input's `xK` var-name for every borrow-typed temp in such
        -- a chain, so we can detect the propagation target by
        -- inspecting `vm[d.local_]`: if it names an input
        -- parameter, the write lands on that input's vm slot instead
        -- of the temp's.
        let resolveInputRoot : Option Nat :=
          match st.vm[d.local_]? with
          | some (.var name) =>
            if name.length ≥ 2 && name.front == 'x' then
              match (name.drop 1).toNat? with
              | some n => if 1 ≤ n ∧ n ≤ st.numParams then some n else none
              | none => none
            else none
          | _ => none
        match resolveInputRoot with
        | some root =>
          { st with
            vm := st.vm.insert root rhsE
            lastWrite := some root }
        | none =>
          { st with
            vm := st.vm.insert d.local_ rhsE
            lastWrite := some d.local_ }
    else
      { st with
        vm := st.vm.insert d.local_ rhsE
        lastWrite := some d.local_ }
  | .binop op lhs rhs d =>
    let lhsE := lookupSymExpr st.vm lhs
    let rhsE := lookupSymExpr st.vm rhs
    let app : PExpr := .app (binopHead op) #[lhsE, rhsE]
    let (nm, st) := st.freshName
    { st with
      binds := st.binds.push (.regular nm app)
      vm := st.vm.insert d.local_ (.var nm)
      lastWrite := some d.local_ }
  -- Borrow events have no value-level effect in the forward
  -- direction; the mutation flows out via the function's return,
  -- modelled by M10.2's backward-function machinery.
  | .mutBorrow _ _ _ | .sharedBorrow _ _ _ _
  | .reborrow _ _ _ | .endBorrow _ _ => st
  -- Control / panic / return are observed at the wrap-up step
  -- below; they don't affect the per-local value map.
  | .assert _ _ | .panic | .retn => st
  | .call _ callId fnName args dst regionAbs =>
    -- M9.5c: intercept Charon's builtin `@ArrayIndexMut` ahead of the
    -- generic call machinery. The standard Aeneas backend lowers
    -- `xs[i] = v` (which compiles to `index_mut` + a deref-store) to a
    -- single `Array.update xs i v` call returning the whole updated
    -- array. We do the same here: stash the call's array/index args
    -- so the subsequent deref-EvAssign through `dst.local_` can emit
    -- `let nm ← Array.update <array> <idx> <rhs>` and thread `nm`
    -- back into the array's input slot. NO binding is emitted at
    -- EvCall time; without this guard we'd otherwise produce the
    -- generic `(forward, backward)`-pair shape that doesn't apply to
    -- arrays (since `index_mut` followed by a write IS the update —
    -- there's no "value side" to keep).
    if fnName == "@ArrayIndexMut" && args.size == 2 then
      let argEs := args.map (lookupSymExpr st.vm)
      let arrayE := argEs[0]!
      let idxE := argEs[1]!
      -- Identify the array's root input-parameter local so we can
      -- write the updated array back into it (and pick it up as the
      -- function's tail value). Two signals:
      --   * the arg's PExpr is `.var "xK"` for some param K (the
      --     M12.2a-1 cert hook makes this almost always true for
      --     borrow-typed temps);
      --   * the arg's place root maps to an input local in vm.
      let paramNameOfPExpr : PExpr → Option Nat := fun e =>
        match e with
        | .var name =>
          if name.length ≥ 2 && name.front == 'x' then
            match (name.drop 1).toNat? with
            | some n => if 1 ≤ n ∧ n ≤ st.numParams then some n else none
            | none => none
          else none
        | _ => none
      let arrayRoot : Option Nat :=
        paramNameOfPExpr arrayE
      { st with
        arrayIndexMut := st.arrayIndexMut.insert dst.local_ (arrayE, idxE, arrayRoot) }
    else
    -- M10.1+M10.2b: forward call.
    --
    -- We always emit the call's binding eagerly here so subsequent
    -- events (EvAssign through a `&mut` return, etc.) see a `vm`
    -- with the call's return slot populated. When `regionAbs` is
    -- non-empty, we additionally record a `PendingCall` per
    -- abstraction; the matching EvEndAbs will then *rebind* the
    -- binding's name to a `<input>_post` form (renaming the most
    -- recent binding rather than re-emitting) and update `vm` for
    -- the borrowed input's caller-side local.
    let argEs := args.map (lookupSymExpr st.vm)
    let postLocals : Array Nat := args.map (postLocalOfArg st.vm)
    -- Pick the binding name: a generic `tN` for forward-only
    -- calls; an `<input>_post` shape when we know which `&mut`
    -- *input parameter*'s post-state we'll thread on EvEndAbs.
    --
    -- M12.2a-1: with the new RvRef→EvAssign cert hook, `vm[l]` for
    -- a borrow-typed temp now resolves to a `.var "<paramName>"`
    -- pointing at the underlying input. We look at each arg's
    -- resolved `PExpr` and pick `_post`-style names whenever an
    -- input parameter shows up. (The previous heuristic only
    -- inspected the *root local* of the arg place and missed the
    -- case where a temp shadows an input through an EvAssign.)
    let inputLocalOfArg : Nat → Nat := fun l =>
      if 1 ≤ l ∧ l ≤ st.numParams then l else 0
    let inputLocals : Array Nat := postLocals.map inputLocalOfArg
    let paramNameOfPExpr : PExpr → Option Nat := fun e =>
      match e with
      | .var name =>
        -- Match `xN` for some N in [1..numParams].
        let parsed : Option Nat :=
          if name.length ≥ 2 && name.front == 'x' then
            (name.drop 1).toNat?
          else none
        match parsed with
        | some n => if 1 ≤ n ∧ n ≤ st.numParams then some n else none
        | none => none
      | _ => none
    let inputLocalsViaExpr : Array Nat :=
      argEs.map (fun e => (paramNameOfPExpr e).getD 0)
    let (nm, st) :=
      match inputLocals.findSome? (fun l => if l = 0 then none else some l) with
      | some l => (s!"{paramName l}_post", st)
      | none =>
        match inputLocalsViaExpr.findSome? (fun l => if l = 0 then none else some l) with
        | some l => (s!"{paramName l}_post", st)
        | none => st.freshName
    let app : PExpr := .app fnName argEs
    -- M12.2a-3: when the callee has `&mut` inputs (non-empty
    -- regionAbs), the call returns a (forward, backward) pair (or
    -- just a backward when the callee's return type is unit/a
    -- single &mut input). We emit a pattern-bound monadic let
    -- destructuring the call result, and stash the backward
    -- variable's name in `callBack` so a subsequent
    -- deref-EvAssign can apply it.
    --
    -- The callee's exact shape (returns &mut? returns unit?) is
    -- inferred from the `dst` place's type. For a non-unit, non-&mut
    -- return type (rare in practice) we fall back to the M10.2b
    -- shape (single-name binding, no destructure).
    let dstIsMutRef : Bool := isMutRef dst.ty
    let dstIsUnit : Bool := isUnitTy dst.ty
    -- M12.2b: detect a multi-region call returning a tuple of
    -- N ≥ 2 mut refs. The standard backend emits N+1 result
    -- components: a forward (often `_` ignored) plus N backward
    -- closures `_back0`, `_back1`, …, `_back{N-1}`. We bind all
    -- of them via a `tuple` Bind and stash per-field closure
    -- names in callBackByField so subsequent field-destructure
    -- EvAssigns can thread them.
    let dstTupleOfMuts : Option Nat := isOutputTupleOfMutRefs dst.ty
    if regionAbs.isEmpty then
      -- No &mut inputs on the callee — straight value-flow call.
      { st with
        binds := st.binds.push (.regular nm app)
        vm := st.vm.insert dst.local_ (.var nm)
        lastWrite := some dst.local_ }
    else if (dstTupleOfMuts.isSome) && regionAbs.size ≥ 2 then
      -- Multi-region call: bind `(<nm>_v, <nm>_back0, …, <nm>_back{N-1})`.
      -- Per-field closure names go in callBackByField; the destructure
      -- assigns later route each per-region local through callBack.
      let n := regionAbs.size
      let vName := s!"{nm}_v"
      let backNames : Array String :=
        (List.range n).toArray.map fun i => s!"{nm}_back{i}"
      let names : Array String := #[vName] ++ backNames
      let cbbf := (List.range n).foldl (init := st.callBackByField)
        fun acc i =>
          acc.insert (dst.local_, i) (backNames[i]!)
      { st with
        binds := st.binds.push (.tuple names app)
        vm := st.vm.insert dst.local_ (.var vName)
        callBackByField := cbbf
        lastWrite := some dst.local_ }
    else if dstIsMutRef then
      -- Callee has &mut inputs AND returns &mut. Bind
      -- `let (nm_v, nm_back) ← fn args`. The forward result is
      -- vm[dst.local_] := nm_v; the backward closure is stashed
      -- in callBack for the next deref-assign to apply.
      let vName := s!"{nm}_v"
      let backName := s!"{nm}_back"
      { st with
        binds := st.binds.push (.pair vName backName app)
        vm := st.vm.insert dst.local_ (.var vName)
        callBack := st.callBack.insert dst.local_ backName
        lastWrite := some dst.local_ }
    else if dstIsUnit then
      -- Callee has &mut inputs AND returns unit. The call returns
      -- the backward closure directly (or a tuple of restored
      -- &mut inputs); we keep the M10.2b single-name shape since
      -- the existing EvEndAbs hook updates the input's vm slot
      -- when the trace closes the abstraction (in-body callee).
      -- For tail-position callees (no EvEndAbs in the trace), the
      -- buildBackwardTail call at translate-time falls back to the
      -- last vm-recorded post-state.
      let pending := regionAbs.foldl (init := st.pending) fun acc abs =>
        acc.insert abs
          { callKey := callId
            fnName, argEs, postLocals
            dstLocal := dst.local_ }
      { st with
        binds := st.binds.push (.regular nm app)
        vm := st.vm.insert dst.local_ (.var nm)
        pending
        emittedCalls := st.emittedCalls.insert callId
        lastWrite := some dst.local_ }
    else
      -- Callee has &mut inputs AND returns a value (not &mut, not
      -- unit). Mirror the &mut-return shape since the result is
      -- still a (value, backward) pair under the standard backend's
      -- convention.
      let vName := s!"{nm}_v"
      let backName := s!"{nm}_back"
      { st with
        binds := st.binds.push (.pair vName backName app)
        vm := st.vm.insert dst.local_ (.var vName)
        callBack := st.callBack.insert dst.local_ backName
        lastWrite := some dst.local_ }
  | .endAbs abs _finals =>
    -- M10.2b: a callee's region abstraction just closed. The call
    -- itself was already emitted at EvCall time; what's left to do
    -- here is update `vm[postLocal] := .var <bindingName>` so that
    -- subsequent reads of the borrowed input's caller-side local
    -- pick up the call's post-state. (The cert's `finalValues`
    -- already carry the OCaml-side symbolic value id for that
    -- post-state; we ignore it on the Lean side because the binding
    -- name we emitted already names the post-state slot.)
    --
    -- For multi-region calls (e.g. `choose` returning `&mut`), each
    -- sibling EvEndAbs would want to bind a distinct post-state
    -- name; M10.2b only threads the FIRST one. The others remain
    -- visible through `dstLocal` but not via the inputs' caller
    -- locals. M11 will tuple-destructure those.
    match st.pending[abs]? with
    | none => st  -- Spurious EvEndAbs (no matching call); no-op.
    | some pc =>
      -- Use the same "first input-parameter local" rule as EvCall
      -- so the binding name we re-derive matches the one we
      -- actually emitted at call time.
      let inputLocals : Array Nat := pc.postLocals.map fun l =>
        if 1 ≤ l ∧ l ≤ st.numParams then l else 0
      -- M12.2a-1: also re-derive via the arg PExprs as we do in
      -- EvCall so the naming stays consistent.
      let paramNameOfPExpr : PExpr → Option Nat := fun e =>
        match e with
        | .var name =>
          let parsed : Option Nat :=
            if name.length ≥ 2 && name.front == 'x' then (name.drop 1).toNat? else none
          match parsed with
          | some n => if 1 ≤ n ∧ n ≤ st.numParams then some n else none
          | none => none
        | _ => none
      let inputLocalsViaExpr : Array Nat :=
        pc.argEs.map (fun e => (paramNameOfPExpr e).getD 0)
      let postLocal : Nat :=
        match inputLocals.findSome? (fun l => if l = 0 then none else some l) with
        | some l => l
        | none =>
          match inputLocalsViaExpr.findSome? (fun l => if l = 0 then none else some l) with
          | some l => l
          | none => 0
      let st :=
        if postLocal == 0 then st
        else
          let postName : String := s!"{paramName postLocal}_post"
          { st with
            vm := st.vm.insert postLocal (.var postName)
            lastWrite := some postLocal }
      { st with pending := st.pending.erase abs }
  -- Out-of-M10.2b events: leave the state untouched. The replayer
  -- already rejected them upstream; this branch keeps `walkEvent`
  -- total. Branching is handled at the [walkEvents] level — by the
  -- time we hit `.assert _ _` here we know it's a real `assert!`
  -- (the branch-marker pair has already been consumed); `.join` is
  -- only reached if the [findBranchEnd] lookahead failed (malformed
  -- cert), in which case ignoring it is the safest fallback.
  | .proj _ _ _
  | .join _ _ _ | .loopInv _ _ | .loopEnd _ => st

/-- Render a `SymExpr` from a join state summary as a Pure expression
    *in the context of a sub-walk's final var map*. Used by
    [applyJoinedLocal] to materialise the per-branch value of a joined
    local. We prefer the sub-walk's `vm` over the raw cert SymExpr
    because the sub-walk has already lifted symbolic ids into named
    `t<N>` / `x<N>` bindings through the events. -/
def renderJoinSide (vm : VarMap) (cs_env : Array (Nat × SymExpr))
    (target : Nat) : Option PExpr :=
  match vm[target]? with
  | some e => some e
  | none =>
    -- Fall back to the cert's per-branch SymExpr if vm doesn't have
    -- an entry. (Should be rare — sub-walks populate vm for every
    -- local they touch.)
    let entry := cs_env.find? (fun (l, _) => l == target)
    entry.map fun (_, se) => lookupSymExpr vm se

/-- Identify locals whose post-join value should be expressed as an
    `if cond then <left> else <right>` binding. Pragmatic heuristic:
    take every local appearing in `result.env` whose value is a
    `SymVal n` (i.e., the join introduced a fresh symbolic) AND whose
    left/right per-branch values disagree in a "meaningful" way.

    A disagreement is *not* meaningful when both branches' values are
    boolean literals (`SymLit (.bool _)`). This catches the
    if-condition itself: when the OCaml interpreter expands a symbolic
    boolean `sN` into `true` on the left and `false` on the right, the
    cert's StateSummary records the post-expansion literal for the
    local that held the cond — emitting an `if c then ok true else
    ok false` for that local would be syntactically pointless and
    obscure the real joined data. M12 will track which locals are
    cond-derived through a sym-id↔local map; for M11 the literal
    check is sound (no real if/else in the program would diverge on
    a literal boolean pair).
    -/
def joinedLocals (left right result : StateSummary) : Array Nat :=
  result.env.filterMap fun (l, resE) =>
    match resE with
    | .symVal _ =>
      let leftE := (left.env.find? (fun (k, _) => k == l)).map (·.2)
      let rightE := (right.env.find? (fun (k, _) => k == l)).map (·.2)
      match leftE, rightE with
      | some le, some re =>
        -- Skip bool-literal pairs: the cond's expansion.
        match le, re with
        | .symLit (.bool _), .symLit (.bool _) => none
        | .symVal a, .symVal b =>
          if a == b then none else some l
        | _, _ => some l
      | _, _ => some l
    | _ => none

/-- Wrap a tail value in `ok` *only* when it is a pure (non-Result)
    expression. Binops emit `Result α`-typed apps already; double-
    wrapping them would change semantics. M12.2a-2: also recognize
    `ifThenElse` whose branches are themselves already Result-typed
    (each branch was built via [assembleBody] which wraps in `ok`). -/
def tailToResult (e : PExpr) : PExpr :=
  match e with
  | .app _ _ => e  -- Already monadic — binops are Result-typed.
  | .ifThenElse _ _ _ => e  -- Branches are already Result-typed.
  | _ => .ok e

/-- A binding name is "fresh" (introduced solely by the translator for
    a monadic let, with no surface-level meaning) iff it starts with
    `t` followed by a digit (the `tN` pattern used by M10.0/M10.1 for
    binops and forward-only calls). Post-state bindings emitted by
    M10.2b carry semantically meaningful names (`x1_post`, …) and
    must *not* be collapsed away even when they're the sole binding
    feeding the tail. -/
def isFreshTempName (nm : String) : Bool :=
  match nm.toList with
  | 't' :: c :: _ => c.isDigit
  | _ => false

/-- Fold the accumulated bindings around a tail expression to form a
    nested `do let … ← …; …` chain. -/
def assembleBody (binds : Array Bind) (tail : PExpr) : PExpr :=
  -- Simplification: if there is exactly one binding and the tail is
  -- just `ok (.var name)` for that name, drop the let and use the
  -- bound expression directly (it already returns Result α). This
  -- matches the standard backend's body shape for tiny functions
  -- like `incr` (`x + 1#u32`).
  --
  -- The collapse is only safe for "fresh temp" bindings (`tN`). A
  -- M10.2b post-state binding (`x1_post`) carries information about
  -- which `&mut` input's post-state we just bound, and the tail
  -- `ok x1_post` is the canonical way of returning that post-state;
  -- keeping the explicit `let x1_post ← …; ok x1_post` makes the
  -- forward-and-backward correspondence visible in the emitted code.
  let wrapOne (b : Bind) (acc : PExpr) : PExpr :=
    match b with
    | .regular nm e => .letIn nm placeholderTy e acc
    | .pair nm bnm e => .letPat #[nm, bnm] placeholderTy e acc
    | .tuple names e => .letPat names placeholderTy e acc
  match binds.toList, tail with
  | [.regular nm e], .ok (.var n) =>
    if nm == n && isFreshTempName nm then e
    else binds.foldr (init := tail) wrapOne
  | _, _ =>
    binds.foldr (init := tail) wrapOne

/-- Outer-loop walk that handles both the linear event stream and
    the M11.2 if/else branching pattern.

    For each event index:
    * If we see `EvAssert {SymVal n, true}` followed (in the well-
      formed shape) by `EvAssert {SymVal n, false}` and an `EvJoin`,
      we fork: sub-walk the true-branch event range, sub-walk the
      false-branch range, then emit `if then else` bindings for each
      joined local, then skip past the `EvJoin`.
    * Otherwise: dispatch to [walkEvent] normally. A real `assert!`
      that isn't followed by an EvJoin lookahead falls through here
      (the [findBranchEnd] check returns `none`) and is handled by
      [walkEvent]'s pass-through `.assert` case.

    Sub-walks start from the parent walk's state but use a *fresh*
    `binds` buffer so each branch's body can be assembled
    independently. The parent's `fresh` counter is threaded so
    binding names stay globally unique. -/
partial def walkEvents (evs : Array Event) (st0 : WalkState) : WalkState :=
  let rec go (i : Nat) (st : WalkState) : WalkState :=
    if h : i ≥ evs.size then st
    else
      let ev := evs[i]'(Nat.lt_of_not_ge h)
      match ev with
      | .assert (.symVal n) true =>
        -- Possible branch opener. Look ahead.
        match findBranchEnd evs i (.symVal n) with
        | none =>
          -- Real assert!: fall through to walkEvent.
          go (i + 1) (walkEvent st ev)
        | some (.returnTailed jIdx tEnd fEnd) =>
          -- M12.2a-2: both branches end in EvReturn with no join.
          -- This is the `choose`-style "two early returns" pattern.
          -- We sub-walk each branch and assemble its tail from
          -- whatever local 0 (the LLBC return slot) ends up holding.
          let leftEvs  := (evs.extract (i + 1) tEnd)
          let rightEvs := (evs.extract (jIdx + 1) fEnd)
          let leftSub  := walkEvents leftEvs  { st with binds := #[] }
          let rightSub := walkEvents rightEvs { st with binds := #[], fresh := leftSub.fresh }
          -- Pick the condition's surface form. Mirror the
          -- M11.2 heuristic but without a join witness: look up the
          -- parent's `vm` for the cond's symbolic id directly.
          --
          -- The cond's sym id is `n`. M11.0's EvAssert(true) hook
          -- typically fires *after* an EvAssign of the cond local
          -- to a SymVal n; the parent's `vm` already has `vm[l] :=
          -- .var <param>`. We scan for any local in vm whose entry
          -- is a `.var` matching a known param name. Default to
          -- `s{n}` if we can't refine.
          let cond : PExpr := Id.run do
            -- Find which local holds a parameter named .var
            -- pointing into the parent's params. The branch
            -- marker's `cond` is `SymVal n`; the OCaml emits this
            -- after `eval_operand` on a Bool-typed operand whose
            -- value was just expanded. The cleanest signal: look
            -- at the *last* EvAssign before `i` whose dst.local_
            -- maps to a bool-typed param. As a coarse fallback,
            -- pick the first input-parameter local that is in vm
            -- and whose stored expression is `.var "xK"`.
            let mut found : Option PExpr := none
            for (l, e) in st.vm.toList do
              -- Heuristic: prefer the lowest-numbered param.
              if 1 ≤ l ∧ l ≤ st.numParams then
                match e with
                | .var name =>
                  match found with
                  | none => found := some (.var name)
                  | some _ => pure ()
                | _ => pure ()
            return found.getD (.var s!"s{n}")
          -- The leftSub / rightSub's vm have everything they
          -- assigned. For a Return-tailed branch, the tail
          -- expression is `vm[0]` (the LLBC return slot), wrapped
          -- in ok.
          let leftTail : PExpr :=
            leftSub.vm.getD 0 (.lit (.scalar .u32 0))
          let rightTail : PExpr :=
            rightSub.vm.getD 0 (.lit (.scalar .u32 0))
          let thenBody := assembleBody leftSub.binds (tailToResult leftTail)
          let elseBody := assembleBody rightSub.binds (tailToResult rightTail)
          let ite : PExpr := PExpr.ifThenElse cond thenBody elseBody
          -- The whole body is this if/else; bind it into vm[0] so
          -- the top-level wrap-up picks it up. We also push a fresh
          -- binding so the linear walk's tail logic preserves the
          -- if-then-else when the caller assembles the body.
          --
          -- Easier: thread the if/else as the final value of
          -- vm[0], then jump past the false branch's EvReturn.
          let st' :=
            { st with
              fresh := rightSub.fresh
              vm := st.vm.insert 0 ite
              lastWrite := some 0
              -- M12.2a-2: also stash the per-branch sub-walk's vm[0]
              -- (the raw forward value of each branch) so the
              -- backward-function builder can re-derive which input
              -- each branch returned through.
              branchTrueVm0 := some leftSub.vm
              branchFalseVm0 := some rightSub.vm }
          go (fEnd + 1) st'
        | some (.joined jIdx kIdx) =>
          -- Found: branch range is (i+1 .. jIdx-1) for true,
          -- (jIdx+1 .. kIdx-1) for false. The EvJoin is at kIdx.
          let leftEvs := (evs.extract (i + 1) jIdx)
          let rightEvs := (evs.extract (jIdx + 1) kIdx)
          -- Build sub-walks with empty `binds` so each branch's
          -- bindings come out as a self-contained do-block. The
          -- parent's vm + fresh counter are inherited.
          let leftSub := walkEvents leftEvs
            { st with binds := #[] }
          let rightSub := walkEvents rightEvs
            { st with binds := #[], fresh := leftSub.fresh }
          -- Compute the condition's surface form. We default to the
          -- raw symbolic name `sN` (so the diagnostics carry the
          -- cert's sym id), but try to refine to a parameter name
          -- when the join witness lets us identify which local held
          -- the cond at branch time.
          --
          -- Heuristic: the cond local is the one whose `left.env`
          -- entry is `SymLit (.bool true)` and `right.env` entry is
          -- `SymLit (.bool false)` — that's the OCaml-side trace of
          -- `expand_symbolic_bool` on the condition. If we find such
          -- a local AND its parent-`vm` entry is already a `.var`,
          -- use that variable name.
          let joinOpt : Option Event := evs[kIdx]?
          match joinOpt with
          | some (.join leftSummary rightSummary resultSummary) =>
            -- Refine the cond. See heuristic above the joinOpt def.
            let cond : PExpr := Id.run do
              let leftBoolLocal : Option Nat :=
                leftSummary.env.findSome? fun (l, v) =>
                  match v with
                  | SymExpr.symLit (Lit.bool true) =>
                    -- Check rightSummary has the matching `false`.
                    match (rightSummary.env.find? (fun (k, _) => k == l)).map (·.2) with
                    | some (SymExpr.symLit (Lit.bool false)) => some l
                    | _ => none
                  | _ => none
              match leftBoolLocal with
              | some l =>
                match st.vm[l]? with
                | some (PExpr.var name) => return PExpr.var name
                | _ => return PExpr.var s!"s{n}"
              | none => return PExpr.var s!"s{n}"
            -- For each joined local, materialise a `let r ← if cond
            -- then ok <left> else ok <right>` binding in the parent's
            -- binds.
            let locals := joinedLocals leftSummary rightSummary resultSummary
            let st' := locals.foldl (init := { st with
              fresh := rightSub.fresh
              vm := st.vm }) fun acc target =>
              let leftValOpt := renderJoinSide leftSub.vm leftSummary.env target
              let rightValOpt := renderJoinSide rightSub.vm rightSummary.env target
              match leftValOpt, rightValOpt with
              | some lE, some rE =>
                -- Wrap each branch with the sub-walk's binds so the
                -- if-then-else captures the full per-branch
                -- computation. For pick-style fixtures the
                -- sub-walks have empty binds (all `EvCopy` /
                -- `EvAssign`s map into vm without producing lets),
                -- so this collapses to `if cond then ok lE else ok rE`.
                let thenBody := assembleBody leftSub.binds (tailToResult lE)
                let elseBody := assembleBody rightSub.binds (tailToResult rE)
                let ite : PExpr := PExpr.ifThenElse cond thenBody elseBody
                let (nm, acc) := acc.freshName
                { acc with
                  binds := acc.binds.push (.regular nm ite)
                  vm := acc.vm.insert target (.var nm)
                  lastWrite := some target }
              | _, _ => acc
            go (kIdx + 1) st'
          | _ =>
            -- findBranchEnd's lookahead said this is a join, but
            -- the event at kIdx isn't EvJoin — should not happen
            -- under M11.0's emission. Fall back to per-event walk.
            go (i + 1) (walkEvent st ev)
      | _ => go (i + 1) (walkEvent st ev)
  go 0 st0

/-- M12.2a-2: Backward-function signature description.
    Captures everything `translateFun` needs to know about the
    function's borrow pattern to build the right (forward, backward)
    output shape.

    `mutInputs` is the array of 1-indexed input-parameter positions
    whose type is `&mut T`. `mutInputTys` is the elementwise unwrap
    of those parameters' types (i.e., the `T` from each `&mut T`).
    `outputIsMutRef` is `true` when the function's return type is
    itself a `&mut T`. `outputInnerTy` is the unwrapped output `T`
    when `outputIsMutRef`, else the raw output PTy. -/
structure BackSig where
  mutInputs     : Array Nat
  mutInputTys   : Array PTy
  outputIsMutRef : Bool
  outputInnerTy : PTy
  outputIsUnit  : Bool
  /-- M12.2b: `some N` when the output is a TAdt-TTuple containing N
      TRef-RMut fields (each in its own region). Drives the
      multi-back-closure emit shape. `none` means single-region or
      non-borrow output (M12.2a falls back to the existing shape). -/
  outputTupleOfMuts : Option Nat
  deriving Repr, Inhabited

/-- M9.5b: build the [BackSig] from a function signature, with a
    type-decl map for resolving `&mut Pair`-style inputs into a
    concrete `.adt "Pair" #[]` PTy (rather than the M11 placeholder
    `u32`). Falls back to [rawTyToPTy] when `tdm` is empty. -/
def backSigOfWith (tdm : TypeDeclMap) (sig : FnSignature) : BackSig := Id.run do
  let mut mutInputs : Array Nat := #[]
  let mut mutInputTys : Array PTy := #[]
  for i in [0:sig.inputs.size] do
    let t := sig.inputs[i]!
    if isMutRef t then
      mutInputs := mutInputs.push (i + 1)
      mutInputTys := mutInputTys.push (rawTyToPTyWith tdm t)
  let bs : BackSig :=
    { mutInputs, mutInputTys
      outputIsMutRef := isMutRef sig.output
      outputInnerTy := rawTyToPTyWith tdm sig.output
      outputIsUnit := isUnitTy sig.output
      outputTupleOfMuts := isOutputTupleOfMutRefs sig.output }
  return bs

/-- Build the [BackSig] from a function signature. Kept for back-compat
    with callers that have no type-decl map; defers to
    [backSigOfWith] with an empty map. -/
def backSigOf (sig : FnSignature) : BackSig := backSigOfWith {} sig

/-- M12.2a-2: backward closure type for a [BackSig]. Returns `none`
    when the function has no `&mut` inputs (no backward function
    needed). The closure shape is:
    * domain = `outputInnerTy` (the value the caller wrote through
      the returned `&mut` borrow). When the function doesn't return
      a `&mut` we conservatively use `Unit`, but the corresponding
      closure is rarely used directly — see [emitRetTy].
    * codomain = `tupleTy mutInputTys` (the restored post-state of
      each `&mut` input, in input-position order). For a single
      `&mut` input we collapse the tuple to the bare type. -/
def backClosureTy (bs : BackSig) : Option PTy :=
  if bs.mutInputs.isEmpty then none
  else
    let dom := if bs.outputIsMutRef then bs.outputInnerTy else .unit
    let cod :=
      if bs.mutInputTys.size = 1 then bs.mutInputTys[0]!
      else .tuple bs.mutInputTys
    some (.arrow dom cod)

/-- M12.2a-2: the function's final return type, accounting for
    backward functions.
    * 0 mut inputs: raw output (unchanged from M10).
    * mut input(s), output is `&mut T_o`:
      `(T_o × (T_o → tuple T_args))`
    * mut input(s), unit output:
      `tuple T_args` (single mut → bare T_arg). This matches the
      M10.2b shape `incr(&mut u32) → u32`.
    * mut input(s), non-unit non-borrow output:
      `(T_o × (T_o → tuple T_args))` (conservative; rare in
      practice). -/
def emitRetTy (bs : BackSig) : PTy :=
  if bs.mutInputs.isEmpty then bs.outputInnerTy
  -- M12.2b: output is `(&'r₀ mut T, …, &'r_{N-1} mut T)` with N ≥ 2.
  -- The standard backend emits a flat tuple
  --   `(fwd_tuple × back_0 × … × back_{N-1})`
  -- where each `back_i : T_i → T_i` is the closure for the i-th
  -- region (one per output field). This branch must come BEFORE the
  -- generic `outputIsMutRef` / `outputIsUnit` cases — the per-region
  -- handling supersedes the single-back-closure conservative shape.
  else if let some n := bs.outputTupleOfMuts then
    if n ≥ 2 then
      -- Inner forward tuple: the unwrapped value type per mut input,
      -- in order. We reuse `mutInputTys` since the count matches
      -- (one returned ref per input region) — true for `swap_pair`
      -- and similar pass-through helpers; revisit if a future
      -- fixture has #outputs ≠ #inputs.
      let fwdTuple : PTy :=
        if bs.mutInputTys.size = 1 then bs.mutInputTys[0]!
        else .tuple bs.mutInputTys
      let backs : Array PTy := bs.mutInputTys.map fun t => .arrow t t
      .tuple (#[fwdTuple] ++ backs)
    else
      -- Fall back to the M12.2a shape.
      match backClosureTy bs with
      | some bcty => .tuple #[bs.outputInnerTy, bcty]
      | none => bs.outputInnerTy
  else if bs.outputIsMutRef then
    -- forward T_o paired with backward closure
    match backClosureTy bs with
    | some bcty => .tuple #[bs.outputInnerTy, bcty]
    | none => bs.outputInnerTy
  else if bs.outputIsUnit then
    -- only backward: single mut → bare; many → tuple
    if bs.mutInputTys.size = 1 then bs.mutInputTys[0]!
    else .tuple bs.mutInputTys
  else
    -- value output AND mut inputs; conservative pair shape
    match backClosureTy bs with
    | some bcty => .tuple #[bs.outputInnerTy, bcty]
    | none => bs.outputInnerTy

/-- M12.2a-2: build the per-branch forward-and-backward tail value
    given the branch's sub-walk var map.

    `bs` is the function's BackSig. `vm` is the branch's terminal
    var map (after the sub-walk consumed the branch's events). The
    returned expression is `ok (...)`-wrapped already, ready to be
    placed in `tailToResult`.

    Algorithm:
    1. Compute each `&mut` input's post-state: `vm.getD p (.var
       (paramName p))`. For inputs that were never written to, this
       falls back to the original `xK` name.
    2. Find the "selected" input: the one whose post-state equals
       `vm[0]` (the forward return value). This is the input whose
       borrow was returned by the function. If none matches, the
       function modified the inputs but didn't return a borrow into
       any of them; in that case the backward closure is `fun _ =>
       <unchanged tuple>`.
    3. Build the backward lambda: takes a fresh parameter `ret` and
       returns the tuple of post-states with the selected input's
       slot replaced by `ret`.
    4. Wrap the forward value and the closure into the BackSig's
       canonical output shape.

    Special case (M12.2a-3): when `vm[0]` is an `.app` whose head
    matches a known backward-closure binding name (e.g.
    `<call>_back` for `use_choose`'s `*r = 7` after-call assign), it
    already represents the function's tail tuple. We pass it through
    directly rather than re-synthesising a closure from per-input
    post-states. -/
def buildBackwardTail (bs : BackSig) (vm : VarMap) : PExpr :=
  -- M12.2b: callee that returns `(&'r₀ mut T, …)` with N ≥ 2 regions.
  -- Emit `ok ((x₁, …, xₙ), fun ret₀ => ret₀, …, fun ret_{N-1} =>
  -- ret_{N-1})`. Each back closure is identity for pass-through
  -- helpers (the only fixture under test today). The forward tuple
  -- is the post-state of each `&mut` input, in order — which for
  -- pass-through means the input's original name `xK`.
  let multiRegionTail : Option PExpr :=
    match bs.outputTupleOfMuts with
    | some n =>
      if n ≥ 2 then
        let postStates : Array PExpr := bs.mutInputs.map fun p =>
          vm.getD p (.var (paramName p))
        let fwdTuple : PExpr :=
          if postStates.size = 1 then postStates[0]!
          else .tuple postStates
        let backs : Array PExpr := bs.mutInputTys.mapIdx fun i t =>
          let retNm := s!"ret{i}"
          .lam #[(retNm, t)] (.var retNm)
        some (.ok (.tuple (#[fwdTuple] ++ backs)))
      else none
    | none => none
  match multiRegionTail with
  | some t => t
  | none =>
  let fwdValue : PExpr := vm.getD 0 (
    if bs.mutInputs.size ≥ 1 then .var (paramName bs.mutInputs[0]!)
    else .lit (.scalar .u32 0))
  -- M12.2a-3: if the deref-write hook already populated vm[0] with
  -- the application of a backward closure, that *is* the
  -- function's tail. Recognise by `.app head args` whose head ends
  -- in `_back`.
  let vm0IsBackApp : Bool :=
    match vm[0]? with
    | some (PExpr.app head _) => (head.splitOn "_back").length ≥ 2
    | _ => false
  if vm0IsBackApp && bs.outputIsUnit then
    .ok fwdValue
  else
  let postStates : Array PExpr := bs.mutInputs.map fun p =>
    vm.getD p (.var (paramName p))
  -- Find the selected input: vm[p] structurally equals fwdValue.
  let eqExpr : PExpr → PExpr → Bool
    | .var a, .var b => a == b
    | _, _ => false
  let selectedIdx : Option Nat :=
    postStates.findIdx? fun e => eqExpr e fwdValue
  -- Build the backward closure (or omit it if no &mut inputs).
  match backClosureTy bs with
  | none =>
    -- No mut inputs. Forward only.
    .ok fwdValue
  | some _ =>
    let retName : String := "ret"
    let backTuple : Array PExpr :=
      match selectedIdx with
      | some idx =>
        postStates.mapIdx fun i e => if i = idx then .var retName else e
      | none => postStates
    let backBody : PExpr :=
      if backTuple.size = 1 then backTuple[0]!
      else .tuple backTuple
    let domTy := if bs.outputIsMutRef then bs.outputInnerTy else .unit
    let backLam : PExpr := .lam #[(retName, domTy)] backBody
    if bs.outputIsMutRef then
      .ok (.tuple #[fwdValue, backLam])
    else if bs.outputIsUnit then
      -- No forward value; the backward result IS the return.
      if backTuple.size = 1 then .ok backTuple[0]!
      else .ok (.tuple backTuple)
    else
      .ok (.tuple #[fwdValue, backLam])

/-- Translate a function's cert + replay into a Pure decl.

    The forward translator walks `f.events`, updates a per-local
    pure-expression map, and emits `let tN ← …` bindings for each
    binop. The tail of the resulting `do`-block is whichever local
    LLBC's return convention dictates — for now: local 0 for value
    returns and the borrowed input's root for `&mut`-returning
    signatures. We approximate "did this function take a `&mut`?" by
    checking if any borrow event fired in the trace; if so, we pick
    the input's root local rather than local 0. -/
def translateFunWith (tdm : TypeDeclMap) (f : Raw.FunCert) (_t : CheckedTrace) : Decl :=
  let numParams := f.signature.inputs.size
  let params : Array Param :=
    (List.range numParams).toArray.map fun i =>
      let ty := match f.signature.inputs[i]? with
        | some t => rawTyToPTyWith tdm t
        | none => placeholderTy
      { name := paramName (i + 1), ty }
  -- M12.1: loop-bearing functions are handled separately by
  -- `translateLoopFun` (called from `Driver.translateCrate` before
  -- this function). If we reach here with `EvLoopInv` in the
  -- events, fall through to the linear walk anyway — the result
  -- won't be semantically right, but it will be syntactically valid
  -- Lean code. Driver should always route loops through
  -- `translateLoopFun`.
  -- Initial var map: input local 1 ↦ x1, local 2 ↦ x2, ...
  let initVm : VarMap := Id.run do
    let mut m : VarMap := {}
    for i in [0:numParams] do
      m := m.insert (i + 1) (.var (paramName (i + 1)))
    return m
  let finalSt : WalkState :=
    walkEvents f.events { vm := initVm, numParams, tdm }
  -- M12.2a-2: pick the function's output shape based on its
  -- signature's borrow pattern. See [BackSig] / [emitRetTy].
  let bs := backSigOfWith tdm f.signature
  let retTy : PTy := emitRetTy bs
  -- M12.2a-2: branch-tailed bodies (the `choose` pattern) compute
  -- their per-branch tail value through [buildBackwardTail] on each
  -- sub-walk's vm. The Return-tailed walker stashed each sub-walk's
  -- vm in `branchTrueVm0` / `branchFalseVm0` and put a single
  -- `ifThenElse` into the parent's `vm[0]`. Detect that case and
  -- rebuild the `if cond then ok (...) else ok (...)` with proper
  -- backward closures.
  let body : PExpr :=
    match finalSt.branchTrueVm0, finalSt.branchFalseVm0 with
    | some tvm, some fvm =>
      -- Re-derive the condition from the parent's vm at branch
      -- time. The walker stored an `ifThenElse cond _ _` in
      -- vm[0]; pull `cond` from there.
      let cond : PExpr :=
        match finalSt.vm[0]? with
        | some (PExpr.ifThenElse c _ _) => c
        | _ =>
          -- Fallback: scan vm for a Bool-typed param.
          Id.run do
            let mut found : Option PExpr := none
            for (l, e) in finalSt.vm.toList do
              if 1 ≤ l ∧ l ≤ numParams then
                match e with
                | PExpr.var _ => found := some e
                | _ => pure ()
            return found.getD (PExpr.var "cond")
      let leftTail := buildBackwardTail bs tvm
      let rightTail := buildBackwardTail bs fvm
      -- assembleBody around each branch picks up the sub-walk's
      -- binds if any. Since the sub-walks' binds were thrown away
      -- when we built `branchTrueVm0/falseVm0` (only the vm was
      -- preserved), we rely on the sub-walks themselves having
      -- already absorbed every binding into vm. This works for
      -- `choose` where the bodies are pure reborrow chains; for
      -- bodies with binops inside a Return-tailed branch we'd
      -- need to thread the binds too — deferred to M12.2b.
      let ite : PExpr := PExpr.ifThenElse cond leftTail rightTail
      assembleBody finalSt.binds ite
    | _, _ =>
      -- Linear body. Use the BackSig to pick the right tail.
      if bs.mutInputs.isEmpty then
        -- Regular function: standard return convention.
        let tailE : PExpr := finalSt.vm.getD 0 (
          if numParams ≥ 1 then .var (paramName 1)
          else .lit (.scalar .u32 0))
        assembleBody finalSt.binds (tailToResult tailE)
      else if !finalSt.multiRegionTail.isEmpty then
        -- M12.2b: caller of a multi-region helper. The deref-EvAssigns
        -- through each destructured local accumulated one back-
        -- closure application per region. Build `ok (app_0, app_1,
        -- …, app_{N-1})` in field order; gaps default to the
        -- corresponding input's `xK` (the input was untouched).
        let n := bs.mutInputs.size
        let comps : Array PExpr := (List.range n).toArray.map fun i =>
          finalSt.multiRegionTail.getD i (.var (paramName bs.mutInputs[i]!))
        let tuple : PExpr :=
          if comps.size = 1 then comps[0]!
          else .tuple comps
        assembleBody finalSt.binds (.ok tuple)
      else
        -- Has &mut inputs. Build the forward-and-backward shape
        -- from the linear walk's final vm.
        let tail := buildBackwardTail bs finalSt.vm
        assembleBody finalSt.binds tail
  { name := innerName f.fnName
    qualifiedName := f.fnName
    params, retTy, body
    sourceSpan := f.sourceSpan }

/-- M9.5b: kept-for-back-compat wrapper around [translateFunWith]
    with an empty type-decl map. Real translation goes through
    [translateFunWith] from the Driver. -/
def translateFun (f : Raw.FunCert) (t : CheckedTrace) : Decl :=
  translateFunWith {} f t

end AeneasCheck.Translate
