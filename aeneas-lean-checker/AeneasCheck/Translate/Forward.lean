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

/-- Crude `RawTy` → `PTy` mapping based on substring lookup in the
    opaque-tagged signature string. M11 brings the first cases that
    actually matter (Bool for `if` conditions); M12 will replace this
    with a structural parser fed by `llbc.json`. -/
def rawTyToPTy : RawTy → PTy
  | .opaque s =>
    if (s.splitOn "TBool").length ≥ 2 then .lit .bool
    else if (s.splitOn "U64").length ≥ 2 then .lit (.int .u64)
    else if (s.splitOn "I32").length ≥ 2 then .lit (.int .i32)
    else if (s.splitOn "U16").length ≥ 2 then .lit (.int .u16)
    else if (s.splitOn "U8").length ≥ 2 then .lit (.int .u8)
    else if (s.splitOn "Usize").length ≥ 2 then .lit (.int .usize)
    else if (s.splitOn "TRef").length ≥ 2 then .lit (.int .u32)
    else .lit (.int .u32)
  | _ => .lit (.int .u32)

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

/-- Walk state: accumulated `let` bindings (in monadic order) plus
    the current per-local pure expression map. -/
structure WalkState where
  binds : Array (String × PExpr) := #[]
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

/-- M11.2 helper: find the indices `(falseAssertIdx, joinIdx)` of the
    branch-marker `EvAssert {cond, false}` and the following `EvJoin`
    that close out a branching block that opens at `i` (which is
    `EvAssert {cond, true}`).

    Returns `none` if the pattern isn't a match (e.g. a real `assert!`
    not surrounded by an EvJoin, or a malformed cert). The search is
    one-level-deep: nested ifs inside a branch leave their own
    well-formed EvAssert+EvJoin runs whose first-`true` marker we'll
    *not* match because we only consider markers carrying the same
    `cond` SymExpr as the opening one. (The inner if's `cond` is a
    different symbolic value, so its markers don't clash.) -/
def findBranchEnd (evs : Array Event) (i : Nat) (openCond : SymExpr) :
    Option (Nat × Nat) := Id.run do
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
    -- Now find the EvJoin that closes this block. Same depth logic.
    let mut depth2 : Nat := 0
    let mut joinIdx : Option Nat := none
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
      | _ => pure ()
      m := m + 1
    match joinIdx with
    | none => none
    | some kIdx => some (jIdx, kIdx)
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
    { st with
      vm := st.vm.insert d.local_ (lookupSymExpr st.vm rhs)
      lastWrite := some d.local_ }
  | .binop op lhs rhs d =>
    let lhsE := lookupSymExpr st.vm lhs
    let rhsE := lookupSymExpr st.vm rhs
    let app : PExpr := .app (binopHead op) #[lhsE, rhsE]
    let (nm, st) := st.freshName
    let bind := (nm, app)
    { st with
      binds := st.binds.push bind
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
    -- For args whose root local is a temp (not an input parameter),
    -- we stay with `tN` — naming a binding `x5_post` when local 5
    -- is the stack slot for a temporary would be misleading.
    let inputLocalOfArg : Nat → Nat := fun l =>
      if 1 ≤ l ∧ l ≤ st.numParams then l else 0
    let inputLocals : Array Nat := postLocals.map inputLocalOfArg
    let (nm, st) :=
      match inputLocals.findSome? (fun l => if l = 0 then none else some l) with
      | some l => (s!"{paramName l}_post", st)
      | none => st.freshName
    let app : PExpr := .app fnName argEs
    let st :=
      { st with
        binds := st.binds.push (nm, app)
        vm := st.vm.insert dst.local_ (.var nm)
        lastWrite := some dst.local_ }
    -- Record the pending entries so EvEndAbs can update vm for
    -- the borrowed input(s).
    if regionAbs.isEmpty then st
    else
      let pending := regionAbs.foldl (init := st.pending) fun acc abs =>
        acc.insert abs
          { callKey := callId
            fnName, argEs, postLocals
            dstLocal := dst.local_ }
      { st with
        pending
        emittedCalls := st.emittedCalls.insert callId }
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
      let postLocal : Nat :=
        match inputLocals.findSome? (fun l => if l = 0 then none else some l) with
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
  | .join _ _ _ | .loopInv _ _ => st

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
    wrapping them would change semantics. -/
def tailToResult (e : PExpr) : PExpr :=
  match e with
  | .app _ _ => e  -- Already monadic — binops are Result-typed.
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
def assembleBody (binds : Array (String × PExpr)) (tail : PExpr) : PExpr :=
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
  match binds.toList, tail with
  | [(nm, e)], .ok (.var n) =>
    if nm == n && isFreshTempName nm then e
    else binds.foldr (init := tail) (fun (n, e) acc =>
      .letIn n placeholderTy e acc)
  | _, _ =>
    binds.foldr (init := tail) (fun (n, e) acc =>
      .letIn n placeholderTy e acc)

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
        | some (jIdx, kIdx) =>
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
                  binds := acc.binds.push (nm, ite)
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

/-- Translate a function's cert + replay into a Pure decl.

    The forward translator walks `f.events`, updates a per-local
    pure-expression map, and emits `let tN ← …` bindings for each
    binop. The tail of the resulting `do`-block is whichever local
    LLBC's return convention dictates — for now: local 0 for value
    returns and the borrowed input's root for `&mut`-returning
    signatures. We approximate "did this function take a `&mut`?" by
    checking if any borrow event fired in the trace; if so, we pick
    the input's root local rather than local 0. -/
def translateFun (f : Raw.FunCert) (_t : CheckedTrace) : Decl :=
  let numParams := f.signature.inputs.size
  let params : Array Param :=
    (List.range numParams).toArray.map fun i =>
      let ty := match f.signature.inputs[i]? with
        | some t => rawTyToPTy t
        | none => placeholderTy
      { name := paramName (i + 1), ty }
  -- M12.0: detect loop-bearing functions. The forward translator
  -- does not yet implement the LLBC# loop-translation rule
  -- (T-Loop-Fixpoint) — that lands in M12.1. For now we emit the
  -- function with a sentinel body (an `ok` of a default value of the
  -- return type) and tag it with a translator note pointing at
  -- M12.1. The full event walk would otherwise produce a partially-
  -- unrolled body that misrepresents the function's semantics.
  let hasLoop : Bool := f.events.any fun
    | .loopInv _ _ => true
    | _ => false
  let retTy0 : PTy := rawTyToPTy f.signature.output
  if hasLoop then
    -- Sentinel body: `ok` of a default value at the return type. We
    -- pick `0` for any integer kind, `false` for `Bool`, and U32 0
    -- as a coarse fallback for other shapes (the body is only
    -- meaningful as a "function exists, body deferred to M12.1"
    -- marker; downstream emit + lake build are all we exercise).
    let sentinelTail : PExpr :=
      match retTy0 with
      | .lit (.int k) => .lit (.scalar k 0)
      | .lit .bool => .lit (.bool false)
      | _ => .lit (.scalar .u32 0)
    let body : PExpr := .ok sentinelTail
    let note := s!"loop-containing function ({f.fnName}): body is a sentinel placeholder; M12.1 implements T-Loop-Fixpoint."
    { name := innerName f.fnName
      qualifiedName := f.fnName
      params, retTy := retTy0, body
      sourceSpan := f.sourceSpan
      note := some note }
  else
  -- Initial var map: input local 1 ↦ x1, local 2 ↦ x2, ...
  let initVm : VarMap := Id.run do
    let mut m : VarMap := {}
    for i in [0:numParams] do
      m := m.insert (i + 1) (.var (paramName (i + 1)))
    return m
  let finalSt : WalkState :=
    walkEvents f.events { vm := initVm, numParams }
  -- Forward return value:
  -- * If any cert event has explicit "borrow flow" (EvMutBorrow /
  --   EvReborrow / EvSharedBorrow), or if any signature input has a
  --   `TRef`-shaped opaque type, the function's mutation flows out
  --   through a borrowed input. Under M10.0 we approximate that
  --   post-state by `lastWrite` — the most recent value-producing
  --   event's destination. M10.2's backward-function pass replaces
  --   this with an exact per-borrow lookup.
  -- * Otherwise we use LLBC's standard return-value convention,
  --   local 0.
  let signatureHasRef : Bool :=
    f.signature.inputs.any fun t => match t with
      | .opaque s => (s.splitOn "TRef").length > 1
      | _ => false
  let usesBorrow : Bool := signatureHasRef || f.events.any fun
    | .mutBorrow _ _ _ | .reborrow _ _ _ | .sharedBorrow _ _ _ _ => true
    | _ => false
  let returnLocal : Nat :=
    if usesBorrow then finalSt.lastWrite.getD 1 else 0
  let tailE : PExpr :=
    -- Fall back to x1 when neither local has been touched (matches
    -- the M7 identity placeholder behaviour).
    finalSt.vm.getD returnLocal (
      if numParams ≥ 1 then .var (paramName 1)
      else .lit (.scalar .u32 0))
  -- M11.2 type-mismatch guard: when the lookupPlace fallback hands
  -- us a parameter of the wrong type (e.g. `choose(b: bool, …)`
  -- whose `usesBorrow` heuristic falls back to local 1 = `b : Bool`
  -- but the real output type is `&mut u32`), the emitted `ok b`
  -- would not typecheck against `Result Std.U32`. Detect the case
  -- and substitute a sentinel literal with a clear TODO marker; M12
  -- (backward function machinery) will replace this with the real
  -- post-state lookup.
  let retTy : PTy := rawTyToPTy f.signature.output
  let tailE : PExpr :=
    match tailE, retTy with
    | .var name, .lit (.int kind) =>
      -- Look up the param's typed PTy; if it's not the same as the
      -- return type, swap for a 0 literal of the return type.
      let pIdx := params.findIdx? (fun p => p.name == name)
      match pIdx with
      | some idx =>
        match params[idx]? with
        | some param =>
          match param.ty with
          | .lit (.int k') => if k' == kind then tailE else .lit (.scalar kind 0)
          | _ => .lit (.scalar kind 0)  -- TODO M12: backward fn
        | none => tailE
      | none => tailE
    | _, _ => tailE
  let body : PExpr := assembleBody finalSt.binds (tailToResult tailE)
  { name := innerName f.fnName
    qualifiedName := f.fnName
    params, retTy, body
    sourceSpan := f.sourceSpan }

end AeneasCheck.Translate
