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

/-- M12.2a-3: a single accumulated monadic binding in the walk's
    do-block. Most bindings are `regular` — `let <name> ← <rhs>`.
    For calls into `&mut`-taking helpers the binding destructures
    the result pair: `let (<name>, <backName>) ← <rhs>`. The
    pattern form is rendered as `letPat` in [assembleBody]. -/
inductive Bind
  | regular (name : String) (rhs : PExpr)
  | pair (name backName : String) (rhs : PExpr)
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
    if derefTail then
      match st.callBack[d.local_]? with
      | some backName =>
        -- The backward closure was bound as `<backName> : T → tuple`.
        -- Applying it to the assigned RHS yields the function's
        -- restored `&mut` input post-states, which IS the function's
        -- return value for unit-returning callers (e.g. use_choose).
        let tailE : PExpr := .app backName #[rhsE]
        { st with
          vm := st.vm.insert 0 tailE
          lastWrite := some 0 }
      | none =>
        -- No tracked backward closure; treat the deref-write as a
        -- regular update to the root local's vm entry. This matches
        -- the M10 behavior and is sound when the borrow's owner is
        -- one of the function's own `&mut` inputs (the in-function
        -- mutation case).
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
    if regionAbs.isEmpty then
      -- No &mut inputs on the callee — straight value-flow call.
      { st with
        binds := st.binds.push (.regular nm app)
        vm := st.vm.insert dst.local_ (.var nm)
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
  deriving Repr, Inhabited

/-- Build the [BackSig] from a function signature. -/
def backSigOf (sig : FnSignature) : BackSig := Id.run do
  let mut mutInputs : Array Nat := #[]
  let mut mutInputTys : Array PTy := #[]
  for i in [0:sig.inputs.size] do
    let t := sig.inputs[i]!
    if isMutRef t then
      mutInputs := mutInputs.push (i + 1)
      mutInputTys := mutInputTys.push (rawTyToPTy t)
  let bs : BackSig :=
    { mutInputs, mutInputTys
      outputIsMutRef := isMutRef sig.output
      outputInnerTy := rawTyToPTy sig.output
      outputIsUnit := isUnitTy sig.output }
  return bs

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
  -- M12.2a-2: pick the function's output shape based on its
  -- signature's borrow pattern. See [BackSig] / [emitRetTy].
  let bs := backSigOf f.signature
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
      else
        -- Has &mut inputs. Build the forward-and-backward shape
        -- from the linear walk's final vm.
        let tail := buildBackwardTail bs finalSt.vm
        assembleBody finalSt.binds tail
  { name := innerName f.fnName
    qualifiedName := f.fnName
    params, retTy, body
    sourceSpan := f.sourceSpan }

end AeneasCheck.Translate
