import AeneasCheck.Pure.Syntax
import AeneasCheck.LLBCSharp.Replay
import AeneasCheck.Translate.Forward

/-!
M12.1 — T-Loop-Fixpoint forward translation.

Drives the per-function loop translation: a function whose cert
contains an `EvLoopInv` / `EvLoopEnd` pair (one syntactic loop) is
split into three Pure decls:

* `<fn>_loop.body (forwarded...) (state...) : Result (ControlFlow
  state_ty fwd_ty)` — the loop body. Walks the body events between
  the matching `EvLoopInv` (start marker) and `EvLoopEnd` (end
  marker). The body recognises the conditional shape `EvAssert(c,
  true) [continue body] EvAssert(c, false)` as `if cond then ok
  (cont <new state>) else ok (done <break state>)`.

* `<fn>_loop (forwarded...) (state...) : Result fwd_ty` — the loop
  wrapper. Calls the `loop` combinator from
  `backends/lean/Aeneas/Std/Primitives.lean` with the body and the
  initial state.

* `<fn> (inputs...) : Result <retTy>` — the top-level function. Walks
  pre-loop events (typically to compute the loop's initial state
  from the inputs), then calls `<fn>_loop` with forwarded inputs and
  the initial state.

State-variable inference: a "state local" is any local appearing in
the loop invariant's env that is not one of the function's input
parameters (locals 1..numParams). For the M12.1 fixture `count_to`
(one input `n` / local 1, one state `i` / local 2), this gives a
single state var `i`.

Limitations / out of scope:
* multi-state-var loops emit a tuple state; the M12.1 fixture only
  exercises the single-state path
* loops with explicit `break value` (no fixture needs it yet)
* nested loops — the OCaml interpreter rejects them upstream
-/

namespace AeneasCheck.Translate

open AeneasCheck Raw Pure LLBCSharp

/-- M12.1: locate the `EvLoopInv` / `EvLoopEnd` markers in `evs`.
    Returns `(invIdx, endIdx, loopId, invariant)` for the FIRST loop
    in the event stream. Returns `none` if no loop is present.

    Nested loops aren't supported at the OCaml side, so we only ever
    expect one pair per function. -/
def findLoopBracket (evs : Array Event) :
    Option (Nat × Nat × Nat × StateSummary) := Id.run do
  let mut invIdx : Option Nat := none
  let mut endIdx : Option Nat := none
  let mut loopId : Nat := 0
  let mut invariant : StateSummary := default
  for i in [0:evs.size] do
    match evs[i]! with
    | .loopInv lid inv _ =>
      if invIdx.isNone then
        invIdx := some i
        loopId := lid
        invariant := inv
    | .loopEnd _ =>
      if invIdx.isSome && endIdx.isNone then
        endIdx := some i
    | _ => pure ()
  match invIdx, endIdx with
  | some iIdx, some eIdx => return some (iIdx, eIdx, loopId, invariant)
  | _, _ => return none

/-- Identify the loop's state-variable locals from its invariant.

    The OCaml side records the invariant as a list of `(local,
    symExpr)` pairs in `invariant.env`. A local is treated as a
    "loop state variable" when:
      * it is *not* an input parameter (local id > numParams), and
      * its current symbolic value is a `SymVal` (not a literal).

    For `count_to`: numParams=1, invariant.env = [(local 2, SymVal 6),
    (local 1, SymVal 0)] → state locals = [2]. -/
def inferStateLocals (numParams : Nat) (inv : StateSummary) : Array Nat :=
  inv.env.filterMap fun (l, se) =>
    if l > numParams then
      match se with
      | .symVal _ => some l
      | _ => none
    else none

/-- M12.1: name a loop's state-local. Mirrors the standard Aeneas
    backend's `i` / `i1` style — we use a single letter (`i`, `j`,
    `k`, …) per state slot to match the visible-output convention,
    falling back to `s<n>` for ≥4 state vars. -/
def stateName (idx : Nat) : String :=
  if idx = 0 then "i"
  else if idx = 1 then "j"
  else if idx = 2 then "k"
  else s!"s{idx}"

/-- M12.1 / M9.7o-E5b: pick a Pure type for a state local. The
    matching `LlbcFunDecl.localsTypes` carries the per-local
    structured `LlbcTy` (indexed by local id, 0 = return slot, 1..N =
    inputs, rest = temps); we look up the state local directly and
    translate to `PTy` via [llbcTyToPTyWithVars]. Falls back to `U32`
    when the local has no entry (shouldn't happen for a valid loop
    invariant on a function with a known body). -/
def stateLocalTy (tdm : TypeDeclMap) (typeParams : Array String)
    (lf : Raw.LlbcFunDecl) (local_ : Nat) : PTy :=
  match lf.localsTypes[local_]? with
  | some t => llbcTyToPTyWithVars tdm typeParams t
  | none => placeholderTy

/-- M12.1: locate the body's branch markers. The body events between
    `EvLoopInv` and `EvLoopEnd` have shape:
      [setup events] EvAssert(c, true) [continue body] EvAssert(c, false) [break body]
    Returns the indices of the two assert events (in the body's
    *relative* indexing — 0 = first body event). Returns `none` for
    unconditional loops (shouldn't appear in the M12.1 fixture). -/
def findBodyBranch (bodyEvs : Array Event) :
    Option (Nat × Nat × SymExpr) := Id.run do
  let mut trueIdx : Option Nat := none
  let mut trueCond : Option SymExpr := none
  for i in [0:bodyEvs.size] do
    match bodyEvs[i]! with
    | .assert c true =>
      if trueIdx.isNone then
        trueIdx := some i
        trueCond := some c
    | .assert c false =>
      match trueIdx, trueCond with
      | some tIdx, some tC =>
        -- The cond should match the opening assert's cond. The OCaml
        -- side uses the same SymVal id for the two markers; bail if
        -- they don't match (malformed cert).
        match c, tC with
        | .symVal a, .symVal b =>
          if a == b then return some (tIdx, i, tC)
        | _, _ => pure ()
      | _, _ => pure ()
    | _ => pure ()
  return none

/-- M12.1: build the `<fn>_loop.body` decl.

    Walks the body events between `EvLoopInv` and `EvLoopEnd`, using
    the parent function's parameter list (forwarded) plus the inferred
    state locals (threaded via `loop`). Returns `Result (ControlFlow
    stateTy retTy)`:
      * `cont <new state>` when the body's continue branch is taken
      * `done <break state>` when the body's break branch is taken

    For multi-state-var loops the state and continuation values are
    tuples; for single-state-var loops they are bare values. -/
def buildLoopBody (fnName : String) (typeParams : Array String)
    (numParams : Nat) (forwarded : Array Param)
    (stateLocals : Array Nat) (stateTys : Array PTy)
    (retTy : PTy)
    (bodyEvs : Array Event) (sourceSpan : Option Raw.SourceSpan) : Decl :=
  let stateNames : Array String :=
    stateLocals.mapIdx fun i _ => stateName i
  -- Body params: forwarded inputs, then state locals.
  let stateParams : Array Param :=
    stateNames.zip stateTys |>.map fun (n, t) => { name := n, ty := t }
  let bodyParams : Array Param := forwarded ++ stateParams
  -- Initial vm for the body walk: input local k ↦ forwarded[k]!.name
  -- (Session 7 Item 1d: read source name from the param record we were
  -- given instead of resynthesising via paramName), state local ↦ its
  -- dedicated state-var name.
  let initVm : VarMap := Id.run do
    let mut m : VarMap := {}
    for i in [0:numParams] do
      let nm := match forwarded[i]? with
        | some p => p.name
        | none => paramName (i + 1)
      m := m.insert (i + 1) (.var nm)
    for i in [0:stateLocals.size] do
      m := m.insert stateLocals[i]! (.var stateNames[i]!)
    return m
  -- Loop body's return type: ControlFlow stateTy retTy.
  let stateTy : PTy :=
    if stateTys.size = 1 then stateTys[0]!
    else .tuple stateTys
  let cfTy : PTy := .adt "ControlFlow" #[stateTy, retTy]
  -- Locate the branch markers.
  match findBodyBranch bodyEvs with
  | none =>
    -- Unconditional body (no break) — shouldn't happen for the M12.1
    -- fixture. Emit a placeholder so downstream consumers still get a
    -- well-typed decl.
    { name := s!"{innerName fnName}_loop.body"
      qualifiedName := s!"{fnName}::loop_body"
      params := bodyParams
      retTy := cfTy
      body := .ok (.app "cont" #[.var (stateNames.getD 0 "i")])
      sourceSpan
      typeParams
      attributes := #["rust_loop_body"]
      note := some "loop body: no branch detected; M12.1 only supports while-loops" }
  | some (tIdx, fIdx, cond) =>
    -- Pre-branch setup (events before tIdx): walk them as ordinary
    -- linear events to compute the loop condition. The condition's
    -- pure expression is whatever local most recently received it
    -- before tIdx — we recover it by inspecting walkSt.vm.
    let setupEvs := bodyEvs.extract 0 tIdx
    let setupSt : WalkState :=
      walkEvents setupEvs { vm := initVm, numParams }
    -- The cond's symExpr is `cond` (the opener's payload). Resolve
    -- it through the setup walk's vm. Most fixtures have the cond
    -- materialised as a binop into a fresh local (e.g. EvBinop Lt …
    -- → local 3); the simplest is to scan the setup walk for the
    -- last "binop into a Bool" event and pick its emitted name.
    -- M12.1: re-inline the condition's binop into the if's test
    -- expression. The setup walk pushed it as a fresh `let tN ← lhs
    -- op rhs` binding into setupSt.binds; we extract that binding,
    -- DROP it from setupSt.binds, and use its raw RHS as the cond
    -- expression. This matches the standard backend's
    --     if i < n then ...
    -- shape (no intermediate `let t0 ← i < n`). When the cond's
    -- binop isn't the last setup binding we fall back to using the
    -- binding's name as a variable reference, which keeps the
    -- emitted code well-typed even if uglier.
    let (condE, setupSt) : PExpr × WalkState := Id.run do
      match setupSt.binds.back? with
      | some (.regular nm (PExpr.app head args)) =>
        match head with
        | "Lt" | "Le" | "Gt" | "Ge" | "Eq" | "Ne" =>
          -- Inline the comparison binop. Drop the trailing binding;
          -- the cond expression now stands on its own.
          let trimmed := setupSt.binds.pop
          return (PExpr.app head args, { setupSt with binds := trimmed })
        | _ => return (PExpr.var nm, setupSt)
      | _ => return (lookupSymExpr setupSt.tdm setupSt.localTypes setupSt.vm cond, setupSt)
    -- Continue branch: events tIdx+1 .. fIdx-1.
    let contEvs := bodyEvs.extract (tIdx + 1) fIdx
    let contSt : WalkState :=
      walkEvents contEvs { setupSt with binds := #[] }
    -- Break branch: events fIdx+1 .. bodyEvs.size. (Typically empty.)
    let breakEvs := bodyEvs.extract (fIdx + 1) bodyEvs.size
    let breakSt : WalkState :=
      walkEvents breakEvs { setupSt with binds := #[], fresh := contSt.fresh }
    -- Build the continue tail: cont <state'> where state' is the
    -- updated value of each state-local in contSt.vm.
    let contValues : Array PExpr :=
      stateLocals.mapIdx fun i l =>
        contSt.vm.getD l (.var stateNames[i]!)
    let contTuple : PExpr :=
      if contValues.size = 1 then contValues[0]!
      else .tuple contValues
    let contTail : PExpr := .ok (.app "cont" #[contTuple])
    let thenBody := assembleBody contSt.binds contTail
    -- Build the break tail: done <ret>. The break payload is the
    -- function's intended forward return value; in the standard
    -- backend's `count_to`, that is the loop state at break time
    -- (which equals the unchanged state-local). For a multi-state
    -- loop, the standard backend returns a tuple; for `count_to`
    -- (single state, return == state), the break payload is bare.
    let breakValues : Array PExpr :=
      stateLocals.mapIdx fun i l =>
        breakSt.vm.getD l (.var stateNames[i]!)
    let breakPayload : PExpr :=
      if breakValues.size = 1 then breakValues[0]!
      else .tuple breakValues
    let breakTail : PExpr := .ok (.app "done" #[breakPayload])
    let elseBody := assembleBody breakSt.binds breakTail
    let ite : PExpr := .ifThenElse condE thenBody elseBody
    let body : PExpr := assembleBody setupSt.binds ite
    { name := s!"{innerName fnName}_loop.body"
      qualifiedName := s!"{fnName}::loop_body"
      params := bodyParams
      retTy := cfTy
      body
      sourceSpan
      typeParams
      attributes := #["rust_loop_body"] }

/-- M12.1: build the `<fn>_loop` wrapper decl. -/
def buildLoopWrapper (fnName : String) (typeParams : Array String)
    (forwarded : Array Param)
    (stateLocals : Array Nat) (stateTys : Array PTy)
    (retTy : PTy) (sourceSpan : Option Raw.SourceSpan) : Decl :=
  let stateNames : Array String :=
    stateLocals.mapIdx fun i _ => stateName i
  let stateParams : Array Param :=
    stateNames.zip stateTys |>.map fun (n, t) => { name := n, ty := t }
  let wrapperParams : Array Param := forwarded ++ stateParams
  -- Body: `loop (fun <state> => <fn>_loop.body <forwarded> <state>) <state>`
  let forwardedArgs : Array PExpr :=
    forwarded.map fun p => .var p.name
  let stateArg : PExpr :=
    if stateNames.size = 1 then .var stateNames[0]!
    else .tuple (stateNames.map fun n => .var n)
  let lambdaParam : String := stateNames.getD 0 "i1"
  -- Inside the lambda, the argument is the loop's *next* state; we
  -- pass it through to the body unchanged. For multi-state we'd need
  -- a let-destructure, deferred for now.
  let bodyCall : PExpr :=
    .app s!"{innerName fnName}_loop.body" (forwardedArgs ++ #[.var lambdaParam])
  let lam : PExpr :=
    .lam #[(lambdaParam, stateTys.getD 0 placeholderTy)] bodyCall
  let loopCall : PExpr := .app "loop" #[lam, stateArg]
  { name := s!"{innerName fnName}_loop"
    qualifiedName := s!"{fnName}::loop"
    params := wrapperParams
    retTy
    body := loopCall
    sourceSpan
    typeParams
    attributes := #["rust_loop"] }

/-- M12.1: build the top-level `<fn>` decl that calls the loop
    wrapper with the initial state. Walks pre-loop events to recover
    the initial state expression for each state local. -/
def buildTopLevelLoopFn (fnName : String) (typeParams : Array String)
    (numParams : Nat) (params : Array Param)
    (forwarded : Array Param)
    (stateLocals : Array Nat) (preLoopEvs : Array Event)
    (retTy : PTy) (sourceSpan : Option Raw.SourceSpan) : Decl :=
  -- Walk pre-loop events to learn the initial state expression for
  -- each state local. For `count_to` this is `EvAssign local 2 := 0`.
  let initVm : VarMap := Id.run do
    let mut m : VarMap := {}
    for i in [0:numParams] do
      -- Session 7 Item 1d: prefer the source name from `params`
      -- (which now flows through Forward.translateLoopFun's
      -- effectiveParamName) so the pre-loop walk's local refs match
      -- the user's identifiers.
      let nm := match params[i]? with
        | some p => p.name
        | none => paramName (i + 1)
      m := m.insert (i + 1) (.var nm)
    return m
  let preSt : WalkState :=
    walkEvents preLoopEvs { vm := initVm, numParams }
  -- Initial state for each state local.
  let stateInit : Array PExpr :=
    stateLocals.map fun l => preSt.vm.getD l (.lit (.scalar .u32 0))
  let forwardedArgs : Array PExpr :=
    forwarded.map fun p => .var p.name
  -- Build the call. Single state: `<fn>_loop <forwarded> <init>`.
  -- Multi state: pass each state arg in position order; the wrapper
  -- splits at the lambda level.
  let callArgs : Array PExpr := forwardedArgs ++ stateInit
  let body : PExpr := .app s!"{innerName fnName}_loop" callArgs
  { name := innerName fnName
    qualifiedName := fnName
    params, retTy, body
    sourceSpan
    typeParams
    attributes := #["reducible"] }

/-- M12.1 / M9.7o-E5b: translate a function whose cert contains a
    loop. Sources signature + per-local types from the matching
    structured `LlbcFunDecl` (threaded by the Driver). Emits three
    decls: the body, the wrapper, and the top-level function.

    Zero-Skip Step 5 (cluster `loop_body_undefined_locals`): the
    `tdm` parameter is now threaded from the Driver so input / output
    types that reference an ADT id resolve to the structured
    `.adt name args` shape (e.g. `&CList<T>` → `CList T`) instead of
    the catch-all `Std.U32` placeholder. -/
def translateLoopFun (tdm : TypeDeclMap) (f : Raw.FunCert)
    (lf : Raw.LlbcFunDecl) : Option (Array Decl) := do
  let (invIdx, endIdx, _loopId, inv) ← findLoopBracket f.events
  let lsig := lf.signature
  let typeParams := lsig.generics.types
  let numParams := lsig.inputs.size
  -- Session 7 Item 1d: mirror translateFunWith's effectiveParamName.
  let effectiveParamName (i : Nat) : String :=
    match lf.localsNames[i + 1]? with
    | some (some n) => n
    | _ => paramName (i + 1)
  let params : Array Param :=
    (List.range numParams).toArray.map fun i =>
      let ty := match lsig.inputs[i]? with
        | some t => llbcTyToPTyWithVars tdm typeParams t
        | none => placeholderTy
      { name := effectiveParamName i, ty }
  let retTy : PTy := llbcTyToPTyWithVars tdm typeParams lsig.output
  let stateLocals := inferStateLocals numParams inv
  let bodyEvs := f.events.extract (invIdx + 1) endIdx
  let stateTys : Array PTy :=
    stateLocals.map fun l => stateLocalTy tdm typeParams lf l
  let preLoopEvs := f.events.extract 0 invIdx
  let bodyDecl :=
    buildLoopBody f.fnName typeParams numParams params stateLocals stateTys
      retTy bodyEvs f.sourceSpan
  let wrapperDecl :=
    buildLoopWrapper f.fnName typeParams params stateLocals stateTys retTy
      f.sourceSpan
  let topDecl :=
    buildTopLevelLoopFn f.fnName typeParams numParams params params stateLocals
      preLoopEvs retTy f.sourceSpan
  return #[bodyDecl, wrapperDecl, topDecl]

end AeneasCheck.Translate
