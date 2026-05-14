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

/-- Walk state: accumulated `let` bindings (in monadic order) plus
    the current per-local pure expression map. -/
structure WalkState where
  binds : Array (String × PExpr) := #[]
  vm : VarMap := {}
  /-- Counter for fresh `tN` names. -/
  fresh : Nat := 0
  /-- The local id last written by a value-producing event (binop,
      assign, copy/move target). Used as a fallback return value for
      functions whose mutation flows through a `&mut` input — the
      "result" is whatever was most recently computed before the
      `EvReturn`. M10.2's backward-function pass will replace this
      with an exact post-state per-borrow read. -/
  lastWrite : Option Nat := none
  deriving Inhabited

namespace WalkState

def freshName (st : WalkState) : String × WalkState :=
  let nm := s!"t{st.fresh}"
  (nm, { st with fresh := st.fresh + 1 })

end WalkState

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
  | .call _ _ fnName args dst _ =>
    -- M10.1: forward call. Build `Pure.App fnName [argE1, …, argEn]`,
    -- emit a `let tN ← …` binding, and update the destination
    -- local's pure value. Backward functions / region abstractions
    -- are handled by M10.2 in tandem with EndAbs / Proj.
    let argEs := args.map (lookupSymExpr st.vm)
    let app : PExpr := .app fnName argEs
    let (nm, st) := st.freshName
    { st with
      binds := st.binds.push (nm, app)
      vm := st.vm.insert dst.local_ (.var nm)
      lastWrite := some dst.local_ }
  -- Out-of-M10.1 events: leave the state untouched. The replayer
  -- already rejected them upstream; this branch keeps `walkEvent`
  -- total.
  | .endAbs _ _ | .proj _ _ _
  | .join _ _ _ | .loopInv _ _ => st

/-- Wrap a tail value in `ok` *only* when it is a pure (non-Result)
    expression. Binops emit `Result α`-typed apps already; double-
    wrapping them would change semantics. -/
def tailToResult (e : PExpr) : PExpr :=
  match e with
  | .app _ _ => e  -- Already monadic — binops are Result-typed.
  | _ => .ok e

/-- Fold the accumulated bindings around a tail expression to form a
    nested `do let … ← …; …` chain. -/
def assembleBody (binds : Array (String × PExpr)) (tail : PExpr) : PExpr :=
  -- Simplification: if there is exactly one binding and the tail is
  -- just `ok (.var name)` for that name, drop the let and use the
  -- bound expression directly (it already returns Result α). This
  -- matches the standard backend's body shape for tiny functions
  -- like `incr` (`x + 1#u32`).
  match binds.toList, tail with
  | [(nm, e)], .ok (.var n) =>
    if nm == n then e else binds.foldr (init := tail) (fun (n, e) acc =>
      .letIn n placeholderTy e acc)
  | _, _ =>
    binds.foldr (init := tail) (fun (n, e) acc =>
      .letIn n placeholderTy e acc)

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
      { name := paramName (i + 1), ty := placeholderTy }
  -- Initial var map: input local 1 ↦ x1, local 2 ↦ x2, ...
  let initVm : VarMap := Id.run do
    let mut m : VarMap := {}
    for i in [0:numParams] do
      m := m.insert (i + 1) (.var (paramName (i + 1)))
    return m
  let finalSt : WalkState :=
    f.events.foldl (init := { vm := initVm }) walkEvent
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
  let body : PExpr := assembleBody finalSt.binds (tailToResult tailE)
  { name := innerName f.fnName
    qualifiedName := f.fnName
    params, retTy := placeholderTy, body
    sourceSpan := f.sourceSpan }

end AeneasCheck.Translate
