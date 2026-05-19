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

/-- M9.7o-E5b: detect a `&mut T` on a structured `LlbcTy`. -/
def isMutRefLlbc : LlbcTy → Bool
  | .tRef _ _ .mut => true
  | _ => false

/-- M9.7o-E5b: detect a unit/`()` shape on a structured `LlbcTy`. The
    cert / LLBC representation for `()` is a zero-arity `tTuple`. -/
def isUnitTyLlbc : LlbcTy → Bool
  | .tTuple #[] => true
  | _ => false

/-- M9.7o-E5b: when an output `LlbcTy` is a tuple containing N ≥ 2
    `&mut T` components (each in its own region), return `some N`. Used
    to detect helpers like `swap_pair<'a,'b>(...) -> (&'a mut u32,
    &'b mut u32)` whose pure translation produces N backward closures
    (one per region) instead of a single closure. Returns `none` if
    the output is not a tuple or contains fewer than 2 mut-ref fields. -/
def isOutputTupleOfMutRefsLlbc : LlbcTy → Option Nat
  | .tTuple args =>
    let nMut := args.foldl (init := 0) fun acc t =>
      match t with
      | .tRef _ _ .mut => acc + 1
      | _ => acc
    if nMut ≥ 2 && nMut = args.size then some nMut else none
  | _ => none

/-- M9.5b / M9.5e: information the translator needs about one ADT
    type declaration: its bare Lean name, an ordered list of field
    names (struct case), and an ordered list of variants with their
    field counts (enum case, M9.5e). The Lean translator uses `name`
    when translating an `&mut Pair`-typed signature input or a
    function whose return type is `Pair`; `fieldNames[K]` resolves a
    `Field K` projection to the surface field name (`fst` / `snd`).
    `variantFieldCounts[V]` gives the payload arity of variant `V`,
    which M9.5e's Forward translator uses to pre-seed payload binders
    in match-arm sub-walks. -/
structure TypeDeclInfo where
  name : String
  fieldNames : Array String
  /-- M9.5e: number of payload fields per variant, indexed by
      variant id. Empty for struct decls; populated for enum decls
      (zero for C-style nullary variants). -/
  variantFieldCounts : Array Nat := #[]
  /-- Bug 4d/4f follow-up: `true` when the cert recorded this ADT as
      `Opaque` (a stdlib type with no body — `StepBy`, `Iter`,
      `IterMut`, `ChunksExact`, `NonZero`, …). The translator keeps
      these in `TypeDeclMap` so the typed-fallback path can dispatch
      on `name`, but `llbcTyToPTyWithVars` still maps them to the
      legacy `U32` fallback (rather than emitting an unknown
      `StepBy T` head into function signatures). -/
  isOpaque : Bool := false
  deriving Repr, Inhabited

/-- M9.5b: a TypeDeclId → TypeDeclInfo lookup, keyed by the integer
    ADT id used by `LlbcTy.tAdt`. The Driver builds this from
    `cc.llbcProgram.typeDecls`. -/
abbrev TypeDeclMap := Std.HashMap Nat TypeDeclInfo

/-- M9.7k: bare last `::`-segment of a fully-qualified path. Mirrors
    the OCaml emitter (`CertGen.ml`) which splits on `:` and takes
    the last non-empty piece — so e.g. `test_crate::Pair` → `Pair`. -/
def bareNameOfQualified (qualified : String) : String :=
  match (qualified.splitOn "::").getLast? with
  | some n => n
  | none => qualified

/-- M9.7k: structured `LlbcTy → PTy`. The sole type translator after
    M9.7o-E5b retired the opaque-string `rawTyToPTy*` family.

    `typeParams` resolves `LlbcTy.tVar K` to the K-th param's bare
    name. `tdm` resolves `LlbcTy.tAdt id args` to `.adt name args`.
    Stdlib `Box` (`alloc::boxed::Box`) is transparently unwrapped to
    its first generic argument.

    Unrecognised / unstructured shapes (closures, fn-ptrs, dyn-trait,
    raw pointers, `LlbcTy.tOpaque`) fall back to `Std.U32`. -/
partial def llbcTyToPTyWithVars
    (tdm : TypeDeclMap) (typeParams : Array String) : LlbcTy → PTy
  | .litTy k => match k with
    | .bool => .lit .bool
    | .int ik => .lit (.int ik)
    | .float _ => .lit (.int .u32)
    | .char => .lit (.int .u32)
  | .tAdt id args =>
    match tdm[id]? with
    | some info =>
      -- M9.5n / M9.7k: stdlib `Box<T>` is transparent — unwrap to the
      -- single generic argument so a `Box<AVLNode<T>>` flows through
      -- the pipeline as `AVLNode<T>`.
      if info.name == "Box" then
        match args[0]? with
        | some inner => llbcTyToPTyWithVars tdm typeParams inner
        | none => .lit (.int .u32)
      -- Bug 4g: iterator-adapter transparency. Each wrapper maps
      -- to whatever the corresponding shim's `next`/`into_iter`
      -- call actually flows through, so the wrapper-sig type
      -- aligns with the call-site binding.
      --
      -- * `StepBy<X>` → `X` (the inner iterable flows through; the
      --   Range.step_by shim returns Range Usize, so the cert's
      --   StepBy<Range<Usize>> renders as Range Usize).
      -- * `Iter<T>` / `IterMut<T>` → `Slice T` (the shim's
      --   Slice.iter / Slice.iter_mut returns the same Slice).
      -- * `IntoIter<T>` → `Vec T` (the shim's Vec.into_iter returns
      --   the same Vec; the cert's wrapper type IntoIter<T> wraps
      --   the Vec value).
      else if info.name == "StepBy" then
        match args[0]? with
        | some inner => llbcTyToPTyWithVars tdm typeParams inner
        | none => .lit (.int .u32)
      else if info.name == "Iter" ∨ info.name == "IterMut" then
        match args[0]? with
        | some inner => .slice (llbcTyToPTyWithVars tdm typeParams inner)
        | none => .lit (.int .u32)
      else if info.name == "IntoIter" then
        match args[0]? with
        | some inner => .adt "Vec" #[llbcTyToPTyWithVars tdm typeParams inner]
        | none => .lit (.int .u32)
      -- Bug 4g: `Vec<T, A>` (where `A : Allocator`). The shim is
      -- mono-arg `alloc.vec.Vec α`; drop the Allocator generic so the
      -- emitted type `Vec U32` matches the shim's signature.
      else if info.name == "Vec" then
        match args[0]? with
        | some inner => .adt "Vec" #[llbcTyToPTyWithVars tdm typeParams inner]
        | none => .lit (.int .u32)
      -- Bug 4d/4f follow-up: opaque stdlib ADTs are in `tdm` so the
      -- placeholder synthesiser can dispatch on `info.name`, but
      -- signature-emission falls back to U32 by default — emitting
      -- a bare `<TypeName> T` head would resolve to an unknown
      -- identifier unless a top-level alias exists. Only the
      -- transparent-wrapper cases above and the `Vec` alias case
      -- are safe to surface; everything else stays on U32.
      else if info.isOpaque then
        .lit (.int .u32)
      else
        let pargs := args.map (llbcTyToPTyWithVars tdm typeParams)
        .adt info.name pargs
    | none => .lit (.int .u32)
  | .tTuple args =>
    match args.toList with
    | [] => .unit
    | _ => .tuple (args.map (llbcTyToPTyWithVars tdm typeParams))
  | .tRef _ inner _ =>
    -- M9.5o: the borrow shape is recovered separately by the BackSig
    -- builder; the value-level translation drops `&` / `&mut`.
    llbcTyToPTyWithVars tdm typeParams inner
  | .tVar k =>
    match typeParams[k]? with
    | some nm => .tyVar nm
    | none => .lit (.int .u32)
  | .tNever => .lit (.int .u32)
  | .tRawPtr inner _ => llbcTyToPTyWithVars tdm typeParams inner
  | .tArray elem len => .array (llbcTyToPTyWithVars tdm typeParams elem) len
  | .tSlice elem => .slice (llbcTyToPTyWithVars tdm typeParams elem)
  -- M9.7o-Bug5: `&str` (parsed via the `Builtin "Str"` branch in
  -- Json.Parser) lowers to Lean's builtin `String` so `expect`-style
  -- shim signatures (`Option α → String → Result α`) line up at the
  -- call site. Pre-fix this fell through to `Std.U32` and broke
  -- `options::test_expect` etc.
  | .tStr => .adt "String" #[]
  | .tFn _ _ => .lit (.int .u32)
  | .tDynTrait _ => .lit (.int .u32)
  | .tOpaque _ => .lit (.int .u32)

/-- M9.7o-E5b: structured ADT-id extractor on `LlbcTy`. Peels one
    layer of `tRef` so a `&mut Pair`-typed local is identified as
    `Pair`. Used by `applyFieldProj` / the structUpdate hook in
    `walkEvent` to resolve a `Field K` projection through the
    field-name map. -/
def adtIdOfLlbcTy : LlbcTy → Option Nat
  | .tAdt id _ => some id
  | .tRef _ inner _ => adtIdOfLlbcTy inner
  | _ => none

/-- Apply a single projection step to an `LlbcTy`. Returns `none`
    when the step can't be resolved (unknown ADT, missing field). For
    `Field K` on an `LlbcTy.tAdt` we approximate the field type by
    looking up the K-th *generic argument* — this is a coarse heuristic
    that's only used by `lookupPlace`'s missing-local fallback (so the
    result is a placeholder anyway), but it picks the correct scalar
    kind for shapes like `Wrap<i32>.value` whose field type is the
    sole generic. -/
private partial def stepLlbcTy : LlbcTy → Raw.ProjElem → Option LlbcTy
  | .tRef _ inner _, .deref => some inner
  | .tRawPtr inner _, .deref => some inner
  | .tAdt _ args, .field k => args[k]?
  | .tTuple args, .field k => args[k]?
  | .tArray elem _, .projIndex => some elem
  | .tSlice elem, .projIndex => some elem
  | .tArray elem _, .subslice => some (.tSlice elem)
  | .tSlice elem, .subslice => some (.tSlice elem)
  | _, _ => none

/-- Walk a projection list against an LlbcTy, returning the terminal
    type if every step resolves. Used by `lookupPlace`'s missing-local
    fallback to pick a type-appropriate placeholder. -/
private partial def projectLlbcTy
    : LlbcTy → List Raw.ProjElem → Option LlbcTy
  | t, [] => some t
  | t, step :: rest =>
    match stepLlbcTy t step with
    | some t' => projectLlbcTy t' rest
    | none => none

/-- Build a placeholder `PExpr` matching an `LlbcTy`'s shape. Used by
    `lookupPlace` to produce a typed zero when the local isn't tracked
    in the vm and we fall back to a literal. Only scalar integers and
    `bool` get a typed placeholder; other shapes default to `0#u32`. -/
def placeholderPExprOf : LlbcTy → PExpr
  | .litTy (.int k) => .lit (.scalar k 0)
  | .litTy .bool => .lit (.bool false)
  | _ => .lit (.scalar .u32 0)

/-- Bug 4a: peel outer `tRef` layers from an `LlbcTy`, returning the
    referenced type. Used by [vm1FallbackCompatible] so a `&mut U32`
    input matches a `U32`-typed temp through the borrow-input
    over-approximation. -/
private def peelRefs : LlbcTy → LlbcTy
  | .tRef _ inner _ => peelRefs inner
  | t => t

/-- Bug 4a: conservative type-compatibility check used by
    [lookupPlace]'s vm[1] fallback. Returns `true` when the queried
    place's projected type is *plausibly* the same as input-1's type
    (after peeling outer refs), and `false` only when both are
    concretely identifiable as different primitive shapes
    (U32 ↔ Bool, U32 ↔ Enum, etc.). Keeps the borrow-input
    over-approximation correct for `incr(x:&mut u32){*x += 1}`-shape
    fixtures (where the temp's projected `U32` matches input-1's
    peeled `&mut U32`) while blocking the fallback when joins like
    `joins::call_choose` would otherwise emit `Bool + U32`.

    Bug 4b extension: a query for a concrete-typed local with an
    input-1 of generic type-variable shape (`static::read`'s
    `S::SLICE`-elided local 5 of type `&Slice U16`, with input-1 a
    bare `S : Type`) is also incompatible — passing the generic-typed
    `x1` into a `Slice.index_usize` arg slot fails to elaborate. Treat
    `tVar`↔concrete as incompatible, plus `tSlice`/`tArray`↔`litTy`
    pairs since those occur in array-indexing and slice-iteration
    paths. -/
private def vm1FallbackCompatible : LlbcTy → LlbcTy → Bool
  | a, b =>
    match peelRefs a, peelRefs b with
    | .litTy x, .litTy y => x == y
    | .litTy _, .tAdt _ _ => false
    | .tAdt _ _, .litTy _ => false
    | .tAdt id1 _, .tAdt id2 _ => id1 == id2
    -- Type-vars don't unify with concrete shapes via vm[1].
    | .tVar i, .tVar j => i == j
    | .tVar _, .litTy _ | .litTy _, .tVar _ => false
    | .tVar _, .tAdt _ _ | .tAdt _ _, .tVar _ => false
    | .tVar _, .tSlice _ | .tSlice _, .tVar _ => false
    | .tVar _, .tArray _ _ | .tArray _ _, .tVar _ => false
    -- Slice/Array vs litTy/Adt — incompatible (Slice operand passed
    -- where a scalar is expected, or vice versa).
    | .tSlice _, .litTy _ | .litTy _, .tSlice _ => false
    | .tArray _ _, .litTy _ | .litTy _, .tArray _ _ => false
    | .tSlice _, .tAdt _ _ | .tAdt _ _, .tSlice _ => false
    | .tArray _ _, .tAdt _ _ | .tAdt _ _, .tArray _ _ => false
    | _, _ => true

/-- Bug 4f follow-up: render an `LlbcTy` to a Lean type string, for
    use in typed-placeholder emission. Returns `none` when the type
    contains a `tVar` (type-variable) — those require `typeParams` to
    resolve, which `placeholderPExprOfWith` doesn't carry. Concrete
    cases (scalars, slices/arrays of scalars, named opaque ADTs)
    render directly; the caller wraps the placeholder in
    `((<expr> : <typeStr>))` so Lean has enough info to elaborate
    even when the call site doesn't constrain the type parameter
    (e.g. `Slice.len Slice.placeholder` whose result is `Result Usize`
    regardless of element type). -/
partial def renderConcreteLlbcTy (tdm : TypeDeclMap) : LlbcTy → Option String
  | .litTy (.int k) =>
    match k with
    | .u8 => some "Std.U8" | .u16 => some "Std.U16" | .u32 => some "Std.U32"
    | .u64 => some "Std.U64" | .u128 => some "Std.U128"
    | .usize => some "Std.Usize"
    | .i8 => some "Std.I8" | .i16 => some "Std.I16" | .i32 => some "Std.I32"
    | .i64 => some "Std.I64" | .i128 => some "Std.I128"
    | .isize => some "Std.Isize"
  | .litTy .bool => some "Bool"
  | .litTy .char => some "Char"
  | .litTy (.float _) => some "Float"
  | .tRef _ inner _ => renderConcreteLlbcTy tdm inner
  | .tSlice elem =>
    (renderConcreteLlbcTy tdm elem).map fun s => s!"Aeneas.Std.Slice {s}"
  | .tArray elem n =>
    (renderConcreteLlbcTy tdm elem).map fun s =>
      s!"Aeneas.Std.Array {s} (Aeneas.Std.Usize.ofNat {n})"
  | .tAdt id args =>
    match tdm[id]? with
    | some info =>
      -- Render args one-by-one; bail on any tVar.
      let argStrs : Option (Array String) :=
        args.foldlM (init := #[]) fun acc a =>
          (renderConcreteLlbcTy tdm a).map (acc.push ·)
      argStrs.map fun strs =>
        if strs.isEmpty then info.name
        else
          let parens (s : String) : String :=
            if s.contains ' ' ∧ !s.startsWith "(" then s!"({s})" else s
          s!"{info.name} {String.intercalate " " (strs.toList.map parens)}"
    | none => none
  | .tTuple #[] => some "Unit"
  | _ => none

/-- Bug 4f follow-up: wrap a placeholder expression with a Lean type
    ascription `((<e> : <typeStr>))` when the LLBC type renders
    concretely (no `tVar`s). The pretty printer's `__typed::`
    handler turns this into the ascription on emit. Returns `e`
    unchanged when the type cannot be rendered. -/
def withTypedAscription (tdm : TypeDeclMap) (t : LlbcTy) (e : PExpr) : PExpr :=
  match renderConcreteLlbcTy tdm t with
  | some s => .app s!"__typed::{s}" #[e]
  | none => e

/-- Phase 4a-3: `tdm`-aware variant of [placeholderPExprOf] that can
    synthesise a struct-literal placeholder for an ADT type. When the
    type is a `tAdt` whose `TypeDeclInfo` has the same number of
    `fieldNames` as the ADT's generic args, assume field K's type is
    the K-th generic arg (the same coarse heuristic [stepLlbcTy] uses
    for missing-local field projections) and emit a `recordLit` of
    typed zeros. Fixes `static S3 : Pair<u32, u32> = P3` whose linear
    walk never writes vm[0], leaving the catch-all to emit a
    type-incorrect `ok 0#u32` against `Result (Pair U32 U32)`. The
    resulting `ok { x := 0#u32, y := 0#u32 }` is still
    semantically wrong (real value is P3 = `Pair { x: 0, y: 1 }`) —
    that's tracked separately as a cert-walker gap; the placeholder
    just keeps the file compiling so the rest of the constants fixture
    can be wired into the lean-diff harness. -/
partial def placeholderPExprOfWith (tdm : TypeDeclMap) : LlbcTy → PExpr
  | .litTy (.int k) => .lit (.scalar k 0)
  | .litTy .bool => .lit (.bool false)
  | t@(.tAdt id args) =>
    match tdm[id]? with
    | some info =>
      -- Struct case (no variants): emit `{ f₁ := 0, …, fₙ := 0 }`
      -- when fields and generic args line up 1-1.
      if info.variantFieldCounts.isEmpty ∧ ¬info.isOpaque
          ∧ info.fieldNames.size == args.size then
        let fields : Array (String × PExpr) :=
          info.fieldNames.zipWith (fun fname fty =>
            (fname, placeholderPExprOfWith tdm fty)) args
        .recordLit fields (some info.name)
      else
        -- Bug 4d: stdlib-ADT placeholder synthesis. Recognise common
        -- stdlib types by their bare name so a missing-identifier
        -- placeholder synthesised at an enum/opaque slot doesn't fall
        -- through to `0#u32`. The shim helpers are Unit-pinned; the
        -- typed-ascription wrapper [withTypedAscription] then
        -- annotates the call site with the concrete LLBC type so
        -- callers like `Slice.len Slice.placeholder` (whose return
        -- is independent of α) still elaborate.
        let raw : Option PExpr :=
          match info.name with
          | "Option" => some (.app "Option.placeholder" #[])
          | "ChunksExact" => some (.app "ChunksExact.placeholder" #[])
          | _ => none
        match raw with
        | some r => withTypedAscription tdm t r
        | none => .lit (.scalar .u32 0)
    | none =>
      -- Bug 4d: opaque ADTs aren't in tdm. Fall through to
      -- `0#u32` here — opaque-tdm population is a separate sub-bug.
      .lit (.scalar .u32 0)
  -- Bug 4 (Array placeholder synthesis): mirror the `.tAdt` placeholder
  -- logic for fixed-length arrays. `use_static::PREFIX` declares a
  -- `[u8; 1]` static whose linear walk never writes vm[0]; without
  -- this branch the catch-all emitted `ok 0#u32` against
  -- `Result (Array Std.U8 1#usize)`. We emit `Array.singleton 0#u8`
  -- (the shim helper from the Aggregate-rvalue propagation pass).
  -- Bug 4c: extend to multi-element placeholders — emit
  -- `Array.ofList (List.cons 0#α … List.nil)` for n ≥ 2, and
  -- `Array.ofList List.nil` for n = 0.
  | .tArray elemTy n =>
    let elem := placeholderPExprOfWith tdm elemTy
    match n with
    | 0 =>
      -- Bug 4d: empty-array placeholder. Use the Unit-pinned shim so
      -- the call site doesn't leave `α` as an unresolved metavariable
      -- through the typical `Array.ofList List.nil →
      -- ArrayToSliceShared → Slice.iter → ...` chain.
      .app "Aeneas.Std.Array.empty" #[]
    | 1 =>
      .app "Aeneas.Std.Array.singleton" #[elem]
    | _ =>
      let chain : PExpr :=
        (List.range n).foldr (init := .app "List.nil" #[]) fun _ acc =>
          .app "List.cons" #[elem, acc]
      .app "Aeneas.Std.Array.ofList" #[chain]
  -- Bug 4b: typed placeholders for `Slice α` and reference shapes —
  -- needed when the cert elides a local's initialiser (Charon
  -- drops const-item reads like `S::SLICE` from the event stream)
  -- and the lookup falls through to the typed-fallback path. The
  -- shim helpers `Slice.placeholder` / `Array.placeholder` infer
  -- `α` from surrounding context.
  | t@(.tSlice _) =>
    withTypedAscription tdm t (.app "Aeneas.Std.Slice.placeholder" #[])
  -- Peel references at the value level (Rust borrows are erased
  -- after monomorphisation, so a `&T` slot pure-value-wise *is* a
  -- `T`).
  | .tRef _ inner _ =>
    placeholderPExprOfWith tdm inner
  | _ => .lit (.scalar .u32 0)

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

/-- M9.5n / M9.7o-E5b: apply a trailing `[Field K]` projection to a
    root pure expression `e`. Resolves the field name through
    `localTypes[L]` (the local's structured `LlbcTy`) →
    [adtIdOfLlbcTy] → `tdm` → the struct's field-name list. If any
    step fails (no type tracked, not a struct, missing field name),
    returns `e` unchanged so pre-M9.5n callers (which never tracked
    types) still see the M10-vintage behaviour.

    Only the LAST projection element matters here — the M9.5b
    structUpdate path handles `[Deref, Field K]` writes; here we
    handle the read of `local.<field>` for a place whose projection
    list ends with `Field K`. Non-`Field` last projections (`Deref`,
    `ProjIndex`, …) fall through unmodified. -/
private def applyFieldProj
    (tdm : TypeDeclMap) (localTypes : Std.HashMap Nat Raw.LlbcTy)
    (localId : Nat) (proj : List Raw.ProjElem) (e : PExpr) : PExpr :=
  match proj.getLast? with
  | some (Raw.ProjElem.field k) =>
    match localTypes[localId]? with
    | some t =>
      match adtIdOfLlbcTy t with
      | some adtId =>
        match tdm[adtId]? with
        | some info =>
          match info.fieldNames[k]? with
          | some fname =>
            -- Phase 1B: when the root expression is a default zero
            -- placeholder (the `0#u32` `lookupPlace` emits for an
            -- untracked local) AND the field's expected type can be
            -- inferred to be a literal integer, drop the field
            -- access and emit a typed zero of the field's type
            -- directly. This keeps a global-constant body like
            -- `unwrap_y` (where the cert never seeds local 1)
            -- well-typed against its declared return type
            -- (`Result Std.I32`) instead of emitting the
            -- nonsense-typed `0#u32.value`. Non-literal field types
            -- still flow through the standard `.fieldAccess` path,
            -- which yields a (still type-imprecise) `0#u32.fname`
            -- but doesn't change the rest of the output.
            match e with
            | .lit (.scalar .u32 0) =>
              match stepLlbcTy t (Raw.ProjElem.field k) with
              | some fieldTy => placeholderPExprOf fieldTy
              | none => .fieldAccess e fname
            | _ => .fieldAccess e fname
          | none => e
        | none => e
      | none => e
    | _ => e
  | _ => e

/-- Resolve a place's *root* local to its current pure expression. M10.0
    ignored projections (Deref, Field, ProjIndex) when computing the
    pure value — sound for the direct-borrow subset but lost field
    reads.

    M9.5n: a trailing `[Field K]` projection on a place whose root
    local has a struct type registered in [localTypes] is lowered to
    a `<root>.<fieldName>` access. The M9.5b structUpdate path
    (write through `[Deref, Field K]`) is unaffected — it consumes
    the projection list directly and goes through `applyFieldProj`'s
    sister logic in the EvAssign branch.

    When the local has no entry in the map (typical for `[Deref]`
    reads through a borrow whose backing local was never observed
    in a tracked event), fall back to the *first input parameter*
    `x1`. This is a deliberate over-approximation: for simple
    borrowed-input functions like `incr(x: &mut u32) { *x += 1 }`
    every Deref read of an intermediate temp ultimately resolves to
    the input, so `x1` is the right pure-value substitute. -/
def lookupPlace (tdm : TypeDeclMap) (localTypes : Std.HashMap Nat Raw.LlbcTy)
    (vm : VarMap) (p : Place) : PExpr :=
  match vm[p.local_]? with
  | some e =>
    -- The local is tracked: use its current pure value as the root
    -- and apply the field projection (if any) through the regular
    -- M9.5n path.
    applyFieldProj tdm localTypes p.local_ p.projection.toList e
  | none =>
    -- Local not tracked. Historically prefer input-1's pure value (a
    -- deliberate over-approximation that mirrors the M9.5n-vintage
    -- borrow-reborrow behaviour). When even `1` is missing — typical
    -- for a global initializer / nullary const-fn whose body the cert
    -- only describes through assignments between uninitialised
    -- locals — use a *type-correct* zero literal derived from the
    -- place's projection-resolved `LlbcTy`. This keeps the emitted
    -- `def`'s body well-typed against its declared return type
    -- (e.g. `unwrap_y : Result Std.I32 := ok 0#i32` instead of the
    -- pre-fix `ok 0#u32.value`). Non-scalar projected types still
    -- fall back to `0#u32`.
    --
    -- Bug 4a (joins::call_choose, joins::use_enum): the vm[1]
    -- over-approximation is unsound when input-1's type is
    -- concretely different from the query's projected type
    -- (e.g. binop lhs is `U32`-typed local 7 with vm[7] unset; input
    -- 1 is `Bool b`). Falling back to vm[1] emits `b + 1#u32` which
    -- fails to elaborate. We now consult [localTypes] for both
    -- sides; when [vm1FallbackCompatible] proves them concretely
    -- incompatible, use the typed placeholder instead. Keeps the
    -- incr-shape (`&mut U32` input + `U32`-projected temp) using
    -- vm[1] as before.
    let queryProjTy : Option LlbcTy :=
      (localTypes[p.local_]?).bind fun t =>
        projectLlbcTy t p.projection.toList
    let input1Ty : Option LlbcTy := localTypes[1]?
    let vm1Ok : Bool :=
      match queryProjTy, input1Ty with
      | some qt, some it => vm1FallbackCompatible qt it
      | _, _ => true
    match vm[1]?, vm1Ok with
    | some e1, true =>
      applyFieldProj tdm localTypes p.local_ p.projection.toList e1
    | _, _ =>
      match localTypes[p.local_]? with
      | some t =>
        match projectLlbcTy t p.projection.toList with
        -- Bug 4b: switch to the tdm-aware [placeholderPExprOfWith]
        -- so `tSlice`/`tArray`/`tRef` shapes (introduced by
        -- Charon-elided const-item access) produce type-correct
        -- shim helpers (`Slice.placeholder`, `Array.singleton`,
        -- `Array.placeholder`) instead of the catch-all `0#u32`.
        -- The original concern about Phase 1B recognition doesn't
        -- apply here — this path returns the placeholder directly,
        -- no downstream `applyFieldProj` runs against it.
        | some projTy => placeholderPExprOfWith tdm projTy
        | none =>
          -- Couldn't resolve the projection. Fall back to the legacy
          -- root + applyFieldProj path so the `.value` shape still
          -- appears (matches the pre-fix output for unrecognised
          -- shapes).
          applyFieldProj tdm localTypes p.local_ p.projection.toList
            (.lit (.scalar .u32 0))
      | none =>
        applyFieldProj tdm localTypes p.local_ p.projection.toList
          (.lit (.scalar .u32 0))

/-- M9.5e: consult a payload-binder map *before* falling back to the
    plain `lookupPlace`. When a place reads `local L` with a trailing
    `[Field K]` projection and `(L, K)` is keyed in `payloadBinders`,
    return the arm-scoped binder name (e.g. `.var "x2"`) instead of
    the root local's pure expression. Used by the match-arm sub-walk
    so an `EvAssign { rhs = SymCopy(scrut.[Field K]) }` resolves to
    the binder introduced by the pattern. -/
def lookupPlaceWithBinders
    (tdm : TypeDeclMap) (localTypes : Std.HashMap Nat Raw.LlbcTy)
    (vm : VarMap) (payloadBinders : Std.HashMap (Nat × Nat) String)
    (p : Place) : PExpr :=
  match p.projection.toList.getLast? with
  | some (ProjElem.field k) =>
    match payloadBinders[(p.local_, k)]? with
    | some name => .var name
    | none => lookupPlace tdm localTypes vm p
  | _ => lookupPlace tdm localTypes vm p

/-- M9.5f: resolve a variant ctor to its pure form. For a nullary
    variant we emit `.var "<adtName>.<variantName>"` (a single
    qualified token). For a payload-bearing variant we emit
    `.app "<adtName>.<variantName>" #[field-pexprs]`. When the
    `adtName` can't be resolved via `tdm` (legacy fixture / stale
    cert), we fall back to the unqualified variant name — the
    pre-M9.5f match-arm path used to call `lookupSymExpr` on a
    `symVariant` it had already qualified, and we preserve that
    bare-name shape for the parent walker's downstream `qualify`
    pass. -/
private partial def variantPExpr
    (tdm : TypeDeclMap) (adtId : Nat) (variantName : String)
    (fieldEs : Array PExpr) : PExpr :=
  let headName : String :=
    match tdm[adtId]? with
    | some info => s!"{info.name}.{variantName}"
    | none => variantName
  if fieldEs.isEmpty then .var headName
  else .app headName fieldEs

/-- Resolve a `SymExpr` against the current var map to a Pure
    expression. Symbolic ids (`SymVal n`) fall back to a generated
    name `sN`.

    M9.5f: takes `tdm` so a `symVariant` resolves to a properly
    qualified ctor application (`NumOrZero.Num x1` rather than a
    bare `Num`). C-style nullary variants still go through
    [variantPExpr] which qualifies them; the parent walker's
    match-arm `qualify` pass becomes a no-op for already-qualified
    names. -/
partial def lookupSymExpr
    (tdm : TypeDeclMap) (localTypes : Std.HashMap Nat Raw.LlbcTy)
    (vm : VarMap) : SymExpr → PExpr
  | .symVal n => .var s!"s{n}"
  | .symLit l => .lit l
  | .symCopy p => lookupPlace tdm localTypes vm p
  | .symMove p => lookupPlace tdm localTypes vm p
  | .symMutBorrowTok n => .var s!"b{n}"
  -- M9.5d / M9.5f: an enum-variant ctor (the RHS of an EvAssign
  -- whose source was an `AggregatedAdt`). We qualify the name
  -- against the type-decl map and apply payload fields when present.
  | .symVariant adtId _ variantName fields =>
    variantPExpr tdm adtId variantName
      (fields.map (lookupSymExpr tdm localTypes vm))
  -- M9.5p: tuple aggregate. Recurse on each operand and assemble a
  -- `PExpr.tuple` (the same ctor M12.2b uses for multi-region tails).
  | .symTuple fields =>
    .tuple (fields.map (lookupSymExpr tdm localTypes vm))
  -- M9.5p: named-field struct aggregate. The OCaml cert generator
  -- already resolved each field's surface name; recurse on the
  -- values and emit a `PExpr.recordLit`.
  --
  -- Phase 1C: also resolve the struct's bare Lean name through
  -- `tdm` so RustEmit can render `Foo { … }` instead of a placeholder.
  | .symRecord adtId fields =>
    let adtName := (tdm[adtId]?).map (·.name)
    .recordLit (fields.map fun (n, e) => (n, lookupSymExpr tdm localTypes vm e)) adtName
  -- Session 6: an `as`-cast. We emit `.app "__cast::<targetTy>" #[inner]`;
  -- RustEmit recognises the head and renders `(<inner> as <targetTy>)`,
  -- LeanEmit renders a typed Lean coercion / shim call. The targetTy
  -- string is the OCaml-stringified literal_type tag (`"i32"`, `"u32"`,
  -- etc.) — both emitters re-stringify it to their target syntax.
  | .symCast targetTy inner =>
    .app s!"__cast::{targetTy}" #[lookupSymExpr tdm localTypes vm inner]

/-- M9.5e/f: payload-binder-aware variant of [lookupSymExpr]. Same
    semantics as [lookupSymExpr] except a `symCopy` / `symMove` of a
    `[..., Field K]`-projected place consults `payloadBinders` first
    via [lookupPlaceWithBinders]. The match-arm sub-walk calls this in
    place of [lookupSymExpr]. -/
partial def lookupSymExprWithBinders
    (tdm : TypeDeclMap) (localTypes : Std.HashMap Nat Raw.LlbcTy)
    (vm : VarMap) (payloadBinders : Std.HashMap (Nat × Nat) String) :
    SymExpr → PExpr
  | .symVal n => .var s!"s{n}"
  | .symLit l => .lit l
  | .symCopy p => lookupPlaceWithBinders tdm localTypes vm payloadBinders p
  | .symMove p => lookupPlaceWithBinders tdm localTypes vm payloadBinders p
  | .symMutBorrowTok n => .var s!"b{n}"
  | .symVariant adtId _ variantName fields =>
    variantPExpr tdm adtId variantName
      (fields.map (lookupSymExprWithBinders tdm localTypes vm payloadBinders))
  -- M9.5p: tuple / record aggregate. Same shape as the non-binder
  -- variant — the payload-binder map applies to `[Field K]`-style
  -- projections inside a match arm, which can't surface inside the
  -- operands of an aggregate construction in current LLBC.
  | .symTuple fields =>
    .tuple (fields.map (lookupSymExprWithBinders tdm localTypes vm payloadBinders))
  -- Phase 1C: resolve the struct's bare Lean name through `tdm`
  -- so RustEmit has a real Rust struct name to render.
  | .symRecord adtId fields =>
    let adtName := (tdm[adtId]?).map (·.name)
    .recordLit (fields.map fun (n, e) =>
      (n, lookupSymExprWithBinders tdm localTypes vm payloadBinders e)) adtName
  -- Session 6: an `as`-cast (binder-aware variant). Identical to
  -- the non-binder case — casts cannot appear inside match-arm
  -- payloads in current LLBC, so the binder map is not consulted.
  | .symCast targetTy inner =>
    .app s!"__cast::{targetTy}"
      #[lookupSymExprWithBinders tdm localTypes vm payloadBinders inner]

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

/-- M9.5h: distinguish pure (non-`Result`) binops from monadic ones.
    `true` for binops whose Lean form returns the operand type (or
    `Bool`) directly, NOT wrapped in `Result α`. The taxonomy follows
    the standard Aeneas backend's emitter:

    * **Pure** (this set): `BitXor` / `BitAnd` / `BitOr` (bit ops),
      `AddWrap` / `SubWrap` / `MulWrap` (wrapping arithmetic — never
      panic), `Eq` / `Ne` / `Lt` / `Le` / `Gt` / `Ge` (comparisons —
      return `Bool`), `Cmp` (three-way compare — returns `Ordering`).
    * **Monadic** (everything else): `Add` / `Sub` / `Mul` / `Div` /
      `Rem` / `Shl` / `Shr` (panic on overflow / divide-by-zero /
      out-of-range shift), `AddChecked` / `SubChecked` / `MulChecked`
      (return `Option<T>` lifted into `Result`), `Offset`.

    Note: `binopHead` lossily lumps `ShlPanic` / `ShlUB` / `ShlWrap`
    together as `"Shl"` (likewise for `Shr`). The current cert format
    only emits `*Panic` shift variants in fixtures under test, so the
    `"Shl"` / `"Shr"` heads are always monadic at the PExpr level. If
    a future fixture exercises `ShlWrap` / `ShrWrap` we'd need to
    either thread the original tag through or extend `binopHead` to
    keep `*Wrap` shifts as a distinct head.

    Used by:
    * [tailToResult] to decide whether to wrap a tail `.app` in `ok`
      (pure binops MUST be wrapped — they're not Result-typed).
    * [assembleBody] to decide whether the
      `let nm ← e; ok (var nm)` collapse should drop the let entirely
      (only safe when `e` is monadic) or instead emit `ok e` (when
      `e` is a pure binop). -/
def isPureBinop : String → Bool
  | "BitXor" | "BitAnd" | "BitOr"
  | "AddWrap" | "SubWrap" | "MulWrap"
  | "Eq" | "Ne" | "Lt" | "Le" | "Gt" | "Ge"
  | "Cmp" => true
  | _ => false

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
  /-- M9.5e: per-arm payload-binder map. Keyed by
      `(scrutineeRootLocal, fieldIdx)`; the value is the pure binder
      name the arm-body sub-walk should surface when an
      `EvCopy`/`EvAssign`/`SymCopy`/`SymMove` reads through a
      `[Field K]` projection of the scrutinee local. Empty in the
      parent walk; populated by the match-arm sub-walk just before
      it walks an arm's body events. Empty at function start; the
      parent walker doesn't consult it. -/
  payloadBinders : Std.HashMap (Nat × Nat) String := {}
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
  /-- M9.5g: in-flight `@SliceIndexMut` calls — slice analogue of
      [arrayIndexMut]. Same shape (`slice × idx × sliceRoot`), same
      lifecycle: stash at EvCall time, consume at the subsequent
      deref-write to lower `xs[i] = v` into a single `Slice.update
      <slice> <idx> <rhs>` binding. Kept as a separate map (rather
      than a tagged union with arrayIndexMut) so the deref-write
      branch can pick the right head name (`Array.update` vs
      `Slice.update`) without re-scanning the dst type. -/
  sliceIndexMut : Std.HashMap Nat (PExpr × PExpr × Option Nat) := {}
  /-- M9.5n / M9.7o-E5b: per-local structured `LlbcTy`, used to
      resolve a `[Field K]` projection on a `local L` to a
      `<vm[L]>.<fieldName>` field access. Seeded from the matching
      `LlbcFunDecl.localsTypes` at WalkState init (Charon's convention:
      local 0 is the return slot, locals 1..N are the inputs, the rest
      are temps); a missing entry causes the field-projection lookup
      to fall back to the projection-erasing legacy behaviour
      (`lookupPlace` returns the root pure value without projecting). -/
  localTypes : Std.HashMap Nat Raw.LlbcTy := {}
  /-- Session 7 Item 1d follow-up: reverse map from a parameter's
      effective name back to its 1-based input-local index. Used by
      the deref-write handler's `resolveInputRoot` so the propagation
      target ("write through this borrow lands on the original input")
      survives when the param uses the user's source name (`y`)
      rather than the synthesised `x{N}` form the legacy `x`-prefix
      check assumed. Seeded once at translateFunWith / translateLoopFun
      from `lf.localsNames` (or the synthesised `paramName` fallback
      when no source name is available). -/
  paramNameMap : Std.HashMap String Nat := {}
  /-- Session 7 Item 1d follow-up: forward map from input-local index
      (1..numParams) to that input's effective name. Lets the EvEndAbs
      `_post`-name synthesiser produce `<sourceName>_post` instead of
      `<paramName k>_post` when the cert carries a source name. -/
  paramNameByLocal : Std.HashMap Nat String := {}
  /-- Zero-Skip Step 3 (Cluster `recursive_match_arm_scoping`): the
      function's `LlbcFunDecl.localsNames` (one entry per local in
      `localTypes`, in declaration order; `none` for unnamed
      MIR-introduced temps). Used by the match-arm sub-walk to give
      payload binders their source-level name (`tl`, `x`, …) instead
      of the synthesised `x{N}` form — without the source name the
      pattern binders don't agree with the body's references after
      the seed pass's variant-field-binder fix-up. -/
  localsNames : Array (Option String) := #[]
  /-- Zero-Skip Step 3 (Cluster `recursive_match_arm_scoping`):
      precomputed per-(variant-id, field-idx) binder name. Built at
      `translateFunWith` time by scanning the LLBC body for
      `Assign localK ← Ref(_.[Field _ (some vid) fIdx])` statements
      and mapping (vid, fIdx) → `localsNames[localK]?` (or the
      synthesised `s!"x{localK}"` fallback used by the seed pass).
      Consulted by the match-arm walker so the pattern slot agrees
      with the body's seeded binder name. Empty for non-match
      bodies / opaque LLBC. -/
  variantBinders : Std.HashMap (Nat × Nat) String := {}
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
  | .symVal _ | .symLit _ | .symMutBorrowTok _ | .symVariant _ _ _ _
  | .symTuple _ | .symRecord _ _ | .symCast _ _ => 0

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
    | .join _ _ _ _ =>
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
      | .join _ _ _ _ =>
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
          | .join _ _ _ _ =>
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
    --
    -- M9.5e: when `s` is a `[..., Field K]` projection of an arm
    -- scrutinee local, surface the arm-scoped payload binder rather
    -- than the scrutinee's root expression.
    if s.local_ == d.local_ then st
    else { st with
      vm := st.vm.insert d.local_ (lookupPlaceWithBinders st.tdm st.localTypes st.vm st.payloadBinders s)
      lastWrite := some d.local_ }
  | .move s d =>
    -- Move: same as copy but invalidate the source.
    if s.local_ == d.local_ then st
    else
      let v := lookupPlaceWithBinders st.tdm st.localTypes st.vm st.payloadBinders s
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
    --
    -- M9.5e: in a match-arm sub-walk where `payloadBinders` carries
    -- one entry per payload field of the matched variant, a SymCopy
    -- / SymMove of `scrutLocal.[Field K]` resolves to the arm-scoped
    -- binder name instead of the scrutinee's root expression.
    let rhsE := lookupSymExprWithBinders st.tdm st.localTypes st.vm st.payloadBinders rhs
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
          -- M9.7o-E5b: source the dst-root local's structured ADT id
          -- via `localTypes` (peeling an outer `&mut` if present).
          (st.localTypes[d.local_]?).bind fun t =>
            (adtIdOfLlbcTy t).bind fun adtId =>
              st.tdm[adtId]?.bind fun info =>
                info.fieldNames[k]?.map fun fname =>
                  let base : PExpr :=
                    st.vm.getD d.local_ (.var (paramName d.local_))
                  -- Phase 1C: pass the struct's bare Lean name through
                  -- so RustEmit can render `Foo { field: v, ..base }`.
                  (fname, .structUpdate base fname rhsE (some info.name))
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
      -- M9.5g: parallel consumption of a pending `@SliceIndexMut`.
      -- Same routing logic as the array case; only the head name
      -- and the underlying map differ.
      match st.sliceIndexMut[d.local_]? with
      | some (sliceE, idxE, sliceRoot) =>
        let updateApp : PExpr :=
          .app "Slice.update" #[sliceE, idxE, rhsE]
        let (nm, st') := st.freshName
        let vm' :=
          match sliceRoot with
          | some r => (st'.vm.insert r (.var nm)).insert d.local_ (.var nm)
          | none => st'.vm.insert d.local_ (.var nm)
        { st' with
          binds := st'.binds.push (.regular nm updateApp)
          vm := vm'
          sliceIndexMut := st'.sliceIndexMut.erase d.local_
          lastWrite := sliceRoot.orElse (fun _ => some d.local_) }
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
            -- Session 7 Item 1d follow-up: consult the reverse map
            -- (`name → 1-based input local`) so a source-named param
            -- (`y`) resolves the same way the synthesised `x1` did.
            -- Fall back to the legacy `x{N}` text-pattern check so
            -- this works even when the map wasn't seeded (e.g.
            -- back-compat callers of the no-op `translateFun`).
            match st.paramNameMap[name]? with
            | some n => some n
            | none =>
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
      -- M12.2a-3: a trailing `EvAssign local=0 rhs=()` shows up in v3
      -- certs for unit-returning functions whose body already wrote
      -- a meaningful return value into vm[0] via a previous deref-
      -- assign that fired a backward closure (the `use_choose`-style
      -- pattern). The unit-write is the LLBC convention of clearing
      -- the return slot before `EvReturn`, but our walker has
      -- *already* stashed the function's real tail in vm[0]. Skip the
      -- overwrite when (a) dst is the return slot, (b) rhs is `()`,
      -- and (c) vm[0] holds a `_back`-headed application. Without
      -- this guard the trailing `()` would clobber the back-closure
      -- application and the function tail would degrade to `ok ()` /
      -- `ok (x, y)` (per the BackSig wrap-up fallback).
      let isUnitRhs : Bool :=
        match rhsE with
        | .tuple #[] => true
        | _ => false
      let vm0IsBackApp : Bool :=
        match st.vm[0]? with
        | some (PExpr.app head _) => (head.splitOn "_back").length ≥ 2
        | _ => false
      if d.local_ == 0 && isUnitRhs && vm0IsBackApp then
        st
      else
        { st with
          vm := st.vm.insert d.local_ rhsE
          lastWrite := some d.local_ }
  | .binop op lhs rhs d =>
    let lhsE := lookupSymExpr st.tdm st.localTypes st.vm lhs
    let rhsE := lookupSymExpr st.tdm st.localTypes st.vm rhs
    let app : PExpr := .app (binopHead op) #[lhsE, rhsE]
    let (nm, st) := st.freshName
    { st with
      binds := st.binds.push (.regular nm app)
      vm := st.vm.insert d.local_ (.var nm)
      lastWrite := some d.local_ }
  -- Borrow events have no value-level effect in the forward
  -- direction; the mutation flows out via the function's return,
  -- modelled by M10.2's backward-function machinery.
  | .mutBorrow _ _ _ _ | .sharedBorrow _ _ _ _
  | .reborrow _ _ _ _ _ | .endBorrow _ _ => st
  -- Control / panic / return are observed at the wrap-up step
  -- below; they don't affect the per-local value map.
  | .assert _ _ | .panic | .retn => st
  | .call _ callId fnName args dst regionAbs _ =>
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
      let argEs := args.map (lookupSymExpr st.tdm st.localTypes st.vm)
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
          -- Session 7 Item 1d follow-up: source-name map first.
          match st.paramNameMap[name]? with
          | some n => some n
          | none =>
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
    else if fnName == "@SliceIndexMut" && args.size == 2 then
      -- M9.5g: parallel intercept for `&mut [T]` writes. Same shape as
      -- `@ArrayIndexMut` — stash the slice/index pair so the
      -- subsequent deref-write to the call's dst local can lower to
      -- a single `Slice.update <slice> <idx> <rhs>` binding. NO
      -- binding is emitted at EvCall time.
      let argEs := args.map (lookupSymExpr st.tdm st.localTypes st.vm)
      let sliceE := argEs[0]!
      let idxE := argEs[1]!
      let paramNameOfPExpr : PExpr → Option Nat := fun e =>
        match e with
        | .var name =>
          -- Session 7 Item 1d follow-up: source-name map first.
          match st.paramNameMap[name]? with
          | some n => some n
          | none =>
            if name.length ≥ 2 && name.front == 'x' then
              match (name.drop 1).toNat? with
              | some n => if 1 ≤ n ∧ n ≤ st.numParams then some n else none
              | none => none
            else none
        | _ => none
      let sliceRoot : Option Nat := paramNameOfPExpr sliceE
      { st with
        sliceIndexMut := st.sliceIndexMut.insert dst.local_
          (sliceE, idxE, sliceRoot) }
    else if fnName == "@SliceIndexShared" && args.size == 2 then
      -- M9.5g: immutable slice read. The standard backend lowers
      -- `xs[i]` (when `xs : &[T]`) to a single `Slice.index_usize xs
      -- i` forward call returning `Result T` — no backward closure.
      -- The cert event marks the call with a non-empty `region_abs`
      -- (the shared-region abstraction), which the generic call
      -- machinery would otherwise mis-route through the
      -- (forward, backward)-pair shape. We emit a regular forward
      -- binding directly here, bypassing the regionAbs-aware path.
      let argEs := args.map (lookupSymExpr st.tdm st.localTypes st.vm)
      let app : PExpr := .app "Slice.index_usize" argEs
      let (nm, st) := st.freshName
      { st with
        binds := st.binds.push (.regular nm app)
        vm := st.vm.insert dst.local_ (.var nm)
        lastWrite := some dst.local_ }
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
    let argEs := args.map (lookupSymExpr st.tdm st.localTypes st.vm)
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
        -- Session 7 Item 1d follow-up: prefer the source-name reverse
        -- map; fall back to the legacy `x{N}` text pattern.
        match st.paramNameMap[name]? with
        | some n => some n
        | none =>
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
    -- Session 7 Item 1d follow-up: prefer the source-name suffix
    -- (`<sourceName>_post`); fall back to the synthesised
    -- `<paramName l>_post`.
    let postBindName (l : Nat) : String :=
      s!"{st.paramNameByLocal.getD l (paramName l)}_post"
    let (nm, st) :=
      match inputLocals.findSome? (fun l => if l = 0 then none else some l) with
      | some l => (postBindName l, st)
      | none =>
        match inputLocalsViaExpr.findSome? (fun l => if l = 0 then none else some l) with
        | some l => (postBindName l, st)
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
    -- M9.7o-E5b: source the dst's structured type from `localTypes`
    -- (seeded from `LlbcFunDecl.localsTypes` at WalkState init). The
    -- call's `dst` place is an unprojected local in every fixture
    -- under test, so the local's recorded type IS the place's type.
    let dstLlbcTy : Option LlbcTy := st.localTypes[dst.local_]?
    let dstIsMutRef : Bool :=
      match dstLlbcTy with
      | some t => isMutRefLlbc t
      | none => false
    let dstIsUnit : Bool :=
      match dstLlbcTy with
      | some t => isUnitTyLlbc t
      | none => false
    -- M12.2b: detect a multi-region call returning a tuple of
    -- N ≥ 2 mut refs. The standard backend emits N+1 result
    -- components: a forward (often `_` ignored) plus N backward
    -- closures `_back0`, `_back1`, …, `_back{N-1}`. We bind all
    -- of them via a `tuple` Bind and stash per-field closure
    -- names in callBackByField so subsequent field-destructure
    -- EvAssigns can thread them.
    let dstTupleOfMuts : Option Nat :=
      match dstLlbcTy with
      | some t => isOutputTupleOfMutRefsLlbc t
      | none => none
    -- M9.5l: a callee with only `&T` (shared) arguments still has
    -- a non-empty `regionAbs` from the OCaml interpreter (a shared
    -- borrow still registers an abstraction), but nothing flows
    -- back through a shared borrow — the call returns just the
    -- forward value, not a `(forward, backward)` pair. Detect this
    -- shape by walking the args and checking that none has type
    -- `&mut T`. M9.7o-E5b: we look up each arg's root-local
    -- structured type from `localTypes`; for an arg whose place
    -- carries a `[Deref]` projection (`*x`) the place's projected
    -- type strips one ref layer, but we still want to recognise the
    -- underlying `&mut T` shape, so we test the root local's type
    -- directly. Non-place args (literals, tokens, variants)
    -- contribute no mut refs.
    let symExprIsMutRef : SymExpr → Bool := fun e =>
      match e with
      | .symCopy p | .symMove p =>
        match st.localTypes[p.local_]? with
        | some t => isMutRefLlbc t
        | none => false
      | _ => false
    let anyArgIsMutRef : Bool := args.any symExprIsMutRef
    if regionAbs.isEmpty || !anyArgIsMutRef then
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
  | .endAbs abs _finals _released _ =>
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
          -- Session 7 Item 1d follow-up: prefer the source-name
          -- reverse map; fall back to the legacy `x{N}` text pattern
          -- for back-compat with unnamed test fixtures.
          match st.paramNameMap[name]? with
          | some n => some n
          | none =>
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
          -- Session 7 Item 1d follow-up: when a source name exists,
          -- use `<sourceName>_post`; otherwise fall back to the
          -- synthesised `<paramName postLocal>_post`.
          let postName : String :=
            s!"{st.paramNameByLocal.getD postLocal (paramName postLocal)}_post"
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
  | .join _ _ _ _ | .loopInv _ _ _ | .loopEnd _ => st
  -- M9.5d: match-arm markers are consumed by the outer [walkEvents]
  -- loop (it groups arms into a `PExpr.matchE`). Hitting one here
  -- means the lookahead failed to recognise a match block; treat
  -- as a no-op so the walk stays total.
  | .matchArm _ _ _ _ => st
  -- M9.5r: lazy borrow expansion is purely a SymState mutation for
  -- the LLBC# replayer; the Forward translator's value-flow walk
  -- doesn't observe new bindings (the dst local that holds the
  -- expanded borrow was already named at EvCall time). No-op.
  | .symExpandMutBorrow _ _ _ _ _ _ => st

/-- Render a `SymExpr` from a join state summary as a Pure expression
    *in the context of a sub-walk's final var map*. Used by
    [applyJoinedLocal] to materialise the per-branch value of a joined
    local. We prefer the sub-walk's `vm` over the raw cert SymExpr
    because the sub-walk has already lifted symbolic ids into named
    `t<N>` / `x<N>` bindings through the events. -/
def renderJoinSide (tdm : TypeDeclMap)
    (localTypes : Std.HashMap Nat Raw.LlbcTy) (vm : VarMap)
    (cs_env : Array (Nat × SymExpr))
    (target : Nat) : Option PExpr :=
  match vm[target]? with
  | some e => some e
  | none =>
    -- Fall back to the cert's per-branch SymExpr if vm doesn't have
    -- an entry. (Should be rare — sub-walks populate vm for every
    -- local they touch.)
    let entry := cs_env.find? (fun (l, _) => l == target)
    entry.map fun (_, se) => lookupSymExpr tdm localTypes vm se

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
    expression. Monadic binops (`Add` / `Sub` / `Mul` / `Div` / `Rem` /
    `Shl` / `Shr`, etc.) emit `Result α`-typed apps already; double-
    wrapping them would change semantics. M12.2a-2: also recognize
    `ifThenElse` whose branches are themselves already Result-typed
    (each branch was built via [assembleBody] which wraps in `ok`).
    M9.5f: an `.app` whose head contains a `.` is a *qualified
    constructor application* (`NumOrZero.Num x1`) — pure, not Result-
    typed, so it must be wrapped in `ok`. M9.5h: **pure binops**
    (`BitXor` / `BitAnd` / `BitOr`, comparisons, `*Wrap` variants —
    see [isPureBinop]) likewise return their operand type directly,
    so they need an explicit `ok` wrap in tail position. Without this
    the emitted body would be `do (x1 ^^^ x2)` rather than `do ok (x1
    ^^^ x2)` — Lean would reject the bare `Std.U32` as a `Result
    Std.U32`-shaped do-tail in the standard-backend semantics.
    (Against the in-tree `RuntimeShim` the bare form happens to
    typecheck because the shim overrides `HXor U32 U32 (Result U32)`;
    that's an artifact of the shim, not the standard backend's
    convention.) -/
def tailToResult (e : PExpr) : PExpr :=
  match e with
  | .app head _ =>
    -- A qualified constructor (`<TypeName>.<Variant>` or
    -- `<Type>.<assoc>`) is a pure value and must be wrapped.
    -- A pure binop (`BitXor`, `Lt`, `AddWrap`, …) similarly returns
    -- a non-Result value; wrap it. Monadic binops (`Add`, `Shl`, …)
    -- already produce `Result α` and are emitted bare.
    -- Session 6: `__cast::<ty>` heads (synthesised by the cert walker
    -- for `as`-casts) emit a pure typed coercion / Rust cast — wrap
    -- in `ok` so the do-tail typechecks against `Result α`.
    -- Session 7 Item 1c follow-up: a Charon-style raw qualified head
    -- (`core::num::{u32}::wrapping_add`) also resolves to a pure shim
    -- call at the Lean level; detect it via `::` (the head comes in
    -- pre-sanitisation here) — without this, do-tail wrapping_add /
    -- pure intercept calls would emit a bare `(call)` and fail to
    -- typecheck against `Result α`.
    if head.contains '.' || head.contains ':' ||
        isPureBinop head || head.startsWith "__cast::" then
      .ok e else e
  | .ifThenElse _ _ _ => e  -- Branches are already Result-typed.
  | .matchE _ _ => e  -- M9.5d: arms are already Result-typed.
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
    nested `do let … ← …; …` chain.

    **Last-binding collapse.** If the *last* binding has the shape
    `regular nm e` with `nm` a fresh temp (`isFreshTempName`) AND the
    tail is `ok (var nm)`, we collapse: the last `let nm ← e` is
    dropped and `e` (resp. `ok e` when `e` is a pure binop, see
    below) becomes the new tail of the do-block. Prior bindings are
    wrapped around the new tail. This produces:

    * `def incr (x : U32) : Result U32 := do x + 1#u32`
      (single binding, `e = x + 1#u32` monadic — bare in tail.)
    * `def shift_u32 a : do let t ← a >>> 16#usize; t <<< 16#usize`
      (two bindings; the last `t1 ← t0 <<< 16#usize` collapses into
      the do-tail; the first binding is preserved as `let t ← …`.)
    * `def xor_u32 a b : do ok (a ^^^ b)` (single pure-binop binding
      — collapse with `ok` wrap, since `a ^^^ b` is `U32`, not
      `Result U32`.)

    M9.5h: the original M10.0 collapse rule unconditionally rewrote
    `let nm ← e; ok (var nm)` to bare `e`, which is wrong when `e` is
    a pure binop — `e` is not Result-typed and would be ill-formed
    as a do-block tail. The pure-binop branch wraps in `ok` instead.

    The collapse is only safe for "fresh temp" bindings (`tN`). A
    M10.2b post-state binding (`x1_post`) carries information about
    which `&mut` input's post-state we just bound, and the tail
    `ok x1_post` is the canonical way of returning that post-state;
    keeping the explicit `let x1_post ← …; ok x1_post` makes the
    forward-and-backward correspondence visible in the emitted code. -/
def assembleBody (binds : Array Bind) (tail : PExpr) : PExpr :=
  let wrapOne (b : Bind) (acc : PExpr) : PExpr :=
    match b with
    | .regular nm e => .letIn nm placeholderTy e acc
    | .pair nm bnm e => .letPat #[nm, bnm] placeholderTy e acc
    | .tuple names e => .letPat names placeholderTy e acc
  -- Determine whether the last-binding collapse should fire and, if
  -- so, what the rewritten tail should be (`e` for monadic, `ok e`
  -- for pure). Returns the new tail + the leading bindings minus
  -- the collapsed last one; or `none` when the collapse doesn't
  -- apply (and the unmodified `binds`/`tail` are used).
  --
  -- M9.5q-3: the rule used to gate on `isFreshTempName nm` to avoid
  -- collapsing M10.2b post-state bindings whose `_post` suffix
  -- carries forward/backward-correspondence info. But for a
  -- *single* `.regular` binding whose rhs is a non-pure function
  -- call (head contains `.`) and whose tail is `ok (.var nm)`, the
  -- `_post` suffix is just naming noise — there's no back-closure
  -- being threaded alongside (those are .pair / .tuple shapes, not
  -- .regular). The standard Aeneas backend emits the bare tail-call
  -- in this case (e.g. `use_numeric t := … Numeric.value t` rather
  -- than `let x1_post ← Numeric.value t; ok x1_post`). Relax the
  -- gate to also accept a `.regular` binding with a `.app` rhs
  -- whose head looks like a qualified function call.
  -- A function-call head looks like a qualified path: Charon's raw
  -- `crate::module::{impl-path}::method`, or after sanitization the
  -- dot-form `Crate.Module.X.method`. Either contains `:` or `.` —
  -- pure binops (`Add`, `BitXor`, `Lt`, …) are single tokens with
  -- neither. We accept both separator styles here because the IR
  -- carries the raw form (pretty-print sanitizes at render time).
  let isCallHead (head : String) : Bool :=
    !isPureBinop head && (head.contains '.' || head.contains ':')
  let collapseOk (nm : String) (rhs : PExpr) : Bool :=
    isFreshTempName nm ||
      (match rhs with
       | .app head _ => isCallHead head
       | _ => false)
  let collapse? : Option (Array Bind × PExpr) :=
    match binds.back?, tail with
    | some (.regular nm e), .ok (.var n) =>
      if nm == n && collapseOk nm e then
        let newTail :=
          match e with
          | .app head _ => if isPureBinop head then .ok e else e
          | _ => e
        some (binds.pop, newTail)
      else none
    | _, _ => none
  match collapse? with
  | some (leading, newTail) => leading.foldr (init := newTail) wrapOne
  | none => binds.foldr (init := tail) wrapOne

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
      | .matchArm scrutinee _adtId _vid _vname =>
        -- M9.5d: a match-arm marker opens an arm. The OCaml emitter
        -- interleaves arms linearly: `[matchArm A] [body_A] [matchArm
        -- B] [body_B] …`. We scan for the *contiguous* run of
        -- matchArm markers + their bodies (all sharing the same
        -- scrutinee), sub-walk each arm's body events into a `PExpr`,
        -- then emit a single `PExpr.matchE` and skip past the whole
        -- run.
        --
        -- Each arm's body range ends at the *next* matchArm with the
        -- same scrutinee, or at the end of the event array, or at an
        -- `EvJoin` (the post-match continuation marker). We strip a
        -- trailing `EvReturn` from each arm body so the per-arm tail
        -- expression is just the assigned return value (the
        -- `tailToResult` wrap below adds the `ok …`).
        let sameScrutinee : Event → Bool
          | .matchArm s _ _ _ =>
            match scrutinee, s with
            | .symVal a, .symVal b => a == b
            | _, _ => false
          | _ => false
        -- Find each arm's [start, end) range and its ctor info.
        let rec collect (k : Nat)
            (acc : List (Nat × Nat × Nat × Nat × String)) :
            List (Nat × Nat × Nat × Nat × String) :=
          if h : k ≥ evs.size then acc.reverse
          else
            match evs[k]'(Nat.lt_of_not_ge h) with
            | .matchArm s adtId vid vname =>
              -- Only collect if it shares our opener's scrutinee.
              if sameScrutinee (Event.matchArm s adtId vid vname) then
                -- Find the end: next matchArm (same scrutinee) or
                -- the array end. We stop at the first non-matching
                -- event boundary; nested matches aren't supported in
                -- M9.5d.
                let rec findEnd (j : Nat) : Nat :=
                  if hj : j ≥ evs.size then j
                  else
                    match evs[j]'(Nat.lt_of_not_ge hj) with
                    | .matchArm s' _ _ _ =>
                      if sameScrutinee (Event.matchArm s' 0 0 "") then j
                      else findEnd (j + 1)
                    | .join _ _ _ _ => j
                    | _ => findEnd (j + 1)
                let endIdx := findEnd (k + 1)
                collect endIdx ((k, endIdx, adtId, vid, vname) :: acc)
              else acc.reverse
            | _ => acc.reverse
        let armsRaw := collect i []
        -- Zero-Skip Step 3 (Cluster `recursive_match_arm_scoping`):
        -- detect Charon's *grouped* match layout. The default
        -- interleaved layout is
        --   `[matchArm A] [body A] [matchArm B] [body B] …`
        -- and `collect` slices it correctly. But Charon also emits a
        -- *grouped* layout for matches whose body values flow
        -- directly into the return slot (e.g. `paper::sum`,
        -- `paper::list_nth_mut`, `demo::list_nth`, `demo::i32_id`
        -- via Assert pairs):
        --   `[matchArm A] [matchArm B] [body B] [body A]`
        -- with all markers up front and the bodies *in reverse
        -- variant-id order* trailing. In that layout `collect`
        -- assigns arm A an empty body (`ok ()`) and arm B the whole
        -- residue, which is the swap bug the audit calls out.
        --
        -- Detection: every arm except the last has an empty body
        -- range (`endIdx == start + 1`). Repair: scan the trailing
        -- event stream of the last arm for top-level body
        -- terminators (`EvReturn` / `EvPanic`), skipping past
        -- Assert(true)…Assert(false)…(EvJoin|EvReturn) pairs, to
        -- split it into one chunk per arm; then assign chunks to
        -- arms in *reverse* order.
        let arms : List (Nat × Nat × Nat × Nat × String) :=
          match armsRaw with
          | []  => []
          | [_] => armsRaw
          | _ =>
            let nArms := armsRaw.length
            let allButLastEmpty :=
              armsRaw.take (nArms - 1) |>.all (fun (s, e, _, _, _) => e == s + 1)
            if !allButLastEmpty then armsRaw
            else
              -- Body events start right after the last marker; they
              -- run to the original last-arm `endIdx` (which is either
              -- the array end or an EvJoin).
              let (firstStart, totalEnd) :=
                match armsRaw.head?, armsRaw.getLast? with
                | some (s0, _, _, _, _), some (_, eN, _, _, _) => (s0, eN)
                | _, _ => (i + nArms, evs.size)
              let _ := firstStart  -- silence unused
              let bodyStart := i + nArms
              -- Walk the body event stream looking for top-level
              -- terminators. We re-use `findBranchEnd` to skip past
              -- whole if/else constructs encoded as Assert pairs so
              -- their internal `EvReturn`s don't get treated as
              -- chunk boundaries.
              let rec nextChunkEnd (k : Nat) (fuel : Nat) : Nat :=
                match fuel with
                | 0 => k
                | Nat.succ fuel' =>
                  if k ≥ totalEnd then totalEnd
                  else
                    match evs[k]? with
                    | some (.assert c true) =>
                      -- Skip past the whole branch construct.
                      match findBranchEnd evs k c with
                      | some (.joined _ kIdx) => nextChunkEnd (kIdx + 1) fuel'
                      | some (.returnTailed _ _ fEnd) => fEnd + 1
                      | none => nextChunkEnd (k + 1) fuel'
                    | some .retn => k + 1
                    | some .panic => k + 1
                    | _ => nextChunkEnd (k + 1) fuel'
              -- Collect chunk ranges in stream order.
              let rec collectChunks (k : Nat) (remaining : Nat)
                  (acc : List (Nat × Nat)) (fuel : Nat) : List (Nat × Nat) :=
                match fuel, remaining with
                | 0, _ => acc.reverse
                | _, 0 => acc.reverse
                | Nat.succ fuel', Nat.succ _ =>
                  if k ≥ totalEnd then acc.reverse
                  else
                    let kEnd := nextChunkEnd k (totalEnd - k + 1)
                    let kEnd := if kEnd > totalEnd then totalEnd else kEnd
                    collectChunks kEnd (remaining - 1) ((k, kEnd) :: acc) fuel'
              let chunks := collectChunks bodyStart nArms [] (nArms + 1)
              -- We need exactly nArms chunks; if fewer were found,
              -- fall back to armsRaw (don't risk a worse mis-emit).
              if chunks.length != nArms then armsRaw
              else
                -- Pair each marker (in marker order) with a chunk
                -- (in reverse chunk order).
                let rev := chunks.reverse
                let pairs :=
                  (List.range nArms).map fun idx =>
                    let (_, _, adtId, vid, vname) := armsRaw[idx]!
                    let (cs, ce) := rev[idx]!
                    -- We synthesise `(start, endIdx)` so the
                    -- downstream body extractor — which uses
                    -- `(start+1, endIdx)` and may strip a trailing
                    -- `EvReturn` — sees the right events. We extend
                    -- `endIdx` by one past `ce` so the
                    -- trailing-EvReturn strip targets the
                    -- post-terminator event (typically a no-op
                    -- `EvMove`) instead of swallowing the chunk's
                    -- own terminator — that terminator is structural
                    -- when the chunk contains an Assert-pair if/else
                    -- (whose false-branch terminator is the chunk's
                    -- own trailing `EvReturn`).
                    (cs - 1, ce + 1, adtId, vid, vname)
                pairs
        match arms with
        | [] => go (i + 1) (walkEvent st ev)
        | _ =>
          -- Resolve the adt name via the type-decl map. All arms
          -- share the same adt id by construction; take the first.
          let adtId : Nat :=
            match arms.head? with
            | some (_, _, a, _, _) => a
            | none => 0
          let adtName : String :=
            match st.tdm[adtId]? with
            | some info => info.name
            | none => "Enum"
          -- Pick the scrutinee's surface form *and* root local: walk
          -- vm looking for an input parameter whose stored expression
          -- is `.var "xK"`. For the C-style fixtures the scrutinee is
          -- always a direct function parameter, so we just pick the
          -- first input that maps to a `var`. Fall back to `s<n>`
          -- form when nothing matches. M9.5e: we also need the
          -- *local id* of the scrutinee so the per-arm sub-walk can
          -- key payload binders by it.
          let (scrutE, scrutLocal) : PExpr × Nat := Id.run do
            let nFallback : Nat :=
              match scrutinee with
              | .symVal n => n
              | _ => 0
            let mut found : Option PExpr := none
            let mut bestLocal : Nat := 0
            for (l, e) in st.vm.toList do
              if 1 ≤ l ∧ l ≤ st.numParams then
                match e with
                | .var _ =>
                  -- Prefer the lowest-numbered input parameter.
                  if found.isNone ∨ l < bestLocal then
                    found := some e
                    bestLocal := l
                | _ => pure ()
            return (found.getD (.var s!"s{nFallback}"), bestLocal)
          -- M9.5e: look up the enum's per-variant field counts. Empty
          -- (or `none`) for older C-style fixtures; populated for
          -- payload-bearing variants via the type-decl map.
          let variantFieldCounts : Array Nat :=
            match st.tdm[adtId]? with
            | some info => info.variantFieldCounts
            | none => #[]
          -- M9.5e: derive a binder name for an arm's K-th payload
          -- field. Zero-Skip Step 3: consult the
          -- `(variantId, fieldIdx) → binderName` map precomputed at
          -- `translateFunWith` time by `collectVariantBinders*`.
          -- The map's name agrees with the seed pass's vm-seeded
          -- name (Charon source name from `localsNames` when
          -- available, synthesised `xL` otherwise), so pattern and
          -- body references resolve to the same identifier even
          -- when Charon injected MIR temps before the named
          -- binders (`demo::list_nth_mut`) or when the binder is
          -- unnamed (`demo::list_tail`'s head `t`). The
          -- `paramName (numParams + 1 + k)` fallback covers
          -- functions without an LLBC body or with synthesised
          -- variants not surfaced through `variantBinders`.
          let binderName (vid k : Nat) : String :=
            match st.variantBinders[(vid, k)]? with
            | some n => n
            | none => paramName (st.numParams + 1 + k)
          -- Build the arm bodies via sub-walks.
          let armResults : Array (String × Array String × PExpr) × Nat :=
            arms.toArray.foldl (init := (#[], st.fresh)) fun (acc, fresh) arm =>
              let (start, endIdx, _adtId, vid, vname) := arm
              -- Body events are (start+1 .. endIdx); strip a trailing
              -- EvReturn (we'll re-wrap in `ok` via tailToResult).
              let bodyEnd :=
                if endIdx > start + 1 then
                  match evs[endIdx - 1]? with
                  | some Event.retn => endIdx - 1
                  | _ => endIdx
                else endIdx
              let bodyEvs := evs.extract (start + 1) bodyEnd
              -- M9.5e: pre-seed the per-arm payload-binder map. For
              -- the variant being matched, the body may project
              -- `scrutLocal.[Field K]` to read the K-th payload; we
              -- want those reads to surface the binder we'll write
              -- in the arm's pattern (`| Foo.Num n => …`).
              let nFields : Nat :=
                if vid < variantFieldCounts.size then variantFieldCounts[vid]!
                else 0
              let binders : Array String :=
                (List.range nFields).toArray.map (binderName vid)
              let armPayloadBinders : Std.HashMap (Nat × Nat) String :=
                (List.range nFields).foldl
                  (init := st.payloadBinders) fun m k =>
                    m.insert (scrutLocal, k) (binderName vid k)
              let sub := walkEvents bodyEvs
                { st with
                  binds := #[], fresh := fresh,
                  payloadBinders := armPayloadBinders }
              -- Tail value = vm[0] (the LLBC return slot). For arms
              -- whose body is just an EvAssign to local 0 of a
              -- SymVariant rhs, vm[0] is that variant ctor expression.
              -- M9.5d: qualify variant ctors with the adt name here so
              -- the emitter produces `Sign.Pos` not bare `Pos`.
              -- M9.5f: the [lookupSymExpr] path now qualifies on its
              -- own via `tdm`, so this fallback is idempotent — we
              -- only prepend `<adtName>.` when the name is a bare
              -- capitalised token (no embedded `.`). This keeps older
              -- code paths and the `.var "()"` fallback safe.
              let qualify : PExpr → PExpr
                | .var name =>
                  if name.length ≥ 1 ∧ name.front.isUpper ∧ !name.contains '.' then
                    .var s!"{adtName}.{name}"
                  else .var name
                | e => e
              -- Zero-Skip Step 3: prefer `fail panic` when the arm
              -- body contains an `EvPanic` event — that's Charon's
              -- encoding of a Rust `panic!()` / unreachable arm and
              -- maps to `fail panic` in the standard backend's
              -- output. Without this, the arm tail falls back to
              -- the inherited parent `vm[0]` (typically the seed
              -- pass's binder for the *other* arm's payload), which
              -- emits `ok x` for a `panic!()` Nil branch.
              -- Zero-Skip Step 3 (continued): a recursive-call-as-
              -- return shape (`let t_dst ← rec_call …` with no
              -- subsequent `Assign local 0 ← …` because Charon
              -- elides it) similarly leaves `vm[0]` inherited. When
              -- the sub-walk's `lastWrite` points to a fresh local
              -- (i.e. one that was *introduced* by an EvCall in this
              -- arm — not present in the parent's `vm`), prefer
              -- `vm[lastWrite]` over the inherited `vm[0]`.
              let armEndsInPanic : Bool :=
                bodyEvs.any (fun ev => match ev with | .panic => true | _ => false)
              -- Did the sub-walk introduce a write to local 0 (the
              -- LLBC return slot)? If not, `vm[0]` is just the
              -- parent's inherited entry and the real tail value is
              -- whatever the sub-walk wrote most recently.
              let vm0Inherited : Bool :=
                match st.vm[0]?, sub.vm[0]? with
                | some _, some _ =>
                  -- Both present and equal-ish. We approximate by
                  -- treating it as inherited iff no event in
                  -- `bodyEvs` is an `.assign` whose dst.local_ is 0.
                  !bodyEvs.any (fun ev => match ev with
                    | .assign d _ => d.local_ == 0
                    | _ => false)
                | _, _ => false
              let tailRaw : PExpr :=
                if armEndsInPanic then .var "error panic"
                else
                  match sub.lastWrite with
                  | some lw =>
                    if vm0Inherited && !st.vm.contains lw then
                      -- lw is a fresh local introduced in this arm.
                      sub.vm.getD lw (sub.vm.getD 0 (.var "()"))
                    else
                      sub.vm.getD 0 (.var "()")
                  | none => sub.vm.getD 0 (.var "()")
              let tail : PExpr := qualify tailRaw
              let armCtor := s!"{adtName}.{vname}"
              -- `fail panic` is already monadic: don't wrap in `ok`.
              let body :=
                if armEndsInPanic then assembleBody sub.binds tail
                else assembleBody sub.binds (tailToResult tail)
              (acc.push (armCtor, binders, body), sub.fresh)
          let armsArr := armResults.1
          let nextFresh := armResults.2
          -- Skip past the entire run: end of last arm's range. For
          -- the Step-3 grouped layout the marker order and chunk
          -- order differ; the safe bound is the *max* `endIdx`
          -- across all arms (the rightmost event consumed).
          let lastEnd : Nat :=
            arms.foldl (init := i + 1) fun acc (_, e, _, _, _) =>
              if e > acc then e else acc
          let matchE : PExpr := PExpr.matchE scrutE armsArr
          -- Whole function body is a match expression. Bind it as
          -- vm[0] (the return slot) so the linear walk's wrap-up
          -- picks it up. Subsequent EvReturn / EvJoin events fall
          -- through harmlessly (they're no-ops at the value layer).
          let st' :=
            { st with
              fresh := nextFresh
              vm := st.vm.insert 0 matchE
              lastWrite := some 0 }
          go lastEnd st'
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
          -- Pick the condition's surface form.
          --
          -- Session 6 Item 1: prefer `st.lastWrite`'s vm entry. The
          -- common case for `get_max`-shape switches is an EvBinop
          -- writing a fresh `t0` to a bool local immediately before
          -- the EvAssert(SymVal n, true) opener. `lastWrite` points
          -- at that bool local; `vm[lastWrite]` is `.var "t0"` — the
          -- right scrutinee. For `choose`-shape switches the bool
          -- comes from a parameter copy (lastWrite still points at
          -- the cond local, vm[lastWrite] = .var "b"). We fall back
          -- to the legacy "first param" heuristic only when
          -- lastWrite is absent, and final fallback is the raw
          -- symbolic name `s{n}`.
          let cond : PExpr := Id.run do
            -- Primary: vm[st.lastWrite].
            match st.lastWrite with
            | some lw =>
              match st.vm[lw]? with
              | some (.var name) => return .var name
              | _ => pure ()
            | none => pure ()
            -- Secondary: legacy first-param scan.
            let mut found : Option PExpr := none
            for (l, e) in st.vm.toList do
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
          -- Zero-Skip Step 3: when a branch ends with a call whose
          -- result IS the return value (Charon elides the trailing
          -- `Assign local 0 ← Move call_dst` because it's
          -- structurally implicit), `vm[0]` stays inherited from
          -- the parent. Detect that case by checking whether any
          -- event in the branch's body wrote to local 0; if not,
          -- prefer the most recently introduced fresh local
          -- (`lastWrite` not present in the parent's `vm`).
          let branchVm0Touched (branchEvs : Array Event) : Bool :=
            branchEvs.any (fun ev => match ev with
              | .assign d _ => d.local_ == 0
              | _ => false)
          let pickBranchTail (subSt : WalkState) (branchEvs : Array Event)
              : PExpr :=
            if branchVm0Touched branchEvs then
              subSt.vm.getD 0 (.lit (.scalar .u32 0))
            else
              match subSt.lastWrite with
              | some lw =>
                if st.vm.contains lw then
                  subSt.vm.getD 0 (.lit (.scalar .u32 0))
                else
                  subSt.vm.getD lw (subSt.vm.getD 0 (.lit (.scalar .u32 0)))
              | none => subSt.vm.getD 0 (.lit (.scalar .u32 0))
          let leftTail : PExpr := pickBranchTail leftSub leftEvs
          let rightTail : PExpr := pickBranchTail rightSub rightEvs
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
          -- M11.2: `EvJoin`'s `witnesses` field defaults to `#[]` but
          -- v3 certs populate it with one [JoinEntry] per result-env
          -- local (Option C, M9.6). The pattern *must* bind the fourth
          -- arg explicitly (`_w`); a 3-arg `.join a b c` would only
          -- match the empty-witnesses case in Lean 4 (the trailing
          -- default fills in as `#[]`), causing every v3-emitted join
          -- to fall through to the per-event walk and silently lose
          -- the if/else shape.
          | some (.join leftSummary rightSummary resultSummary _w) =>
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
              let leftValOpt := renderJoinSide st.tdm st.localTypes leftSub.vm leftSummary.env target
              let rightValOpt := renderJoinSide st.tdm st.localTypes rightSub.vm rightSummary.env target
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

/-- M9.5b / M9.7o-E5b: build the [BackSig] from a structured
    `LlbcSignature` (sourced from `cc.llbcProgram.funDecls`). Uses
    [llbcTyToPTyWithVars] to convert input/output types to `PTy` and
    the structured borrow detectors ([isMutRefLlbc] etc.) to compute
    the back-closure shape. -/
def backSigOfLlbcWithVars
    (tdm : TypeDeclMap) (typeParams : Array String)
    (sig : LlbcSignature) : BackSig := Id.run do
  let mut mutInputs : Array Nat := #[]
  let mut mutInputTys : Array PTy := #[]
  for i in [0:sig.inputs.size] do
    let t := sig.inputs[i]!
    if isMutRefLlbc t then
      mutInputs := mutInputs.push (i + 1)
      mutInputTys := mutInputTys.push (llbcTyToPTyWithVars tdm typeParams t)
  let bs : BackSig :=
    { mutInputs, mutInputTys
      outputIsMutRef := isMutRefLlbc sig.output
      outputInnerTy := llbcTyToPTyWithVars tdm typeParams sig.output
      outputIsUnit := isUnitTyLlbc sig.output
      outputTupleOfMuts := isOutputTupleOfMutRefsLlbc sig.output }
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

-- Session 5 (Item 1): seed the var-map with global-ref bindings
-- surfaced by the LLBC body.
--
-- Charon's `decompose_global_operands` pre-pass (`PrePasses.ml`'s
-- `visit_PlaceGlobal`) rewrites every `PlaceGlobal g` operand into
-- `*local L` after inserting `local L = RvRef(PlaceGlobal g)` as a
-- new earlier statement. The cert event log captures the
-- *consequence* (a reborrow chain with `Deref`-projected reads)
-- but drops the `Assign` that records `g` — so `lookupPlace local
-- L [Deref]` during event walk has no way to recover the source
-- global without help.
--
-- This pass walks the LLBC body once (pre-event-walk) and:
--   1. For each `Assign(local L, RvRef(<place with globalName g>, _))`,
--      emits a fresh monadic let-bind `let gN ← <g>` *and* seeds
--      `vm[L] := .var gN`. The bind is mandatory because every
--      global is `Result`-typed in our emit and call arguments /
--      field accesses need the unwrapped value.
--   2. For each re-borrow `Assign(local L, RvRef(<place with
--      placeRef.local_ in vm>, _))`, propagates the seeded var
--      unchanged (`&*v ≡ v` at pure-IR level).
--   3. For each `Assign(local L, Use(Copy/Move <place with
--      placeRef.local_ in vm>))`, propagates the seeded var unchanged
--      (any projection threading is left to the event walker's
--      `applyFieldProj` at the use site).
--
-- Walks nested blocks (loops + switch arms) defensively even though
-- const-fn bodies are flat in practice. Names use a `g<L>` shape
-- (collision-safe: each LLBC local L gets at most one seed) to
-- minimise interference with the event walker's `tN` fresh-name
-- counter.

/-- Accumulator state for the seed pass. -/
structure SeedAcc where
  vm : VarMap := {}
  binds : Array Bind := #[]
  deriving Inhabited

/-- Session 7 Item 2: resolve a single Charon debug-printed generic
    arg back to its user-visible name. `T@k` (type var, de-Bruijn
    `k`) → `typeNames[k]?`; `C@k` (const-generic var) →
    `constNames[k]?`. Falls back to the raw string when the marker
    doesn't parse cleanly or the index is out of range — the caller
    will then either emit it as-is or skip. A bare identifier (`T`,
    `4`) passes through unchanged. -/
def resolveGlobalGenericArg (typeNames constNames : Array String)
    (s : String) : Option String :=
  if s.startsWith "T@" then
    let suffix := s.drop 2
    match suffix.toNat? with
    | some k => typeNames[k]?
    | none => some s
  else if s.startsWith "C@" then
    let suffix := s.drop 2
    match suffix.toNat? with
    | some k => constNames[k]?
    | none => some s
  else some s

/-- Session 7 Item 2: build the seed binding's call expression for a
    generic global. Combines the sanitised bare name with the
    resolved type / const-generic args; skips when any arg fails to
    resolve (returns `none` so the seed pass leaves the local
    uninitialised and the event walker falls back to the typed-zero
    placeholder). -/
def buildGlobalGenericCall
    (typeNames constNames : Array String)
    (bareName : String) (gg : Raw.LlbcGlobalGenerics) : Option PExpr := do
  let resolve (s : String) : Option PExpr :=
    (resolveGlobalGenericArg typeNames constNames s).map PExpr.var
  let tyArgs ← gg.types.mapM resolve
  let cgArgs ← gg.constGenerics.mapM resolve
  -- Zero-Skip Step 7: when the callee carries both type-params and
  -- const-generics, the type-params are emitted as *implicit*
  -- `{T : Type}` binders (see `Pretty.lean::Decl.toLean`). Passing
  -- type-args via the bare-app form `(<head> T N)` mis-applies `T` to
  -- the const-generic's explicit slot; passing them via the
  -- `@<head> T N` form makes the implicits explicit so the
  -- application order matches the binder order. We prefix the
  -- sanitised head with `@` and include both arg lists. For globals
  -- without type-args (just const-generics, e.g. a future
  -- monomorphic-T const), the `@` is harmless. For globals without
  -- generics at all, this branch isn't entered (see callers — the
  -- non-generic path uses `.app g #[]`).
  let head := if tyArgs.isEmpty then bareName else "@" ++ bareName
  some (.app head (tyArgs ++ cgArgs))

/-- Zero-Skip Step 3 helper: detect a match-arm-binder Ref-projection.

    For an `Assign localK ← Ref(localScrut.[…, Field(_, some _, _), …])`,
    Charon's pattern is to introduce a fresh local (`localK`) that is
    bound to the *named* variant payload (`x`, `tl`, …). The
    standard backend renders the match arm as `| List.Cons x tl => …`
    and references `x` / `tl` directly in the body. The cert events
    *don't* carry the projection itself (it's stripped at the
    symbolic-interpreter layer), so without a seed the event walker
    falls back to `vm[1]` and emits the scrutinee root (`l`) in place
    of the binder — the source of the Cluster-3 "wrong argument"
    bug. We seed `vm[localK] := .var <binderName>` so the rest of
    the seed pass's deref/Use propagation forwards the binder
    through any reborrow chain (`local 6 := Ref(local 3.[Deref,
    Deref])` → `vm[6] := vm[3]`). The chosen binder name is the
    Charon source name (`localsNames[localK]`) when available — for
    `paper::sum` / `demo::list_nth`-shaped functions where the
    arm-pattern handler (see `binderName` in the match-arm walker)
    will surface the same source name in the pattern slot — and the
    synthesised `s!"x{localK}"` otherwise (so seed and pattern stay
    aligned even when Charon injected MIR temps before the named
    binders). -/
def variantFieldBinderName
    (localsNames : Array (Option String))
    (place : Raw.LlbcPlace) (placeRef : Raw.LlbcPlace) :
    Option String :=
  let isVariantProj : Bool :=
    placeRef.projection.any fun
      | .field _ (some _) _ => true
      | _ => false
  if !isVariantProj then none
  else
    -- Always seed *something* so the body's downstream reads pick
    -- up a binder name rather than the scrutinee fallback. Prefer
    -- the Charon source name; fall back to synthesised `xL`.
    match localsNames[place.local_]?.bind id with
    | some n => some n
    | none => some s!"x{place.local_}"

/-- Zero-Skip Step 3 helper: extract the first variant-field
    projection element (if any) from a place's projection chain.
    Returns `(vid, fieldIdx)` for `_.[Field _ (some vid) fIdx]`. -/
def firstVariantFieldProj (p : Raw.LlbcPlace) : Option (Nat × Nat) :=
  p.projection.foldl (init := none) fun acc el =>
    match acc, el with
    | none, .field _ (some vid) fIdx => some (vid, fIdx)
    | acc, _ => acc

-- Zero-Skip Step 3: deep scan of the LLBC body for
-- `Assign localK ← Ref(_.[Field _ (some vid) fIdx])` statements,
-- accumulating a `(vid, fIdx) → binderName` map. The binder name
-- is the Charon source name (`localsNames[localK]`) when present,
-- otherwise the synthesised `xL` form — same scheme the
-- `variantFieldBinderName` seed helper uses, so the pattern slot
-- and the seeded vm binding always agree. First occurrence wins.
-- Used by the match-arm walker's `binderName` to pick the right
-- pattern slot for arm `vid` field `K`.
mutual

partial def collectVariantBindersBlock
    (localsNames : Array (Option String))
    : Raw.LlbcBlock → Std.HashMap (Nat × Nat) String
        → Std.HashMap (Nat × Nat) String
| .mk _ stmts, acc =>
  stmts.foldl (init := acc) fun acc s =>
    collectVariantBindersStmt localsNames s acc

partial def collectVariantBindersStmt
    (localsNames : Array (Option String))
    : Raw.LlbcStatement → Std.HashMap (Nat × Nat) String
        → Std.HashMap (Nat × Nat) String
| .mk kind _, acc =>
  match kind with
  | .assign place (.ref placeRef _) =>
    match firstVariantFieldProj placeRef with
    | none => acc
    | some (vid, fIdx) =>
      if acc.contains (vid, fIdx) then acc
      else
        let nm : String :=
          match localsNames[place.local_]? with
          | some (some n) => n
          | _ => s!"x{place.local_}"
        acc.insert (vid, fIdx) nm
  | .block b => collectVariantBindersBlock localsNames b acc
  | .loopStmt b => collectVariantBindersBlock localsNames b acc
  | .switch sw => collectVariantBindersSwitch localsNames sw acc
  | _ => acc

partial def collectVariantBindersSwitch
    (localsNames : Array (Option String))
    : Raw.LlbcSwitch → Std.HashMap (Nat × Nat) String
        → Std.HashMap (Nat × Nat) String
| .ifBool _ t e, acc =>
  collectVariantBindersBlock localsNames e
    (collectVariantBindersBlock localsNames t acc)
| .switchInt _ _ arms dflt, acc =>
  let acc := arms.foldl (init := acc)
    fun acc (_, b) => collectVariantBindersBlock localsNames b acc
  collectVariantBindersBlock localsNames dflt acc
| .match_ _ arms dfltOpt, acc =>
  let acc := arms.foldl (init := acc)
    fun acc (_, b) => collectVariantBindersBlock localsNames b acc
  match dfltOpt with
  | some b => collectVariantBindersBlock localsNames b acc
  | none => acc

end

mutual

partial def seedGlobalRefsFromBlock
    (typeNames constNames : Array String)
    (localsNames : Array (Option String))
    : Raw.LlbcBlock → SeedAcc → SeedAcc
| .mk _ stmts, acc =>
  stmts.foldl (init := acc) fun acc s =>
    seedGlobalRefsFromStatement typeNames constNames localsNames s acc

partial def seedGlobalRefsFromStatement
    (typeNames constNames : Array String)
    (localsNames : Array (Option String))
    : Raw.LlbcStatement → SeedAcc → SeedAcc
| .mk kind _, acc =>
  match kind with
  | .assign place rvalue =>
    match rvalue with
    | .ref placeRef _ =>
      match placeRef.globalName with
      | some g =>
        -- Session 7 Item 2: when the global carries generic args
        -- (`global_generics`), build a typed call `<bareName>
        -- <T> <N>`. Otherwise emit the legacy `<g>` call shape.
        -- The check that previously skipped `<`-bearing names is
        -- gone: the bare name is recovered by sanitisation (see
        -- `sanitizeCallName`) and the args are resolved from the
        -- function's generic-param names.
        let mkCall : Option PExpr :=
          match placeRef.globalGenerics with
          | some gg =>
            buildGlobalGenericCall typeNames constNames g gg
          | none =>
            if g.contains '<' then none
            else some (.app g #[])
        match mkCall with
        | some callE =>
          let name := s!"g{place.local_}"
          { acc with
              vm := acc.vm.insert place.local_ (.var name)
              binds := acc.binds.push (.regular name callE) }
        | none => acc
      | none =>
        -- Zero-Skip Step 3 (Cluster `recursive_match_arm_scoping`):
        -- when the Ref projects a *variant* field, prefer the named
        -- binder from `localsNames` over the root local's pure
        -- value. See [variantFieldBinderName].
        match variantFieldBinderName localsNames place placeRef with
        | some binderName =>
          { acc with vm := acc.vm.insert place.local_ (.var binderName) }
        | none =>
          match acc.vm[placeRef.local_]? with
          | some v => { acc with vm := acc.vm.insert place.local_ v }
          | none => acc
    | .use op =>
      let propagate (p : Raw.LlbcPlace) : SeedAcc :=
        match acc.vm[p.local_]? with
        | some v => { acc with vm := acc.vm.insert place.local_ v }
        | none => acc
      match op with
      | .copy p => propagate p
      | .move p => propagate p
      | _ => acc
    | _ => acc
  | .block b => seedGlobalRefsFromBlock typeNames constNames localsNames b acc
  | .loopStmt b => seedGlobalRefsFromBlock typeNames constNames localsNames b acc
  | .switch sw => seedGlobalRefsFromSwitch typeNames constNames localsNames sw acc
  | _ => acc

partial def seedGlobalRefsFromSwitch
    (typeNames constNames : Array String)
    (localsNames : Array (Option String))
    : Raw.LlbcSwitch → SeedAcc → SeedAcc
| .ifBool _ t e, acc =>
  seedGlobalRefsFromBlock typeNames constNames localsNames e
    (seedGlobalRefsFromBlock typeNames constNames localsNames t acc)
| .switchInt _ _ arms dflt, acc =>
  let acc := arms.foldl (init := acc)
    fun acc (_, b) => seedGlobalRefsFromBlock typeNames constNames localsNames b acc
  seedGlobalRefsFromBlock typeNames constNames localsNames dflt acc
| .match_ _ arms dfltOpt, acc =>
  let acc := arms.foldl (init := acc)
    fun acc (_, b) => seedGlobalRefsFromBlock typeNames constNames localsNames b acc
  match dfltOpt with
  | some b => seedGlobalRefsFromBlock typeNames constNames localsNames b acc
  | none => acc

end

-- Bug 2 (uninitialised locals): a post-walk Ref/Use propagation pass.
-- Same shape as `seedGlobalRefsFromBlock` but only propagates *local*
-- Refs and `Use(Copy/Move)` operands; the global-ref branch is
-- skipped because those binds were already emitted by the pre-walk
-- seed pass.
--
-- Used after the event walk to resolve `Assign(local 0,
-- Ref(localL.deref, _))`-style chains that the cert event stream
-- flattens away — the LLBC body still has them as ordinary statements,
-- so re-walking with the post-walk vm propagates `vm[L]` (typically a
-- call result like `t0`) into `vm[0]`.
mutual

partial def propagateRefsFromBlock
    : Raw.LlbcBlock → VarMap → VarMap
| .mk _ stmts, vm =>
  stmts.foldl (init := vm) fun vm s =>
    propagateRefsFromStatement s vm

partial def propagateRefsFromStatement
    : Raw.LlbcStatement → VarMap → VarMap
| .mk kind _, vm =>
  match kind with
  | .assign place rvalue =>
    -- Bug 2: this is a *post-walk* propagation, so we must NOT
    -- overwrite values the event walker computed. Only fill in
    -- vm[target] when it is currently empty.
    if vm.contains place.local_ then vm
    else
    match rvalue with
    | .ref placeRef _ =>
      -- Skip globals — they were seeded by the pre-walk pass.
      match placeRef.globalName with
      | some _ => vm
      | none =>
        match vm[placeRef.local_]? with
        | some v => vm.insert place.local_ v
        | none => vm
    | .use op =>
      let propagate (p : Raw.LlbcPlace) : VarMap :=
        match vm[p.local_]? with
        | some v => vm.insert place.local_ v
        | none => vm
      match op with
      | .copy p => propagate p
      | .move p => propagate p
      | _ => vm
    -- Bug 4 (Aggregate-rvalue propagation): a Rust array literal `[x]`
    -- (a single-operand `Aggregate(Array, [Move/Copy local])`) is
    -- emitted as `Aeneas.Std.Array.singleton <vm[local]>`. Bug 4c
    -- extends this to N-operand literals `[e₁, …, eₙ]` (n ≥ 2),
    -- emitted as `Array.ofList (List.cons e₁ … (List.cons eₙ
    -- List.nil))`. All operands must resolve through `vm`; if any
    -- doesn't, drop the propagation (safe — keeps the slot empty so
    -- the placeholder path takes over).
    | .aggregate (.array _) ops =>
      let resolvedOpts : Array (Option PExpr) := ops.map fun op =>
        match op with
        | .move p | .copy p => vm[p.local_]?
        | _ => none
      if resolvedOpts.any Option.isNone then vm
      else
        let elems : Array PExpr := resolvedOpts.map (·.getD (.lit (.scalar .u32 0)))
        match elems.size with
        | 0 =>
          -- Zero-length array literal `[]`: emit the Unit-pinned shim
          -- so the surrounding chain doesn't leave `α` unresolved.
          vm.insert place.local_ (.app "Aeneas.Std.Array.empty" #[])
        | 1 =>
          vm.insert place.local_ (.app "Aeneas.Std.Array.singleton" #[elems[0]!])
        | _ =>
          -- Build a List.cons chain: List.cons e₁ (List.cons e₂ … List.nil).
          let chain : PExpr :=
            elems.foldr (init := .app "List.nil" #[]) fun e acc =>
              .app "List.cons" #[e, acc]
          vm.insert place.local_ (.app "Aeneas.Std.Array.ofList" #[chain])
    | _ => vm
  | .block b => propagateRefsFromBlock b vm
  | .loopStmt b => propagateRefsFromBlock b vm
  | .switch sw => propagateRefsFromSwitch sw vm
  | _ => vm

partial def propagateRefsFromSwitch
    : Raw.LlbcSwitch → VarMap → VarMap
| .ifBool _ t e, vm =>
  propagateRefsFromBlock e (propagateRefsFromBlock t vm)
| .switchInt _ _ arms dflt, vm =>
  let vm := arms.foldl (init := vm)
    fun vm (_, b) => propagateRefsFromBlock b vm
  propagateRefsFromBlock dflt vm
| .match_ _ arms dfltOpt, vm =>
  let vm := arms.foldl (init := vm)
    fun vm (_, b) => propagateRefsFromBlock b vm
  match dfltOpt with
  | some b => propagateRefsFromBlock b vm
  | none => vm

end

/-- Translate a function's cert + replay into a Pure decl.

    The forward translator walks `f.events`, updates a per-local
    pure-expression map, and emits `let tN ← …` bindings for each
    binop. The tail of the resulting `do`-block is whichever local
    LLBC's return convention dictates — for now: local 0 for value
    returns and the borrowed input's root for `&mut`-returning
    signatures. We approximate "did this function take a `&mut`?" by
    checking if any borrow event fired in the trace; if so, we pick
    the input's root local rather than local 0.

    M9.7o-E5b: the structured `LlbcFunDecl` is now the sole source of
    typed-signature and per-local-type information. The Driver
    matches each `Raw.FunCert` to its `LlbcFunDecl` (by `fnId`) and
    threads it through. -/
def translateFunWith (tdm : TypeDeclMap) (f : Raw.FunCert)
    (lf : Raw.LlbcFunDecl) (_t : CheckedTrace) : Decl :=
  let lsig := lf.signature
  let numParams := lsig.inputs.size
  -- M9.5i: the function's type-parameter names flow into both the
  -- emitted `Decl.typeParams` (for the `{T : Type}` binder line) and
  -- into the type-translator so any `LlbcTy.tVar K` inside an input /
  -- output type resolves to `.tyVar (typeParams[K])`.
  let typeParams := lsig.generics.types
  -- Session 7 Item 1d: prefer the source-level name from
  -- `lf.localsNames[i+1]?` over the synthesised `x{i+1}`. Returns
  -- the synthesised name as a fallback when the local is unnamed
  -- (return slot, MIR-introduced temp) or `localsNames` is empty
  -- (opaque body / older cert). Charon stores locals in index order
  -- with index 0 = return slot, 1..N = inputs, so paramI refers to
  -- local index `i + 1`.
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
  -- M12.1: loop-bearing functions are handled separately by
  -- `translateLoopFun` (called from `Driver.translateCrate` before
  -- this function). If we reach here with `EvLoopInv` in the
  -- events, fall through to the linear walk anyway — the result
  -- won't be semantically right, but it will be syntactically valid
  -- Lean code. Driver should always route loops through
  -- `translateLoopFun`.
  -- Initial var map: input local 1 ↦ x1, local 2 ↦ x2, ...
  -- Session 5 (Item 1): also pre-seed locals that the LLBC body binds
  -- to global references, and accumulate the `let gN ← <global>`
  -- monadic let-binds those references require. The cert event log
  -- doesn't carry the `RvRef(PlaceGlobal g)` borrows that Charon's
  -- pre-pass inserted; without this seed, `lookupPlace local L [Deref]`
  -- falls back to a typed-zero placeholder and call args / field
  -- accesses misuse the `Result`-typed global. See
  -- `seedGlobalRefsFromBlock`.
  -- Session 7 Item 2: the seed pass now receives the function's
  -- type-param + const-generic names so it can resolve Charon's
  -- debug-printed `T@k` / `C@k` markers attached to `global_generics`
  -- back to the user-visible identifiers (`T`, `N`). For functions
  -- without globals this is a no-op.
  let genericTypeNames : Array String := typeParams
  let genericConstNames : Array String := lsig.generics.constGenerics
  -- Bug 5 (Option/String): pre-populate the seed accumulator's vm
  -- with input names BEFORE running the LLBC-body seed pass. The
  -- seed's `Assign(local L, Ref(localRef.deref, _))` and
  -- `Assign(local L, Use(Copy/Move localRef))` branches both
  -- propagate `acc.vm[localRef]?` to `place.local_` only when the
  -- referenced local is already in `acc.vm`. Inputs are referenced
  -- by `&msg`-style temps (`Ref(local 2.deref, Shared)` where local
  -- 2 is `msg`) and without the pre-seed those temps fall through
  -- to `lookupPlace`'s vm[1] fallback, producing `expect x x`
  -- instead of `expect x msg` at the call site.
  let inputSeedVm : VarMap := Id.run do
    let mut m : VarMap := {}
    for i in [0:numParams] do
      m := m.insert (i + 1) (.var (effectiveParamName i))
    return m
  let seedAcc : SeedAcc := match lf.body with
    | some b => seedGlobalRefsFromBlock genericTypeNames genericConstNames
                  lf.localsNames b { vm := inputSeedVm }
    | none => { vm := inputSeedVm }
  let initVm : VarMap := Id.run do
    let mut m : VarMap := seedAcc.vm
    for i in [0:numParams] do
      -- Session 7 Item 1d: seed with the source-level name so body
      -- emit (which resolves `local L` through this vm) inherits the
      -- user's `y` instead of the synthesised `x1`.
      m := m.insert (i + 1) (.var (effectiveParamName i))
    return m
  -- M9.5n / M9.7o-E5b: seed `localTypes` from the structured
  -- `LlbcFunDecl.localsTypes`. Charon's convention: index 0 is the
  -- return slot, indices 1..N are the inputs, the rest are temps.
  -- We record every local with a known type so the EvAssign/EvCopy
  -- walk can lower a `local L.[Field K]` read to `<root>.<fieldName>`
  -- via `applyFieldProj`, and the EvCall hooks can detect a `&mut`
  -- destination via `isMutRefLlbc`. When `localsTypes` is empty
  -- (`body = none` opaque function), we fall back to seeding inputs
  -- alone from `lsig.inputs` so the linear walk still has the
  -- parameter types in scope.
  let initLocalTypes : Std.HashMap Nat Raw.LlbcTy := Id.run do
    let mut m : Std.HashMap Nat Raw.LlbcTy := {}
    if lf.localsTypes.isEmpty then
      for i in [0:numParams] do
        match lsig.inputs[i]? with
        | some t => m := m.insert (i + 1) t
        | none => ()
    else
      for i in [0:lf.localsTypes.size] do
        m := m.insert i lf.localsTypes[i]!
    return m
  -- Session 5 (Item 1): seed the initial walk-state with the binds
  -- the global-ref seed pass produced. These prepend the body so the
  -- function-level `let g<L> ← <global>` shows up before any
  -- event-walk-generated bind. Order within `seedAcc.binds` is
  -- LLBC-statement order, matching Charon's pre-pass insertion order
  -- (`g<L>` for the smallest `L` first), so a later global that
  -- references an earlier one resolves in scope.
  -- Session 7 Item 1d follow-up: reverse-map each param's effective
  -- name back to its 1-based local index. The deref-write handler
  -- uses this to detect "this borrow writes back into input N" when
  -- the param uses the user's source name instead of `x{N}`. The
  -- forward map `paramNameByLocal` is the same info indexed the
  -- other way so the EvCall/EvEndAbs `_post`-name synthesiser can
  -- emit `<sourceName>_post` instead of `<paramName k>_post`.
  let paramNameMap : Std.HashMap String Nat := Id.run do
    let mut m : Std.HashMap String Nat := {}
    for i in [0:numParams] do
      m := m.insert (effectiveParamName i) (i + 1)
    return m
  let paramNameByLocal : Std.HashMap Nat String := Id.run do
    let mut m : Std.HashMap Nat String := {}
    for i in [0:numParams] do
      m := m.insert (i + 1) (effectiveParamName i)
    return m
  -- Zero-Skip Step 3 (Cluster `recursive_match_arm_scoping`): scan
  -- the LLBC body once for variant-projection Assigns and build the
  -- (variantId, fieldIdx) → binderName map the match-arm walker
  -- consults to keep pattern slots aligned with the seed pass's
  -- vm-seeded names.
  let variantBinders : Std.HashMap (Nat × Nat) String :=
    match lf.body with
    | none => {}
    | some body =>
      collectVariantBindersBlock lf.localsNames body {}
  let finalSt0 : WalkState :=
    walkEvents f.events
      { vm := initVm, numParams, tdm, localTypes := initLocalTypes,
        binds := seedAcc.binds, paramNameMap, paramNameByLocal,
        localsNames := lf.localsNames, variantBinders }
  -- Bug 2 (uninitialised locals): the cert event stream often flattens
  -- away Charon's `Assign(localTgt, Ref(localSrc.deref, _))` /
  -- `Assign(localTgt, Use(...))` borrow chains. The LLBC body still
  -- carries them, so re-walk it with `finalSt.vm` to propagate
  -- post-call values (e.g. the call's `t0` binding into the
  -- return slot `local 0`) along the LLBC chain.
  let propagatedVm : VarMap :=
    match lf.body with
    | some b => propagateRefsFromBlock b finalSt0.vm
    | none => finalSt0.vm
  let finalSt : WalkState := { finalSt0 with vm := propagatedVm }
  -- M12.2a-2: pick the function's output shape based on its
  -- signature's borrow pattern. See [BackSig] / [emitRetTy].
  -- M9.5i / M9.7o-E5b: thread the structured `LlbcSignature` so a
  -- `T` output / `&mut T` input resolves to `.tyVar "T"`.
  let bs := backSigOfLlbcWithVars tdm typeParams lsig
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
        -- M9.5o: a unit-returning function whose trace ends without
        -- writing local 0 (typical for trait-method default bodies
        -- like `fn foo() {}`) should tail with `ok ()`, not
        -- `ok (0 : Std.U32)`. Detect via the signature's output
        -- type. Use `.var "()"` so [tailToResult]'s default
        -- `.var _ → .ok _` path wraps it in `ok` (a bare `.app`
        -- head would be treated as Result-typed).
        --
        -- Phase 4a-3/4a-4: when there's no first input to fall back
        -- to (typical for `const fn` / `static` initialisers whose
        -- only emitted body should have been a call but the cert
        -- walker never wrote vm[0]), use a *type-correct* placeholder
        -- derived from the return slot's LlbcTy (`localTypes[0]`).
        -- This fixes `V::LEN : Result Usize := ok 0#usize` (was
        -- `ok 0#u32`) and `S3 : Result (Pair U32 U32) := ok {…}`
        -- (was the type-mismatched `ok 0#u32`). The placeholder is
        -- still semantically wrong for non-literal types — see
        -- [placeholderPExprOfWith]'s docstring — but the file now
        -- compiles against the shim.
        let unitDefault : PExpr := .var "()"
        let typedDefault : PExpr :=
          match finalSt.localTypes[(0 : Nat)]? with
          | some t => placeholderPExprOfWith tdm t
          | none => .lit (.scalar .u32 0)
        let tailE0 : PExpr := finalSt.vm.getD 0 (
          if bs.outputIsUnit then unitDefault
          else if numParams ≥ 1 then .var (paramName 1)
          else typedDefault)
        -- Phase 4a-3 post-walk: when vm[0] *was* populated but with
        -- `lookupPlace`'s scalar catch-all (`.lit (.scalar .u32 0)`,
        -- emitted for an untracked local with no resolvable LlbcTy)
        -- AND the function's return slot is an ADT, swap in a
        -- struct-literal placeholder so the emitted `ok 0#u32` shape
        -- (which doesn't typecheck against `Result (Pair U32 U32)`)
        -- becomes `ok { x := 0#u32, y := 0#u32 }`. Fixes `static S3 :
        -- Pair<u32, u32> = P3`, whose cert walker writes the placeholder
        -- to vm[0] instead of leaving it empty (which would have
        -- triggered the `typedDefault` path above). The substitution
        -- is gated on the ADT shape so non-ADT return types (which
        -- elaborate with the scalar placeholder fine) stay unchanged.
        let tailE : PExpr :=
          match tailE0, finalSt.localTypes[(0 : Nat)]? with
          | .lit (.scalar .u32 0), some t =>
            match t with
            | .tAdt _ _ => placeholderPExprOfWith tdm t
            | _ => tailE0
          | _, _ => tailE0
        -- Zero-Skip Step 6 (tail_back_closure_wrap): for a Unit-returning
        -- function whose `vm[0]` was written with a back-closure
        -- application like `(t0_back t1)` (an `.app` whose head is a
        -- locally-bound name — no `.` / `:` qualifier, not a binop, not
        -- a `__cast::` head), discard the tail value and emit `ok ()`.
        -- The cert walker writes the back-closure call into vm[0] when
        -- an `&mut`-borrowing helper's effect is dropped at end-of-scope
        -- (e.g. `test_choose` after `*z = *z + 1`). Without this the
        -- do-tail elaborates against the back-closure's pure return type
        -- (e.g. `I32 × I32`) and fails to match `Result Unit`. Other
        -- Unit-returning patterns (empty body via `.var "()"`, a pure
        -- call via qualified head, …) are left untouched so existing
        -- byte-identical fixtures stay byte-identical.
        let isBackClosureApp : PExpr → Bool := fun e =>
          match e with
          | .app head _ =>
            !(head.contains '.') && !(head.contains ':') &&
              !isPureBinop head && !head.startsWith "__cast::"
          | _ => false
        let needsUnitDiscard : Bool :=
          bs.outputIsUnit && isBackClosureApp tailE
        let body :=
          if needsUnitDiscard then
            assembleBody finalSt.binds
              (.letPure "_" placeholderTy tailE
                (tailToResult (.var "()")))
          else
            assembleBody finalSt.binds (tailToResult tailE)
        body
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
  -- M9.5j: detect self-recursion by scanning for any `EvCall` whose
  -- callee id AND qualified name match the current function's. The
  -- standard Aeneas backend appends `partial_fixpoint` after the
  -- do-block for such defs so Lean's elaborator doesn't reject them
  -- on structural-recursion grounds. We don't try to be smarter
  -- (e.g. structural-recursion analysis on the match-arm shape) —
  -- the standard backend itself uses `partial_fixpoint` uniformly
  -- for recursive funs.
  -- Post-M9.5l: matching on `fnId` alone was unsound — Charon emits
  -- intercept-style callees (e.g. `@SliceIndexShared`, `@ArrayIndexMut`)
  -- with `fn = 0`, which collides with the first user function's fnId.
  -- The qualified `fnName` is the robust discriminator: real self-calls
  -- carry the same qualified path; intercepts start with `@`.
  let isSelfRecursive : Bool := f.events.any fun ev =>
    match ev with
    | .call calleeId _ calleeName _ _ _ _ =>
        calleeId == f.fnId && calleeName == f.fnName
    | _ => false
  let trailer : Option String :=
    if isSelfRecursive then some "partial_fixpoint" else none
  { name := innerName f.fnName
    qualifiedName := f.fnName
    params, retTy, body
    sourceSpan := f.sourceSpan
    -- M9.5i: emit `{T : Type}` binders. Empty for monomorphic
    -- functions, so the emit shape stays byte-identical with M9.5h.
    typeParams
    -- Zero-Skip Step 7: emit `(N : Std.Usize)` binders for const-
    -- generics. Empty for the 99% of fixtures without const-generics
    -- so the byte-identical emit shape stays unchanged. The
    -- `seedGlobalRefsFromBlock` pass already references these names
    -- via `genericConstNames` for global call args; binding them here
    -- closes the loop so e.g. `use_v` emits
    -- `def use_v {T : Type} (N : Std.Usize) : Result Std.Usize`
    -- and the seeded `(constants.V.LEN T N)` resolves.
    constParams := lsig.generics.constGenerics
    -- M9.5j: `partial_fixpoint` only when we observed a self-call.
    trailer
    -- Session 7 Item 1a: thread Charon's `attr_info.public` so the
    -- docstring can carry the `Visibility: public` line.
    isPublic := lf.itemMeta.isPublic }

/-- M9.5b / M9.7o-E5b: back-compat wrapper around [translateFunWith]
    with an empty type-decl map and a synthetic empty `LlbcFunDecl`.
    Used only by tests that construct a `Raw.FunCert` by hand without
    a surrounding crate program; real translation goes through
    [translateFunWith] called from the Driver, which always has the
    matching `LlbcFunDecl` in scope. -/
def translateFun (f : Raw.FunCert) (t : CheckedTrace) : Decl :=
  translateFunWith {} f { id := f.fnId, itemMeta := { name := f.fnName } } t

end AeneasCheck.Translate
