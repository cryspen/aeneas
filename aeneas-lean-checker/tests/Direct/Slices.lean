import AeneasCheck

/-!
M9.5g: slice support (`&[T]` immutable read + `&mut [T]` write).

The fixture `slices_basic.rs` defines two minimal functions:

* `get_first(xs: &[u32]) -> u32 { xs[0] }` — immutable slice
  indexing. The cert emits an `EvCall("@SliceIndexShared", _, _)`
  with a non-empty `region_abs`; the M9.5g intercept lowers it
  directly to `Slice.index_usize xs 0` and bypasses the
  generic regionAbs-aware pair-destructure path that the call
  walker would otherwise apply.

* `set_idx_slice(xs: &mut [u32], i: usize, v: u32) { xs[i] = v; }` —
  mutable slice indexing. The cert emits
  `EvCall("@SliceIndexMut", _, _)` followed by a deref-EvAssign
  through the call's dst local; the M9.5g intercept stashes the
  slice/index pair at call time and consumes it at the deref-write
  to emit a single `Slice.update xs i v` binding, mirroring M9.5c's
  `@ArrayIndexMut` → `Array.update` lowering.

This test asserts on the rendered source for both functions and
includes negative-substring checks pinning the slice-vs-array
distinction: `Slice Std.U32` must show up in both signatures and
neither function may carry an `Array Std.U32 _#usize` (the M9.5c
shape, which would indicate the slice was mis-classified as a
fixed-size array).
-/

open AeneasCheck Json LLBCSharp Typecheck Translate Backends

def expectAccept (path : System.FilePath) : IO Unit := do
  let cc ← readCrateCert path
  match checkCrateCert cc with
  | .ok _ => IO.println s!"  ✓ {path} typechecks"
  | .error errs =>
    for e in errs do IO.eprintln s!"    {e}"
    throw <| IO.userError s!"expected accept, got reject: {path}"
  match replayCrate cc with
  | .ok _ => IO.println s!"  ✓ {path} replays"
  | .error msg =>
    IO.eprintln s!"    {msg}"
    throw <| IO.userError s!"expected replay, got error: {path}"
  match translateCrate cc with
  | .ok tc => IO.println s!"  ✓ {path} translates ({tc.decls.size} decls)"
  | .error msg =>
    throw <| IO.userError s!"expected translate, got: {msg}"

/-- Count events of a given shape across all functions in the cert. -/
def countEvents (cc : Raw.CrateCert) (pred : Raw.Event → Bool) : Nat :=
  cc.functions.foldl (init := 0) fun acc f =>
    acc + (f.events.foldl (init := 0) fun a e => if pred e then a + 1 else a)

def main : IO Unit := do
  IO.println "M9.5g slice tests:"
  expectAccept "tests/Direct/slices_basic.cert.json"
  -- Shape sanity: each function carries one `@SliceIndex*` EvCall —
  -- `@SliceIndexShared` for `get_first`, `@SliceIndexMut` for
  -- `set_idx_slice`. If the cert ever loses one (e.g. an OCaml-side
  -- bug suppresses the indexing call), the intercepts in
  -- Translate/Forward.lean would have nothing to fire on and the
  -- emitted source would silently regress.
  let cc ← readCrateCert "tests/Direct/slices_basic.cert.json"
  let nShared := countEvents cc fun
    | .call _ _ name _ _ _ => name == "@SliceIndexShared"
    | _ => false
  let nMut := countEvents cc fun
    | .call _ _ name _ _ _ => name == "@SliceIndexMut"
    | _ => false
  if nShared = 1 then
    IO.println s!"  ✓ saw {nShared} @SliceIndexShared event"
  else
    throw <| IO.userError s!"expected 1 @SliceIndexShared event, saw {nShared}"
  if nMut = 1 then
    IO.println s!"  ✓ saw {nMut} @SliceIndexMut event"
  else
    throw <| IO.userError s!"expected 1 @SliceIndexMut event, saw {nMut}"
  -- End-to-end: translate + emit, then assert on the rendered source.
  -- Param-name (`x1`/`x2`/`x3` vs. Rust source names `xs`/`i`/`v`)
  -- and literal-style (`(0 : Std.Usize)` vs `0#usize`) cosmetic
  -- diffs are allowed per the M9.5g done criteria.
  match translateCrate cc with
  | .error e => throw <| IO.userError s!"translate failed: {e}"
  | .ok tc =>
    let src := emitTranslatedCrate "slices_basic" tc
    let mustContain : List String := [
      -- get_first: `&[u32] -> u32` lowers to `Slice Std.U32 ->
      -- Result Std.U32` with a single `Slice.index_usize` call in
      -- the body. The `(0 : Std.Usize)` literal style is the
      -- checker's; the standard backend prints `0#usize` — both
      -- elaborate identically against the RuntimeShim.
      "def get_first (x1 : Slice Std.U32) : Result Std.U32 := do",
      "Slice.index_usize x1 (0 : Std.Usize)",
      -- set_idx_slice: `&mut [u32]` post-state surfaces as the bare
      -- `Slice Std.U32`. The body is a single `Slice.update`
      -- call. As with M9.5c's `Array.update`, the outer parens
      -- around the tail app are the checker's `PExpr.app`
      -- pretty-print convention; the standard backend emits the
      -- bare form — cosmetic-only.
      "def set_idx_slice (x1 : Slice Std.U32) (x2 : Std.Usize) (x3 : Std.U32) : Result (Slice Std.U32) := do",
      "Slice.update x1 x2 x3"
    ]
    for c in mustContain do
      if (src.splitOn c).length < 2 then
        IO.eprintln s!"  ✗ missing expected substring: {c}"
        IO.eprintln src
        throw <| IO.userError "slices_basic output regressed"
      else
        IO.println s!"  ✓ contains: {c}"
    -- Negative checks: a slice MUST NOT be confused with a fixed
    -- array. `Array Std.U32 ...#usize` is the M9.5c rendering for
    -- `[u32; N]`; if either function's signature carries that
    -- shape, the slice was misclassified by `rawTyToPTyWith`.
    -- Similarly the standard backend's `@SliceIndex*` symbols
    -- should NEVER show up in the emitted source — they're
    -- Charon-internal builtins that the M9.5g intercepts replace
    -- with `Slice.index_usize` / `Slice.update`. Seeing them in
    -- the output means the intercept didn't fire.
    let mustNotContain : List String := [
      "Array Std.U32",
      "@SliceIndexShared",
      "@SliceIndexMut",
      -- Post-M9.5l regression guard: neither `get_first` nor
      -- `set_idx_slice` is self-recursive. The cert call's `fn` field
      -- is `0` for `@SliceIndex*` intercepts (a Charon-side legacy)
      -- which collides with `get_first`'s own `fn_id = 0`, so the
      -- pre-fix `isSelfRecursive` test (fnId-only) misclassified the
      -- call and appended `partial_fixpoint`. The fix matches on
      -- qualified `fnName` as well; if that ever regresses, this
      -- substring check fires.
      "partial_fixpoint"
    ]
    for c in mustNotContain do
      if (src.splitOn c).length ≥ 2 then
        IO.eprintln s!"  ✗ unexpected substring present: {c}"
        IO.eprintln src
        throw <| IO.userError "slices_basic output contains a forbidden substring"
      else
        IO.println s!"  ✓ absent: {c}"
  IO.println "all tests passed"
