# G_byte divergence report

Compared 89 fixtures' L₀ (mainline `aeneas -backend lean`) vs L₁ (our `aeneas-check`) emit, per-decl.

## Topline

- File-level byte-identical: **3**
- L₀ emit failed: **3**
- L₁ emit failed: **0**
- Divergent fixtures: **83**
- Total divergent (decl, fixture) pairs: **1417**

## Patterns by frequency

| Pattern | Count | What it means |
|---|---|---|
| `other` | 459 | Catch-all — not matched by any heuristic. |
| `only_in_L1` | 292 | Decl emitted by our cert-walker only. |
| `only_in_L0` | 276 | Decl emitted by mainline only. |
| `bind_arrow_count_diff` | 171 | Different number of `←` monadic binds. |
| `decl_body_size_diff` | 84 | Different number of `:=` definitions inside the slice. |
| `missing_backward_closure` | 65 |  |
| `l1_placeholder_emit` | 25 | L₁ emits a `.placeholder` shim (Bug 4d/4f); L₀ has the real value. |
| `comment_only` | 20 | Differs only inside docstrings / line comments. |
| `wrong_backward_closure_domain` | 14 |  |
| `l1_type_ascription` | 10 | L₁ wraps a value in `((<x> : <ty>))` (Bug 4f `__typed::`); L₀ doesn't. |
| `tuple_collapse` | 1 | L₀ collapses a unit-field struct to a `def NAME := A × B`; L₁ keeps `structure`. |

## Examples (up to 3 per pattern)

### `other`

<details><summary><code>adt-borrows</code> · `SharedList.pop`</summary>

**L₀ (mainline):**
```lean
def SharedList.pop
  {T : Type} (self : SharedList T) : Result (T × (SharedList T)) := do
  match self with
  | SharedList.Nil => fail panic
  | SharedList.Cons hd tl => ok (hd, tl)
```

**L₁ (ours):**
```lean
def SharedList.pop {T : Type} (self : SharedList T) : Result (T × SharedList T) := do
  match self with
  | SharedList.Nil => error panic
  | SharedList.Cons x2 x3 => ok (0#u32, x3)
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,5 +1,4 @@
-def SharedList.pop
-  {T : Type} (self : SharedList T) : Result (T × (SharedList T)) := do
+def SharedList.pop {T : Type} (self : SharedList T) : Result (T × SharedList T) := do
   match self with
-  | SharedList.Nil => fail panic
-  | SharedList.Cons hd tl => ok (hd, tl)
+  | SharedList.Nil => error panic
+  | SharedList.Cons x2 x3 => ok (0#u32, x3)
```

</details>

<details><summary><code>adt-borrows</code> · `SharedWrapper.unwrap`</summary>

**L₀ (mainline):**
```lean
def SharedWrapper.unwrap {T : Type} (self : SharedWrapper T) : Result T := do
  ok self
```

**L₁ (ours):**
```lean
def SharedWrapper.unwrap {T : Type} (self : SharedWrapper T) : Result T := do
  ok self.field0
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,2 +1,2 @@
 def SharedWrapper.unwrap {T : Type} (self : SharedWrapper T) : Result T := do
-  ok self
+  ok self.field0
```

</details>

<details><summary><code>adt-borrows</code> · `array_shared_borrow`</summary>

**L₀ (mainline):**
```lean
def array_shared_borrow
  {N : Std.Usize} (x : Array Std.U32 N) : Result (Array Std.U32 N) := do
  ok x
```

**L₁ (ours):**
```lean
def array_shared_borrow (N : Std.Usize) (x : Array Std.U32 0#usize) : Result (Array Std.U32 0#usize) := do
  ok x
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,3 +1,2 @@
-def array_shared_borrow
-  {N : Std.Usize} (x : Array Std.U32 N) : Result (Array Std.U32 N) := do
+def array_shared_borrow (N : Std.Usize) (x : Array Std.U32 0#usize) : Result (Array Std.U32 0#usize) := do
   ok x
```

</details>

### `only_in_L1`

<details><summary><code>array_slice_index</code> · `RangeFrom`</summary>

**L₀ (mainline):**
```lean

```

**L₁ (ours):**
```lean
structure RangeFrom (Idx : Type) where
  start : Idx
```

</details>

<details><summary><code>arrays</code> · `SZ`</summary>

**L₀ (mainline):**
```lean

```

**L₁ (ours):**
```lean
def SZ : Result Std.Usize := do
  ok 32#usize
```

</details>

<details><summary><code>builtin-auto</code> · `Error`</summary>

**L₀ (mainline):**
```lean

```

**L₁ (ours):**
```lean
def Error := Unit
```

</details>

### `only_in_L0`

<details><summary><code>builtin-auto</code> · `U32.Insts.Builtin_autoSuperPointee`</summary>

**L₀ (mainline):**
```lean
def U32.Insts.Builtin_autoSuperPointee : SuperPointee Std.U32 := {
}

end builtin_auto
```

**L₁ (ours):**
```lean

```

</details>

<details><summary><code>const-shadow</code> · `Foo.Insts.Const_shadowHasConst4`</summary>

**L₀ (mainline):**
```lean
def Foo.Insts.Const_shadowHasConst4 : HasConst Foo 4#usize := {
  N := ok Foo.Insts.Const_shadowHasConst4.N
  get := Foo.Insts.Const_shadowHasConst4.get
}
```

**L₁ (ours):**
```lean

```

</details>

<details><summary><code>const-shadow</code> · `Foo.Insts.Const_shadowHasConst4.get`</summary>

**L₀ (mainline):**
```lean
def Foo.Insts.Const_shadowHasConst4.get
  (self : Foo) : Result (Array Std.U8 4#usize) := do
  ok (Array.repeat 4#usize 0#u8)
```

**L₁ (ours):**
```lean

```

</details>

### `bind_arrow_count_diff`

<details><summary><code>adt-borrows</code> · `SharedList.push`</summary>

**L₀ (mainline):**
```lean
def SharedList.push
  {T : Type} (self : SharedList T) (x : T) : Result (SharedList T) := do
  ok (SharedList.Cons x self)
```

**L₁ (ours):**
```lean
def SharedList.push {T : Type} (self : SharedList T) (x : T) : Result (SharedList T) := do
  let self_post ← (alloc.boxed.Box.new self)
  ok (SharedList.Cons x self_post)
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,3 +1,3 @@
-def SharedList.push
-  {T : Type} (self : SharedList T) (x : T) : Result (SharedList T) := do
-  ok (SharedList.Cons x self)
+def SharedList.push {T : Type} (self : SharedList T) (x : T) : Result (SharedList T) := do
+  let self_post ← (alloc.boxed.Box.new self)
+  ok (SharedList.Cons x self_post)
```

</details>

<details><summary><code>array_slice_index</code> · `slice_use_index_mut_range_from`</summary>

**L₀ (mainline):**
```lean
def slice_use_index_mut_range_from
  (s : Slice Std.U32) :
  Result ((Slice Std.U32) × (Slice Std.U32 → Slice Std.U32))
  := do
  core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U32) s
    { start := 0#usize }
```

**L₁ (ours):**
```lean
def slice_use_index_mut_range_from (s : Slice Std.U32) : Result (Slice Std.U32 × (Slice Std.U32 → Slice Std.U32)) := do
  let (s_post_v, s_post_back) ← (core.slice.index.Slice.index_mut s { start := 0#usize })
  ok (s_post_v, fun ret => s)
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,7 +1,3 @@
-def slice_use_index_mut_range_from
-  (s : Slice Std.U32) :
-  Result ((Slice Std.U32) × (Slice Std.U32 → Slice Std.U32))
-  := do
-  core.slice.index.Slice.index_mut
-    (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U32) s
-    { start := 0#usize }
+def slice_use_index_mut_range_from (s : Slice Std.U32) : Result (Slice Std.U32 × (Slice Std.U32 → Slice Std.U32)) := do
+  let (s_post_v, s_post_back) ← (core.slice.index.Slice.index_mut s { start := 0#usize })
+  ok (s_post_v, fun ret => s)
```

</details>

<details><summary><code>arrays</code> · `array_subslice_mut_`</summary>

**L₀ (mainline):**
```lean
def array_subslice_mut_
  (x : Array Std.U32 32#usize) (y : Std.Usize) (z : Std.Usize) :
  Result ((Slice Std.U32) × (Slice Std.U32 → Array Std.U32 32#usize))
  := do
  core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeUsizeSlice Std.U32)) x
    { start := y, «end» := z }
```

**L₁ (ours):**
```lean
def array_subslice_mut_ (x : Array Std.U32 32#usize) (y : Std.Usize) (z : Std.Usize) : Result (Slice Std.U32 × (Slice Std.U32 → Array Std.U32 32#usize)) := do
  let (x_post_v, x_post_back) ← (core.array.Array.index_mut x { start := y, «end» := z })
  ok (x_post_v, fun ret => x)
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,7 +1,3 @@
-def array_subslice_mut_
-  (x : Array Std.U32 32#usize) (y : Std.Usize) (z : Std.Usize) :
-  Result ((Slice Std.U32) × (Slice Std.U32 → Array Std.U32 32#usize))
-  := do
-  core.array.Array.index_mut (core.ops.index.IndexMutSlice
-    (core.slice.index.SliceIndexRangeUsizeSlice Std.U32)) x
-    { start := y, «end» := z }
+def array_subslice_mut_ (x : Array Std.U32 32#usize) (y : Std.Usize) (z : Std.Usize) : Result (Slice Std.U32 × (Slice Std.U32 → Array Std.U32 32#usize)) := do
+  let (x_post_v, x_post_back) ← (core.array.Array.index_mut x { start := y, «end» := z })
+  ok (x_post_v, fun ret => x)
```

</details>

### `decl_body_size_diff`

<details><summary><code>adt-borrows</code> · `MutWrapper`</summary>

**L₀ (mainline):**
```lean
def MutWrapper (T : Type) := T
```

**L₁ (ours):**
```lean
structure MutWrapper (T : Type) where
  field0 : T
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1 +1,2 @@
-def MutWrapper (T : Type) := T
+structure MutWrapper (T : Type) where
+  field0 : T
```

</details>

<details><summary><code>adt-borrows</code> · `SharedWrapper`</summary>

**L₀ (mainline):**
```lean
def SharedWrapper (T : Type) := T
```

**L₁ (ours):**
```lean
structure SharedWrapper (T : Type) where
  field0 : T
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1 +1,2 @@
-def SharedWrapper (T : Type) := T
+structure SharedWrapper (T : Type) where
+  field0 : T
```

</details>

<details><summary><code>adt-borrows</code> · `SharedWrapper.create`</summary>

**L₀ (mainline):**
```lean
def SharedWrapper.create {T : Type} (x : T) : Result (SharedWrapper T) := do
  ok x
```

**L₁ (ours):**
```lean
def SharedWrapper.create {T : Type} (x : T) : Result (SharedWrapper T) := do
  ok { field0 := x }
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,2 +1,2 @@
 def SharedWrapper.create {T : Type} (x : T) : Result (SharedWrapper T) := do
-  ok x
+  ok { field0 := x }
```

</details>

### `missing_backward_closure`

<details><summary><code>adt-borrows</code> · `MutList.pop`</summary>

**L₀ (mainline):**
```lean
def MutList.pop
  {T : Type} (self : MutList T) :
  Result ((T × (MutList T)) × ((T × (MutList T)) → MutList T))
  := do
  match self with
  | MutList.Nil => fail panic
  | MutList.Cons hd tl =>
    let back := fun p => let (t, ml) := p
                         MutList.Cons t ml
    ok ((hd, tl), back)
```

**L₁ (ours):**
```lean
def MutList.pop {T : Type} (self : MutList T) : Result (T × MutList T) := do
  match self with
  | MutList.Nil => error panic
  | MutList.Cons x2 x3 => ok (x2, x3)

end adt_borrows
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,10 +1,6 @@
-def MutList.pop
-  {T : Type} (self : MutList T) :
-  Result ((T × (MutList T)) × ((T × (MutList T)) → MutList T))
-  := do
+def MutList.pop {T : Type} (self : MutList T) : Result (T × MutList T) := do
   match self with
-  | MutList.Nil => fail panic
-  | MutList.Cons hd tl =>
-    let back := fun p => let (t, ml) := p
-                         MutList.Cons t ml
-    ok ((hd, tl), back)
+  | MutList.Nil => error panic
+  | MutList.Cons x2 x3 => ok (x2, x3)
+
+end adt_borrows
```

</details>

<details><summary><code>adt-borrows</code> · `MutWrapper.id`</summary>

**L₀ (mainline):**
```lean
def MutWrapper.id
  {T : Type} (self : MutWrapper T) :
  Result ((MutWrapper T) × (MutWrapper T → MutWrapper T))
  := do
  let back := fun mw => mw
  ok (self, back)
```

**L₁ (ours):**
```lean
def MutWrapper.id {T : Type} (self : MutWrapper T) : Result (MutWrapper T) := do
  ok self
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,6 +1,2 @@
-def MutWrapper.id
-  {T : Type} (self : MutWrapper T) :
-  Result ((MutWrapper T) × (MutWrapper T → MutWrapper T))
-  := do
-  let back := fun mw => mw
-  ok (self, back)
+def MutWrapper.id {T : Type} (self : MutWrapper T) : Result (MutWrapper T) := do
+  ok self
```

</details>

<details><summary><code>adt-borrows</code> · `MutWrapper.unwrap`</summary>

**L₀ (mainline):**
```lean
def MutWrapper.unwrap
  {T : Type} (self : MutWrapper T) : Result (T × (T → MutWrapper T)) := do
  let back := fun t => t
  ok (self, back)
```

**L₁ (ours):**
```lean
def MutWrapper.unwrap {T : Type} (self : MutWrapper T) : Result T := do
  ok self
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,4 +1,2 @@
-def MutWrapper.unwrap
-  {T : Type} (self : MutWrapper T) : Result (T × (T → MutWrapper T)) := do
-  let back := fun t => t
-  ok (self, back)
+def MutWrapper.unwrap {T : Type} (self : MutWrapper T) : Result T := do
+  ok self
```

</details>

### `l1_placeholder_emit`

<details><summary><code>arrays</code> · `f3`</summary>

**L₀ (mainline):**
```lean
def f3 : Result Std.U32 := do
  let i ← Array.index_usize (Array.make 2#usize [ 1#u32, 2#u32 ]) 0#usize
  f2 i
  let b := Array.repeat 32#usize 0#u32
  let s ← lift (Array.to_slice (Array.make 2#usize [ 1#u32, 2#u32 ]))
  let s1 ← f4 b 16#usize 18#usize
  sum2 s s1
```

**L₁ (ours):**
```lean
def f3 : Result Std.U32 := do
  let t0 ← (ArrayIndexShared (Aeneas.Std.Array.ofList (List.cons 0#u32 (List.cons 0#u32 List.nil))) 0#usize)
  let t1 ← (arrays.f2 t0)
  let t2 ← (ArrayRepeat 0#u32)
  let t3 ← (ArrayToSliceShared (Aeneas.Std.Array.ofList (List.cons 0#u32 (List.cons 0#u32 List.nil))))
  let t4 ← (arrays.f4 (Aeneas.Std.Array.ofList (List.cons 0#u32 (List.cons 0#u32 (List.cons 0#u32 (Li
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,7 +1,6 @@
 def f3 : Result Std.U32 := do
-  let i ← Array.index_usize (Array.make 2#usize [ 1#u32, 2#u32 ]) 0#usize
-  f2 i
-  let b := Array.repeat 32#usize 0#u32
-  let s ← lift (Array.to_slice (Array.make 2#usize [ 1#u32, 2#u32 ]))
-  let s1 ← f4 b 16#usize 18#usize
-  sum2 s s1
+  let t0 ← (ArrayIndexShared (Aeneas.Std.Array.ofList (List.cons 0#u32 (List.cons 0#u32 List.nil))) 0#usize)
+  let t1 ← (arrays.f2 t0)
+  let t2 ← (ArrayRepeat 0#u32)
+  let t3 ← (ArrayToSliceShared (Aeneas.Std.Array.ofList (List.cons 0#u32 (List.cons 0#u32 List.nil))))
+  let t4 ← (arrays.f4 (Aeneas.Std.Array.ofList (List.cons 0#u32 (List.cons 0#u32 (List.cons 0#u32 (Li
```

</details>

<details><summary><code>chunks_exact</code> · `test_chunks_exact_2_odd`</summary>

**L₀ (mainline):**
```lean
def test_chunks_exact_2_odd : Result Unit := do
  let s ←
    lift (Array.to_slice
      (Array.make 5#usize [ 1#u32, 2#u32, 3#u32, 4#u32, 5#u32 ]))
  let it ← core.slice.Slice.chunks_exact s 2#usize
  let (o, it1) ← core.slice.iter.IteratorChunksExact.next it
  let c1 ← core.option.Option.unwrap o
  let i ← Slice.index_usize c1 0#usize
  massert (i = 1#u32)
  let i1 ← Slice.index_usize c1 1#usize
```

**L₁ (ours):**
```lean
def test_chunks_exact_2_odd : Result Unit := do
  let t0 ← (ArrayToSliceShared (Aeneas.Std.Array.ofList (List.cons 0#u32 (List.cons 0#u32 (List.cons 0#u32 (List.cons 0#u32 (List.cons 0#u32 List.nil)))))))
  let t1 ← (core.slice.Slice.chunks_exact t0 2#usize)
  let (t2_v, t2_back) ← (core.slice.iter.ChunksExact.next t1)
  let t3 ← (core.option.Option.unwrap t2_v)
  let t4 ← (Slice.index_usize ((Aen
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,10 +1,6 @@
 def test_chunks_exact_2_odd : Result Unit := do
-  let s ←
-    lift (Array.to_slice
-      (Array.make 5#usize [ 1#u32, 2#u32, 3#u32, 4#u32, 5#u32 ]))
-  let it ← core.slice.Slice.chunks_exact s 2#usize
-  let (o, it1) ← core.slice.iter.IteratorChunksExact.next it
-  let c1 ← core.option.Option.unwrap o
-  let i ← Slice.index_usize c1 0#usize
-  massert (i = 1#u32)
-  let i1 ← Slice.index_usize c1 1#usize
+  let t0 ← (ArrayToSliceShared (Aeneas.Std.Array.ofList (List.cons 0#u32 (List.cons 0#u32 (List.cons 0#u32 (List.cons 0#u32 (List.cons 0#u32 List.nil)))))))
+  let t1 ← (core.slice.Slice.chunks_exact t0 2#usize)
+  let (t2_v, t2_back) ← (core.slice.iter.ChunksExact.next t1)
+  let t3 ← (core.option.Option.unwrap t2_v)
+  let t4 ← (Slice.index_usize ((Aen
```

</details>

<details><summary><code>chunks_exact</code> · `test_chunks_exact_2_single_element`</summary>

**L₀ (mainline):**
```lean
def test_chunks_exact_2_single_element : Result Unit := do
  let s ← lift (Array.to_slice (Array.make 1#usize [ 42#u32 ]))
  let it ← core.slice.Slice.chunks_exact s 2#usize
  let (o, it1) ← core.slice.iter.IteratorChunksExact.next it
  let b := core.option.Option.is_none o
  massert b
  let rem ← core.slice.iter.ChunksExact.getRemainder it1
  let i := Slice.len rem
  massert (i = 1#usize)
  let i
```

**L₁ (ours):**
```lean
def test_chunks_exact_2_single_element : Result Unit := do
  let t0 ← (ArrayToSliceShared (Aeneas.Std.Array.singleton 0#u32))
  let t1 ← (core.slice.Slice.chunks_exact t0 2#usize)
  let (t2_v, t2_back) ← (core.slice.iter.ChunksExact.next t1)
  let t3 ← (core.option.Option.is_none ((Option.placeholder : Option (Aeneas.Std.Slice Std.U32))))
  let t4 ← (core.slice.iter.ChunksExact.remainder ((ChunksE
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,10 +1,6 @@
 def test_chunks_exact_2_single_element : Result Unit := do
-  let s ← lift (Array.to_slice (Array.make 1#usize [ 42#u32 ]))
-  let it ← core.slice.Slice.chunks_exact s 2#usize
-  let (o, it1) ← core.slice.iter.IteratorChunksExact.next it
-  let b := core.option.Option.is_none o
-  massert b
-  let rem ← core.slice.iter.ChunksExact.getRemainder it1
-  let i := Slice.len rem
-  massert (i = 1#usize)
-  let i
+  let t0 ← (ArrayToSliceShared (Aeneas.Std.Array.singleton 0#u32))
+  let t1 ← (core.slice.Slice.chunks_exact t0 2#usize)
+  let (t2_v, t2_back) ← (core.slice.iter.ChunksExact.next t1)
+  let t3 ← (core.option.Option.is_none ((Option.placeholder : Option (Aeneas.Std.Slice Std.U32))))
+  let t4 ← (core.slice.iter.ChunksExact.remainder ((ChunksE
```

</details>

### `comment_only`

<details><summary><code>adt-borrows</code> · `SharedWrapper2.unwrap`</summary>

**L₀ (mainline):**
```lean
def SharedWrapper2.unwrap
  {T : Type} (self : SharedWrapper2 T) : Result (T × T) := do
  ok (self.x, self.y)
```

**L₁ (ours):**
```lean
def SharedWrapper2.unwrap {T : Type} (self : SharedWrapper2 T) : Result (T × T) := do
  ok (self.x, self.y)
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,3 +1,2 @@
-def SharedWrapper2.unwrap
-  {T : Type} (self : SharedWrapper2 T) : Result (T × T) := do
+def SharedWrapper2.unwrap {T : Type} (self : SharedWrapper2 T) : Result (T × T) := do
   ok (self.x, self.y)
```

</details>

<details><summary><code>adt-borrows</code> · `boxed_slice_shared_borrow`</summary>

**L₀ (mainline):**
```lean
def boxed_slice_shared_borrow
  (x : Slice Std.U32) : Result (Slice Std.U32) := do
  ok x
```

**L₁ (ours):**
```lean
def boxed_slice_shared_borrow (x : Slice Std.U32) : Result (Slice Std.U32) := do
  ok x
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,3 +1,2 @@
-def boxed_slice_shared_borrow
-  (x : Slice Std.U32) : Result (Slice Std.U32) := do
+def boxed_slice_shared_borrow (x : Slice Std.U32) : Result (Slice Std.U32) := do
   ok x
```

</details>

<details><summary><code>defaulted_method</code> · `NoOverride.Insts.Defaulted_methodTrait.provided_method`</summary>

**L₀ (mainline):**
```lean
def NoOverride.Insts.Defaulted_methodTrait.provided_method
  (self : NoOverride) : Result Std.U32 := do
  ok 73#u32
```

**L₁ (ours):**
```lean
def NoOverride.Insts.Defaulted_methodTrait.provided_method (self : NoOverride) : Result Std.U32 := do
  ok 73#u32
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,3 +1,2 @@
-def NoOverride.Insts.Defaulted_methodTrait.provided_method
-  (self : NoOverride) : Result Std.U32 := do
+def NoOverride.Insts.Defaulted_methodTrait.provided_method (self : NoOverride) : Result Std.U32 := do
   ok 73#u32
```

</details>

### `wrong_backward_closure_domain`

<details><summary><code>adt-borrows</code> · `MutList.push`</summary>

**L₀ (mainline):**
```lean
def MutList.push
  {T : Type} (self : MutList T) (x : T) :
  Result ((MutList T) × (MutList T → ((MutList T) × T)))
  := do
  let back :=
    fun ml =>
      let (x1, ml1) :=
        match ml with
        | MutList.Cons t ml2 => (t, ml2)
        | _ => (x, self)
      (ml1, x1)
  ok (MutList.Cons x self, back)
```

**L₁ (ours):**
```lean
def MutList.push {T : Type} (self : MutList T) (x : T) : Result (MutList T × (Unit → T)) := do
  let self_post ← (alloc.boxed.Box.new self)
  ok ((MutList.Cons x self_post), fun ret => x)
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,12 +1,3 @@
-def MutList.push
-  {T : Type} (self : MutList T) (x : T) :
-  Result ((MutList T) × (MutList T → ((MutList T) × T)))
-  := do
-  let back :=
-    fun ml =>
-      let (x1, ml1) :=
-        match ml with
-        | MutList.Cons t ml2 => (t, ml2)
-        | _ => (x, self)
-      (ml1, x1)
-  ok (MutList.Cons x self, back)
+def MutList.push {T : Type} (self : MutList T) (x : T) : Result (MutList T × (Unit → T)) := do
+  let self_post ← (alloc.boxed.Box.new self)
+  ok ((MutList.Cons x self_post), fun ret => x)
```

</details>

<details><summary><code>adt-borrows</code> · `MutWrapper.create`</summary>

**L₀ (mainline):**
```lean
def MutWrapper.create
  {T : Type} (x : T) : Result ((MutWrapper T) × (MutWrapper T → T)) := do
  ok (x, fun mw => mw)
```

**L₁ (ours):**
```lean
def MutWrapper.create {T : Type} (x : T) : Result (MutWrapper T × (Unit → T)) := do
  ok ({ field0 := x }, fun ret => x)
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,3 +1,2 @@
-def MutWrapper.create
-  {T : Type} (x : T) : Result ((MutWrapper T) × (MutWrapper T → T)) := do
-  ok (x, fun mw => mw)
+def MutWrapper.create {T : Type} (x : T) : Result (MutWrapper T × (Unit → T)) := do
+  ok ({ field0 := x }, fun ret => x)
```

</details>

<details><summary><code>adt-borrows</code> · `MutWrapper1.create`</summary>

**L₀ (mainline):**
```lean
def MutWrapper1.create
  {T : Type} (x : T) : Result ((MutWrapper1 T) × (MutWrapper1 T → T)) := do
  let back := fun mw => mw.x
  ok ({ x }, back)
```

**L₁ (ours):**
```lean
def MutWrapper1.create {T : Type} (x : T) : Result (MutWrapper1 T × (Unit → T)) := do
  ok ({ x := x }, fun ret => x)
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,4 +1,2 @@
-def MutWrapper1.create
-  {T : Type} (x : T) : Result ((MutWrapper1 T) × (MutWrapper1 T → T)) := do
-  let back := fun mw => mw.x
-  ok ({ x }, back)
+def MutWrapper1.create {T : Type} (x : T) : Result (MutWrapper1 T × (Unit → T)) := do
+  ok ({ x := x }, fun ret => x)
```

</details>

### `l1_type_ascription`

<details><summary><code>curve25519</code> · `m`</summary>

**L₀ (mainline):**
```lean
def m (x : Std.U64) (y : Std.U64) : Result Std.U128 := do
  let i ← lift (UScalar.cast .U128 x)
  let i1 ← lift (UScalar.cast .U128 y)
  i * i1
```

**L₁ (ours):**
```lean
def m (x : Std.U64) (y : Std.U64) : Result Std.U128 := do
  ((x : u128)) * ((y : u128))
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,4 +1,2 @@
 def m (x : Std.U64) (y : Std.U64) : Result Std.U128 := do
-  let i ← lift (UScalar.cast .U128 x)
-  let i1 ← lift (UScalar.cast .U128 y)
-  i * i1
+  ((x : u128)) * ((y : u128))
```

</details>

<details><summary><code>dyn</code> · `Bool.Insts.DynTrait.get`</summary>

**L₀ (mainline):**
```lean
def Bool.Insts.DynTrait.get (self : Bool) : Result Std.U32 := do
  ok (UScalar.cast_fromBool .U32 self)
```

**L₁ (ours):**
```lean
def Bool.Insts.DynTrait.get (self : Bool) : Result Std.U32 := do
  ok ((self : Aeneas.Std.U32))
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,2 +1,2 @@
 def Bool.Insts.DynTrait.get (self : Bool) : Result Std.U32 := do
-  ok (UScalar.cast_fromBool .U32 self)
+  ok ((self : Aeneas.Std.U32))
```

</details>

<details><summary><code>loop_shared_loan_in_join</code> · `State.extract`</summary>

**L₀ (mainline):**
```lean
def State.extract
  (self : State) (result : Slice Std.U64) (count : Std.Usize) :
  Result (State × (Slice Std.U64))
  := do
  let lane_index ← lift (UScalar.cast .Usize self.index)
  let (a, i, result1) ←
    State.extract_loop { start := 0#usize, «end» := count } self.data
      self.index self.limit result lane_index
  ok ({ self with data := a, index := i }, result1)

end loop_shared_loan_in_j
```

**L₁ (ours):**
```lean
def State.extract (self : State) (result : Slice Std.U64) (count : Std.Usize) : Result Unit := do
  (State.extract_loop self result count { start := 0#usize, «end» := count } ((self : Aeneas.Std.Usize)))

end loop_shared_loan_in_join
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,11 +1,4 @@
-def State.extract
-  (self : State) (result : Slice Std.U64) (count : Std.Usize) :
-  Result (State × (Slice Std.U64))
-  := do
-  let lane_index ← lift (UScalar.cast .Usize self.index)
-  let (a, i, result1) ←
-    State.extract_loop { start := 0#usize, «end» := count } self.data
-      self.index self.limit result lane_index
-  ok ({ self with data := a, index := i }, result1)
+def State.extract (self : State) (result : Slice Std.U64) (count : Std.Usize) : Result Unit := do
+  (State.extract_loop self result count { start := 0#usize, «end» := count } ((self : Aeneas.Std.Usize)))
 
-end loop_shared_loan_in_j
+end loop_shared_loan_in_join
```

</details>

### `tuple_collapse`

<details><summary><code>adt</code> · `BigStruct`</summary>

**L₀ (mainline):**
```lean
def BigStruct :=
  BigStructName × BigStructName × BigStructName × BigStructName ×
  BigStructName × BigStructName

end adt
```

**L₁ (ours):**
```lean
structure BigStruct where
  field0 : BigStructName
  field1 : BigStructName
  field2 : BigStructName
  field3 : BigStructName
  field4 : BigStructName
  field5 : BigStructName
```

**Diff:**
```diff
--- L0
+++ L1
@@ -1,5 +1,7 @@
-def BigStruct :=
-  BigStructName × BigStructName × BigStructName × BigStructName ×
-  BigStructName × BigStructName
-
-end adt
+structure BigStruct where
+  field0 : BigStructName
+  field1 : BigStructName
+  field2 : BigStructName
+  field3 : BigStructName
+  field4 : BigStructName
+  field5 : BigStructName
```

</details>

## Emit failures

### L₀ (mainline aeneas) failures: 3
- `closures`: [?25lApplied prepasses:  [--------------------------------------------------]  0/46 ⠋
- `issue-804-closure-return-ref`: [?25lApplied prepasses:  [----------------------------------------------------] 0/6 ⠋
- `raw_pointers`: [?25lApplied prepasses:  [----------------------------------------------------] 0/6 ⠋

## Per-fixture summary

| Fixture | Status | Top pattern | Other patterns |
|---|---|---|---|
| `derive` | divergent | `only_in_L1`(75) | `only_in_L0`(74), `other`(4) |
| `loops-rec` | divergent | `other`(57) | `only_in_L1`(22), `missing_backward_closure`(19), `bind_arrow_count_diff`(15), `only_in_L0`(6) |
| `loops` | divergent | `other`(57) | `only_in_L1`(22), `missing_backward_closure`(19), `bind_arrow_count_diff`(15), `only_in_L0`(6) |
| `traits` | divergent | `other`(46) | `only_in_L0`(26), `only_in_L1`(26), `decl_body_size_diff`(4) |
| `arrays` | divergent | `other`(40) | `bind_arrow_count_diff`(32), `decl_body_size_diff`(2), `only_in_L1`(1), `l1_placeholder_emit`(1) |
| `no_nested_borrows` | divergent | `other`(24) | `decl_body_size_diff`(18), `bind_arrow_count_diff`(7), `only_in_L0`(2), `only_in_L1`(2) |
| `loops-nested-rec` | divergent | `only_in_L0`(24) | `only_in_L1`(12), `other`(9), `bind_arrow_count_diff`(3), `comment_only`(3) |
| `loops-nested` | divergent | `only_in_L0`(24) | `only_in_L1`(12), `other`(9), `bind_arrow_count_diff`(3), `comment_only`(3) |
| `iterators` | divergent | `only_in_L0`(24) | `only_in_L1`(12), `other`(9), `bind_arrow_count_diff`(6), `decl_body_size_diff`(1) |
| `hashmap` | divergent | `other`(15) | `bind_arrow_count_diff`(11), `only_in_L1`(9), `only_in_L0`(3), `missing_backward_closure`(2) |
| `adt-borrows` | divergent | `missing_backward_closure`(16) | `decl_body_size_diff`(9), `other`(6), `wrong_backward_closure_domain`(5), `comment_only`(2) |
| `assert-cfg` | divergent | `bind_arrow_count_diff`(26) | `other`(7) |
| `nested-borrows` | divergent | `bind_arrow_count_diff`(7) | `other`(7), `wrong_backward_closure_domain`(6), `only_in_L0`(4), `decl_body_size_diff`(3) |
| `rename_attribute` | divergent | `only_in_L0`(14) | `only_in_L1`(14) |
| `constants` | divergent | `only_in_L1`(14) | `other`(9), `decl_body_size_diff`(2), `bind_arrow_count_diff`(1) |
| `loops-issues` | divergent | `other`(15) | `bind_arrow_count_diff`(8), `only_in_L0`(1), `only_in_L1`(1), `decl_body_size_diff`(1) |
| `order` | divergent | `only_in_L0`(9) | `only_in_L1`(9), `other`(5), `decl_body_size_diff`(1) |
| `constants-lean` | divergent | `only_in_L1`(9) | `only_in_L0`(6), `other`(5), `decl_body_size_diff`(2), `bind_arrow_count_diff`(1) |
| `dyn` | divergent | `only_in_L0`(9) | `only_in_L1`(9), `other`(2), `bind_arrow_count_diff`(2), `l1_type_ascription`(1) |
| `loops-adts` | divergent | `other`(9) | `missing_backward_closure`(5), `only_in_L1`(2), `decl_body_size_diff`(2), `comment_only`(1) |
| `scalars` | divergent | `other`(14) | `l1_type_ascription`(4), `bind_arrow_count_diff`(1) |
| `demo` | divergent | `other`(5) | `decl_body_size_diff`(4), `bind_arrow_count_diff`(4), `only_in_L1`(3), `only_in_L0`(2) |
| `discriminant` | divergent | `only_in_L1`(7) | `only_in_L0`(6) |
| `loops-sequences` | divergent | `comment_only`(5) | `only_in_L0`(4), `only_in_L1`(2), `decl_body_size_diff`(1), `bind_arrow_count_diff`(1) |
| `mut-borrow-in-shared-borrow` | divergent | `other`(7) | `decl_body_size_diff`(4) |
| `step_by` | divergent | `l1_placeholder_emit`(11) |  |
| `builtin` | divergent | `other`(9) | `only_in_L1`(1) |
| `from_to` | divergent | `only_in_L0`(4) | `only_in_L1`(4), `other`(2) |
| `list-borrows` | divergent | `only_in_L0`(4) | `other`(3), `only_in_L1`(1), `wrong_backward_closure_domain`(1), `bind_arrow_count_diff`(1) |
| `multi-target` | divergent | `other`(4) | `only_in_L0`(3), `only_in_L1`(3) |
| `chunks_exact` | divergent | `l1_placeholder_emit`(9) |  |
| `const-shadow` | divergent | `only_in_L0`(3) | `only_in_L1`(3), `other`(1), `bind_arrow_count_diff`(1) |
| `array_slice_index` | divergent | `other`(4) | `only_in_L1`(1), `wrong_backward_closure_domain`(1), `bind_arrow_count_diff`(1) |
| `curve25519` | divergent | `only_in_L0`(2) | `only_in_L1`(2), `decl_body_size_diff`(1), `l1_type_ascription`(1), `bind_arrow_count_diff`(1) |
| `issue-194-recursive-struct-projector` | divergent | `only_in_L0`(6) | `other`(1) |
| `joins` | divergent | `other`(4) | `bind_arrow_count_diff`(3) |
| `paper` | divergent | `decl_body_size_diff`(5) | `other`(1), `bind_arrow_count_diff`(1) |
| `slices` | divergent | `other`(3) | `bind_arrow_count_diff`(2), `only_in_L1`(1), `decl_body_size_diff`(1) |
| `defaulted_method` | divergent | `comment_only`(3) | `other`(2), `decl_body_size_diff`(1) |
| `issue-134-loop-shared-borrows` | divergent | `other`(3) | `only_in_L0`(2), `only_in_L1`(1) |
| `loop_shared_loan_in_join` | divergent | `other`(3) | `bind_arrow_count_diff`(2), `l1_type_ascription`(1) |
| `mini_tree` | divergent | `other`(3) | `only_in_L0`(2), `only_in_L1`(1) |
| `builtin-auto` | divergent | `only_in_L1`(2) | `other`(2), `only_in_L0`(1) |
| `deref` | divergent | `bind_arrow_count_diff`(3) | `other`(2) |
| `drop_bug` | divergent | `decl_body_size_diff`(4) | `bind_arrow_count_diff`(1) |
| `issue-789-loop-ctx-match` | divergent | `other`(2) | `only_in_L1`(1), `bind_arrow_count_diff`(1), `decl_body_size_diff`(1) |
| `calls` | divergent | `other`(3) | `decl_body_size_diff`(1) |
| `mutually-recursive-traits` | divergent | `only_in_L0`(4) |  |
| `static` | divergent | `other`(3) | `l1_placeholder_emit`(1) |
| `arrays_defs` | divergent | `other`(3) |  |
| `default` | divergent | `other`(3) |  |
| `drop` | divergent | `bind_arrow_count_diff`(2) | `other`(1) |
| `into` | divergent | `other`(2) | `only_in_L1`(1) |
| `issue-270-loop-list` | divergent | `other`(2) | `only_in_L1`(1) |
| `issue-807-missing-symbolic-value` | divergent | `other`(2) | `bind_arrow_count_diff`(1) |
| `iterators-array` | divergent | `other`(2) | `bind_arrow_count_diff`(1) |
| `iterators-scalar` | divergent | `other`(2) | `bind_arrow_count_diff`(1) |
| `loops_simple` | divergent | `other`(3) |  |
| `options` | divergent | `other`(3) |  |
| `range` | divergent | `other`(2) | `only_in_L1`(1) |
| `string-chars` | divergent | `only_in_L1`(1) | `other`(1), `bind_arrow_count_diff`(1) |
| `vec` | divergent | `other`(2) | `l1_placeholder_emit`(1) |
| `adt` | divergent | `tuple_collapse`(1) | `other`(1) |
| `as_mut` | divergent | `bind_arrow_count_diff`(2) |  |
| `bitwise` | divergent | `other`(2) |  |
| `dynamic_size` | divergent | `l1_placeholder_emit`(2) |  |
| `issue-803-self-in-array` | divergent | `decl_body_size_diff`(1) | `other`(1) |
| `issue-815-global-referencing-fallible-global` | divergent | `only_in_L1`(2) |  |
| `multi_region` | divergent | `other`(1) | `l1_type_ascription`(1) |
| `slices_basic` | divergent | `other`(2) |  |
| `aggregates_basic` | divergent | `decl_body_size_diff`(1) |  |
| `compare_simple` | divergent | `other`(1) |  |
| `enums_payload` | divergent | `other`(1) |  |
| `generics_basic` | divergent | `other`(1) |  |
| `issue-440-type-error` | divergent | `decl_body_size_diff`(1) |  |
| `join-duplicate` | divergent | `decl_body_size_diff`(1) |  |
| `list_basic` | divergent | `other`(1) |  |
| `list_generic` | divergent | `other`(1) |  |
| `names` | divergent | `only_in_L0`(1) |  |
| `print` | divergent | `bind_arrow_count_diff`(1) |  |
| `reborrows` | divergent | `other`(1) |  |
| `switch_test` | divergent | `other`(1) |  |
| `traits_basic` | divergent | `other`(1) |  |
| `blanket_impl` | pass-file | `-`(0) |  |
| `enums_basic` | pass-file | `-`(0) |  |
| `incr_cert` | pass-file | `-`(0) |  |
