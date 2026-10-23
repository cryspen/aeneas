# Specs from Rust, via hax annotations (`-specs hax`)

## High-level documentation

When Aeneas is invoked with `-specs hax` (Lean backend only, together with
`-core-models-lib`) it reads the contracts written with
[`hax_lib`](https://github.com/cryspen/hax) annotations in the Rust code and
emits them as Lean statements of correctness, together with the proof
obligations stating that the code meets them.

### Overview

There are several kinds of rust-written specs:

* *Function level specs*: `#[requires(..)]` / `#[ensures(\|res\|..)]` on a
  function. Those generate specification functions `<fn>.pre`, `<fn>.post`, a
  statement of correctness `<fn>.spec`, and the obligation `<fn>.spec.proof`
* *Trait level specs*: every local trait gets a *companion* structure
  `<Trait>.Lawful` that registers the specifications attached to its methods.
  Every local implementation, including derived impls and the impls of foreign
  traits (e.g. `Clone`, or the `Fn*` impls of closures), generates a
  corresponding obligation of lawfulness.
    * If no annotation is written, the companion structure has no method field
      (the parent fields remain).
    * `#[requires(..)]` / `#[ensures(\|res\|..)]` on the methods of trait
      generate specification functions `<Trait>.<m>.pre`, `<Trait>.<m>.post`,
      and add a field `<m>_spec` to the companion structure `<Trait>.Lawful`.
* *Impl level specs*: trait-level specifications can be *refined* (weaker
  pre-condition and stronger post) for each implementation. Such specifications,
  written with `#[requires(..)]` / `#[ensures(\|res\|..)]`, generate standalone
  contracts. For now, the trait-level and impl-level specs are not linked.

At most one `#[requires]` and one `#[ensures]` are used per item. Other hax
annotations (e.g. `decreases`) are dropped.

### File structure

With `-split-files`, the specs go to `Specs.lean` and the obligations to
`ProofObligations.lean` (which imports `Specs`). Without `-split-files`, both
go at the end of the single output file.

`Specs.lean` contains, in order:
1. For each local trait (parents first): the `.pre`/`.post` of its annotated
   methods, then `<Trait>.Lawful`.
2. For each contracted function: `<fn>.pre`, `<fn>.post`, then `<fn>.spec`.

`ProofObligations.lean` contains, in order:
1. `<impl>.Lawful` for each local trait impl (dependencies first).
2. `<fn>.spec.proof` for each contracted function.

### Function contracts

```rust
#[requires(x < 10)]
#[ensures(|result| result > x)]
fn both(x: u32) -> u32 { x + 1 }
```

```lean
-- Specs.lean
@[reducible]
def both.pre (x : Std.U32) : RustM Bool := do
  ok (x < 10#u32)

@[reducible]
def both.post
  (x : Std.U32) (result : Std.U32) : RustM Bool := do
  ok (result > x)

def both.spec (x : Std.U32) : Prop :=
  (specs.contracts.both.pre x).holds →
  ⦃ ⌜ True ⌝ ⦄
  specs.contracts.both x
  ⦃ ⇓ res => ⌜ (specs.contracts.both.post x res).holds ⌝ ⦄
```

```lean
-- ProofObligations.lean
theorem both.spec.proof (x : Std.U32) :
  specs.contracts.both.spec x
  := by sorry
```

- The conditions are the hax decoration functions, translated like any function:
  `RustM Bool` (or `RustM hax_lib.prop.Prop` for `hax_lib::prop`
  conditions). The postcondition takes the result as its last argument.
- Without `#[requires]` the spec has no hypothesis; without `#[ensures]` its
  postcondition is `⌜ True ⌝`.
- `.spec` is a total-correctness triple (`⇓`): the function must not panic or
  diverge.

### Trait contracts and `X.Lawful`

```rust
#[hax_lib::attributes]
trait A {
    #[ensures(|res| res >= 1)]
    fn a(&self) -> usize;
}

#[hax_lib::attributes]
trait B: A {
    #[requires(self.a() < 100)]
    #[ensures(|res| res > self.a())]
    fn b(&self) -> usize;
}

impl B for u8 { ... }
```

```lean
-- Specs.lean
structure B.Lawful
  (Self : Type)
  (BInst : specs.traits.supertraits.B Self) : Prop where

  -- supertrait lawfulness
  AInstLawful : specs.traits.supertraits.A.Lawful Self BInst.AInst

  -- method spec
  b_spec (self_ : Self) :
    (specs.traits.supertraits.B.b.pre BInst.AInst BInst self_).holds →
    ⦃ ⌜ True ⌝ ⦄
    BInst.b self_
    ⦃ ⇓ res =>
      ⌜ (specs.traits.supertraits.B.b.post BInst.AInst BInst self_ res).holds ⌝ ⦄
```

```lean
-- ProofObligations.lean
theorem U8.Insts.Hax_testsSpecsTraitsSupertraitsB.Lawful :
  specs.traits.supertraits.B.Lawful Std.U8
  U8.Insts.Hax_testsSpecsTraitsSupertraitsB
  := by sorry
```

One Lawful field per parent clause `<P>InstLawful : P.Lawful …
<X>Inst.<P>Inst`, one spec per annotated method `<m>_spec`. A trait with no
annotated method and no parent still gets an empty structure. Each local
implementation gets a corresponding proof obligation.

#### Foreign traits

`X.Lawful` is only generated for local traits. For a foreign trait the generated
code refers to `X.Lawful` as if it existed, so a Lean library must provide it,
following the same conventions.


## Details

### Diagnostics

The warnings below start with `hax-specs:`. Those marked *(span)* point at the
Rust source when it is known; with `-warnings-as-errors` they become errors:
the item is still dropped and the extraction continues, but Aeneas exits with
code 1. The others are logged at warning level (shown by `cargo hax extract
-v`).

*  ``multiple #[requires] on `f`; ignoring extras`` (or `#[ensures]`) : More
   than one condition of a kind on an item: the first one is used.
* ``` `f` references unknown decoration uid …; skipping that side ``` : The
  decoration function of a condition is not in the LLBC.
* ``argument count mismatch for `f.pre` (takes N, expected M); dropping this
  condition`` : The condition does not take the arguments of the function (plus
  the result, for a post).
* ``dropping the contract of trait method `m`: <reason>`` *(span)* : the whole
  contract of the trait method is dropped (its `<m>_spec` field is not
  generated). The reasons:
  * `its #[requires] is invalid` (or `#[ensures]`): one of its conditions was
    dropped (see above);
  * `the generics of its conditions don't match those of the trait and the
    method`: only `#[requires]` is written, and the postcondition cannot be
    synthesized (see [Limitations](#limitations));
  * `trait instances in its output type are not supported yet`: only
    `#[requires]` is written, and the output type of the method mentions a trait
    instance;
  * `a missing condition could not be synthesized`: an error was reported while
    synthesizing it.
* ``the contract of `m` is checked as a standalone spec only; it is independent
  of the trait-level contract`` Contract on a method of a trait impl, whose
  trait method has a contract too.
* ``dropping the hax decoration `d`: it is attached to no translated item``
  *(span)* No item refers to this decoration function.
* ``dropping the hax decoration `d`: unsupported or invalid annotation, or part
  of a dropped contract`` A decoration that was not used (e.g. `decreases`, an
  extra or dropped condition).
* ``dropping the contract of function `f`: the function was not translated``
  *(span)* The annotated function failed to translate. Same for a trait
  (``dropping the contract of trait `X`: the trait was not translated``) and a
  trait impl (``dropping the Lawful obligation of trait impl `I`: the trait impl
  was not translated``).
* ``dropping the Lawful obligation of an impl of trait `X`: the trait was not
  translated`` *(span)* The impl was translated, but not the trait it
  implements.

If a spec or an obligation fails to extract, the error is reported and only that
entry is skipped; Aeneas exits with code 1.

Command-line errors: `The -specs option is valid only for the Lean backend`,
and `The -specs hax option requires the -core-models-lib option`.

Name clashes between the generated names (`.pre`, `.post`, `.spec`,
`.spec.proof`, `.Lawful`) and the names of the crate items are errors (`Name
clash detected: …`). This includes a trait field (parent clause, associated
constant or type, or method) whose projection would be named `<X>.Lawful`,
e.g. an associated type `Lawful`; the check is case-sensitive (a method `lawful`
is fine).

### Limitations

- **No `@[spec]` registration.** The obligations are plain theorems: `mvcgen`
  does not use them automatically. A caller unfolds the callee's `.spec` or
  passes the theorem explicitly (see below).
- **Impl-level contracts**: see [Overview](#overview).
- **`ProofObligations.lean` is a template**: every proof is `sorry`, and it is
  overwritten on each extraction. Copy the obligations to a handwritten file to
  prove them. Nothing checks the copy against the template: after a
  re-extraction, compare the two (the theorems live in `namespace <crate>`, as
  in the generated files).
- **Built-in instances**: an instance that Charon resolves as built-in
  (`BuiltinOrAuto`, e.g. `Clone` for a tuple) is printed as `BuiltinClone …`,
  not as a `CoreModels` instance, so no `Lawful` theorem exists for it (e.g. to
  fill the `Clone` parent field of an impl of `Dup: Clone` for a tuple).
- **Trait methods and associated types.** Charon lifts the associated types of
  a trait to type parameters, but not the same way in the trait and in the
  decoration functions of its conditions: once per clause path in the latter
  (`Clause0_Item`, `Clause1_Clause0_Item`, …), and after the type parameters of
  the method. Aeneas maps the generics of the conditions to those of the trait
  and the method by position, so:
  - the contract is dropped with a warning (`the generics of its conditions
    don't match those of the trait and the method`) when only `#[requires]` is
    written and a supertrait has an associated type (e.g. `trait SubAssoc:
    Assoc`, or `trait Call<Args>: CallOnce<Args>` with `type Output` in
    `CallOnce`);
  - extraction fails (exit code 1, partial `<Trait>.Lawful`) when `#[ensures]`
    is written (with or without `#[requires]`) and a supertrait has an
    associated type (``Internal error: the generics of the condition `…` don't
    match those it is applied to``), or when the trait has an associated type and the method a type
    parameter (`Could not find an instance for a trait clause of a pre/post
    condition`).

  The cases are in `tests/hax/src/specs/traits/synthesized.rs` (the failing
  ones are commented out).
- **Compile with `--cfg hax_backend_lean`.** `cargo hax` sets it. Without it,
  `hax_lib` encodes the decoration functions for hax's legacy engine: the
  future values of `&mut` arguments come before the result in a postcondition
  (Aeneas expects them after it), and a function without arguments gets
  conditions with a unit argument. The second is detected: Aeneas drops these
  conditions (e.g. ``argument count mismatch for `f.pre` (takes 1, expected 0);
  dropping this condition``). The first is not: the postcondition may silently
  refer to the wrong values.
- **Associated constants** are not covered by `<Trait>.Lawful`: nothing says
  that reading one does not fail, so the spec of a generic function that reads
  `T::C` outside of its conditions may not be provable.
- **Recursive associated-type bounds** (`type Item: Foo` in `trait Foo`) are
  not supported: Charon cannot lift them, and Lean rejects the generated trait
  structure.
- **`dyn Trait`** is out of scope: a `dyn Trait` argument gets no Lawful
  hypothesis in the spec of the function (and Aeneas does not translate calls
  through `dyn` yet).
- **Mutually recursive methods** of an impl need one joint proof: the
  obligation is a single `<impl>.Lawful` theorem, so prove the methods together
  in a separate lemma and use it for each field.

### Proving the obligations

The examples below are adapted from the hax test suite
(`tests/hax/proofs/hax-tests/lean/HaxTests/Verification/`).

**Function specs.** Unfold the spec and the function, then run `hax_mvcgen`
(from hax's Lean library) or `mvcgen`:

```lean
theorem specs.contracts.both.spec.proof (x : Std.U32) : specs.contracts.both.spec x := by
  unfold specs.contracts.both.spec specs.contracts.both
  hax_mvcgen
  · simp; scalar_tac
  · scalar_tac
```

**Using a Lawful hypothesis.** `mvcgen [L.m_spec]` does not accept a projection
of a local hypothesis: bind it with `have` first. To learn that a method call
returns (e.g. because a condition calls it again), use
`Aeneas.Std.triple_iff_exists_ok`, which turns a `⇓` triple into `∃ a, x =
.ok a ∧ P a`:

```lean
theorem specs.traits.basic.g.spec.proof … := by
  unfold specs.traits.basic.g.spec specs.traits.basic.g
  have h2 := FooInstLawful.f2_spec
  obtain ⟨b, hf1, -⟩ := (Aeneas.Std.triple_iff_exists_ok).1 (FooInstLawful.f1_spec x (by simp))
  mvcgen [hf1, h2]
  simp [specs.traits.basic.g.post]
```

Parent contracts are reached through the parent fields,
e.g. `BInstLawful.AInstLawful.a_spec`.

**Concrete callers.** A caller at a concrete impl uses the `.Lawful` theorem of
the impl. Either instantiate the callee's proof and unfold it, or reuse a
generic proof directly when the function is the same code at a concrete type:

```lean
theorem specs.traits.basic.h.spec.proof (x : Std.U64) : specs.traits.basic.h.spec x := by
  unfold specs.traits.basic.h.spec specs.traits.basic.h
  have hg := specs.traits.basic.g.spec.proof U64.Insts.Hax_testsSpecsTraitsBasicFoo x
    U64.Insts.Hax_testsSpecsTraitsBasicFoo.Lawful
  unfold specs.traits.basic.g.spec at hg
  mvcgen [hg]

theorem specs.traits.supertraits.via_u8.spec.proof (x : Std.U8) :
    specs.traits.supertraits.via_u8.spec x :=
  specs.traits.supertraits.via_b.spec.proof _ x U8.Insts.Hax_testsSpecsTraitsSupertraitsB.Lawful
```

A generic caller passes its own Lawful binders instead, or their parent fields
for a parent instance (e.g. `… SubInst.FooInst SubInstLawful.FooInstLawful`, in
`Verification/Traits/GenericImpl.lean`). A foreign bound at a concrete type
takes the theorem of the core impl
(e.g. `core.U32.Insts.CoreCloneClone.Lawful`).

**Impl obligations.** Prove `<impl>.Lawful` with `where` (one tactic block per
field) or an anonymous constructor (`⟨⟩` for an empty structure). Fill the
parent fields with the theorems of the parent impls, and, for generic impls,
with the Lawful binders:

```lean
theorem U8.Insts.Hax_testsSpecsTraitsSupertraitsB.Lawful :
  specs.traits.supertraits.B.Lawful Std.U8 U8.Insts.Hax_testsSpecsTraitsSupertraitsB
  where
  AInstLawful := U8.Insts.Hax_testsSpecsTraitsSupertraitsA.Lawful
  b_spec := by
    intro self _
    apply Aeneas.Std.WP.spec_to_mvcgen
    simp [U8.Insts.Hax_testsSpecsTraitsSupertraitsB.b, U8.Insts.Hax_testsSpecsTraitsSupertraitsA.a]
    step*

theorem …Wrapper.Insts.Hax_testsSpecsTraitsGeneric_implFoo.Lawful {T : Type}
  (FooInst : …) (FooInstLawful : specs.traits.generic_impl.Foo.Lawful T FooInst) : …
  where
  f_spec self hpre := FooInstLawful.f_spec self.inner hpre
```

`Aeneas.Std.WP.spec_to_mvcgen` turns the `⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ Q r ⌝ ⦄`
goal of a field into the Aeneas `spec` form, so that `step*` can be used.

**`.holds` of `RustM Bool` conditions.** A trait-method condition used as a
proposition appears as `((fun a => a = true) <$> x).holds`, which neither Aeneas
nor Hax simplifies yet. The test suite proves a simp lemma for it in
`HaxTests/Verification/Lemmas.lean`:

```lean
@[simp] theorem Aeneas.Std.RustM.holds_bool (x : RustM Bool) :
    ((fun a => a = true) <$> x : RustM Prop).holds ↔ x = ok true
```
