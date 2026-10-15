# Specs from Rust, via hax annotations (`-specs hax`)

## High-level documentation

When Aeneas is invoked with `-specs hax` (Lean backend only) it reads the
contracts written with [`hax_lib`](https://github.com/cryspen/hax) annotations
in the Rust code and emits them as Lean statements of correctness, together with
the proof obligations stating that the code meets them.

### Overview

There are several kinds of rust-written specs:

* *Function level specs*: `#[requires(..)]` / `#[ensures(\|res\|..)]` on a
  function. Those generate specification functions`<fn>.pre`, `<fn>.post`, a
  statement of correctness `<fn>.spec`, and the obligation `<fn>.spec.proof`
* *Trait level specs*: every trait gets a *companion* structure `<Trait>.Lawful`
  that registers the specifications attached to methods and constants. Every
  implementation generates a corresponding obligation of lawfulness.
    * If no annotation is written, the companion structure is empty.
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

impl B for Foo { ... }
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
theorem Foo.Insts.BLawful : specs.traits.supertraits.B.Lawful U32 := by sorry
```

One lawful instances per parent clause `<P>InstLawful : P.Lawful …
<X>Inst.<P>Inst`, one spec per annotated method `<m>_spec`. A trait with no
annotated method and no parent still gets an empty structure. Each
implementation gets a corresponding proof obligation.

#### Foreign traits

`X.Lawful` is only generated for local traits. For a foreign trait the generated
code refers to `X.Lawful` as if it existed, so a Lean library must provide it,
following the same conventions.


## Details

### Diagnostics

All messages start with `hax-specs:`. Warnings marked *(span)* point at the Rust
source when it is known and become errors with `-warnings-as-errors`; the others
are logged at warning level.

*  ``multiple #[requires] on `f`; ignoring extras`` (or `#[ensures]`) : More
   than one condition of a kind on an item: the first one is used.
* ``` `f` references unknown decoration uid …; skipping that side ``` : The
  decoration function of a condition is not in the LLBC.
* ``argument count mismatch for `f.pre` (takes N, expected M); dropping this
  condition`` : The condition does not take the arguments of the function (plus
  the result, for a post).
* ``dropping the contract of trait method `m`: its #[requires] is invalid`` (or
  `#[ensures]`) *(span)* : A condition of a trait method was dropped: the whole
  method contract is dropped.
* ``the contract of `m` is checked as a standalone spec only; it is independent
  of the trait-level contract`` Contract on a method of a trait impl.
* ``dropping the hax decoration `d`: it is attached to no translated item``
  *(span)* No item refers to this decoration function.
* ``dropping the hax decoration `d`: unsupported or invalid annotation, or part
  of a dropped contract`` A decoration that was not used (e.g. `decreases`, an
  extra or dropped condition).
* ``dropping the contract of function `f`: the function was not translated``
  *(span)* The annotated function failed to translate. Same for a trait (``the
  contract of trait `X` ``) and a trait impl (``the Lawful obligation of trait
  impl `I` ``).

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
- **Impl-level contracts**: see [Inputs](#inputs).
- **`ProofObligations.lean` is a template**: every proof is `sorry`, and it is
  overwritten on each extraction. Copy the obligations to a handwritten file to
  prove them. Nothing checks the copy against the template: after a
  re-extraction, compare the two (the theorems live in `namespace <crate>`, as
  in the generated files).
- **Built-in instances**: an instance that Charon resolves as built-in
  (`BuiltinOrAuto`, e.g. `Clone` for a tuple) is printed as `BuiltinClone …`,
  not as a `CoreModels` instance, so no `Lawful` theorem exists for it (e.g. to
  fill the `Clone` parent field of an impl of `Dup: Clone` for a tuple).
- **Dropped trait-method contracts** (with a warning, see
  [Diagnostics](#diagnostics)): when the generics of the conditions match those
  of the trait and the method ambiguously (e.g. a supertrait with an associated
  type, plus several method type parameters with the same bound that no input
  distinguishes), and when a postcondition must be synthesized for a method
  whose output type mentions a trait instance.

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
`Aeneas.Std.WP.triple_iff_exists_ok`, which turns a `⇓` triple into `∃ a, x =
.ok a ∧ P a`:

```lean
theorem specs.traits.basic.g.spec.proof … := by
  unfold specs.traits.basic.g.spec specs.traits.basic.g
  have h2 := FooInstLawful.f2_spec
  obtain ⟨b, hf1, -⟩ := (Aeneas.Std.WP.triple_iff_exists_ok).1 (FooInstLawful.f1_spec x (by simp))
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
