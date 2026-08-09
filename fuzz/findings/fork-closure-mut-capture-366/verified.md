# FORK-ONLY: a closure reading through a captured `&mut` crashes at SymbolicToPureValues.ml:366

## Summary

On the **fork** branch, translating a function that defines a closure which
**reads** through a captured `&mut` reference aborts with an uncaught internal
error:

```
[Error] Internal error: please file an issue
Compiler source: symbolic/SymbolicToPureValues.ml, line 366
```

Minimal reproducer (`min.rs`, valid Rust; `rustc` accepts it):

```rust
pub fn read_via_closure(a: &mut u8) -> u8 {
    let read = || -> u8 { *a };
    read()
}
```

## Classification

**Class A — genuine translator bug (crash on valid Rust).**

Justification:
- `rustc --edition=2021 -C overflow-checks=on` accepts the input.
- The failure is an uncaught OCaml `Failure` (exit 2, backtrace), and aeneas
  itself prints "Internal error: please file an issue" — i.e. the compiler
  self-classifies it as a bug, not a feature gate. Not Class B.
- Fingerprint `symbolic/SymbolicToPureValues.ml:366` is not in the findings DB.
  Not Class C. (Note: a preceding non-fatal `InterpBorrows.ml:1203` diagnostic
  is printed, but the *fatal* uncaught exception is at
  `SymbolicToPureValues.ml:366`.)

## Upstream status

**FORK-ONLY.** Upstream (aeneas `main` 3a8586fa, charon v0.1.225) translates the
same input successfully (exit 0, `Closure.lean` generated). Only the fork branch
`dump-pure-ir-minimal` (aeneas `6a3fc35b-dirty`) crashes. **This is a fork
regression, not filable upstream.**

## Root cause (file:line)

Fatal craise: `src/symbolic/SymbolicToPureValues.ml:366`, function
`gtranslate_adt_fields`, in the **"preserve all the fields"** branch:

```ocaml
| TAdtId _ ->
    if filter_fields then (
      [%sanity_check] span (List.for_all Option.is_none info_fields);
      (ctx, None))
    else
      (* We should preserve all the fields *)
      let infos, fields =
        List.split (List.map ([%try_unwrap] span) info_fields)   (* line 366 *)
      in
      ...
```

`[%try_unwrap]` raises `Failure` when an element of `info_fields` is `None`.
Reached during **backward translation** of the closure's captured environment
(an ADT holding the `&mut u8` capture):
`SymbolicToPureExpressions.translate_end_abstraction_synth_input`
→ `abs_to_consumed` → `tavalue_to_consumed_aux` → `adt_avalue_to_consumed_aux`
→ `gtranslate_adt_fields`.

For the closure-env ADT that captures a `&mut` reference, one field's info is
`None`, but the non-filtering ("preserve all fields") path assumes every field
is `Some`. This path is tied to the fork branch's recent field-**preservation**
work (commits "pure micro-passes: preserve carriers with a cosmetic-only
allowlist" / "exempt 'preserved' defs from value-eliminating passes"), which
explains why upstream is unaffected.

## Controls (verified on fork)

| program | verdict |
|---|---|
| closure reads captured `&mut u8`, **called** (min.rs / C5) | **CRASH** SymbolicToPureValues:366 |
| closure reads captured `&mut u8`, **never called** (C2) | **CRASH** SymbolicToPureValues:366 |
| closure reads captured shared `&[u8]` (C3) | different path: `InterpBorrows.ml:1203` (known #804 family) |
| closure **mutates** `*a` through `&mut u8` (C4) | clean `reject[expected]` (feature gate) |
| same min.rs on **upstream** | **OK** (exit 0, Lean generated) |

## Severity

**MEDIUM.** Valid, realistic Rust (a helper closure closing over a `&mut`) hard-
crashes the fork translator and aborts the whole crate. Fork-only, so it affects
the branch under study but not released upstream.

## Provenance

Found by the Aeneas fuzzing harness (`fuzz/`), fork Wave A (seeds via
`internalerror-symbolictopurevalues-366`; 4 independent hits across workers
A2/A4/A5). Seed file `tests/src/closures.rs::call_fn_shared`, `BorrowFlip`
mutation; auto-minimized, then hand-reduced to the two-line function above.

## CORRECTION (coordinator verification, 2026-07-26)

The "tied to the fork's field-preservation commits" root-cause claim above is
**not supported** and is retracted:

- The crash-site function `gtranslate_adt_fields` in
  `src/symbolic/SymbolicToPureValues.ml` is **byte-identical** between the fork
  and upstream `main` (verified by diff; only a comment differs). So the fork did
  not modify this code path.
- The uncommitted fork fixes (F1–F3) touch only `-dump-pure-ir` dump points and
  the pure-micro-pass `is_preserved` gate, both of which run outside/after
  symbolic-to-pure. They cannot cause a crash here, and indeed N3 reproduces
  without `-dump-pure-ir`.
- Fork vs upstream differ in **both** aeneas version and charon version
  (0.1.196 vs 0.1.225), and their `.llbc` formats are mutually incompatible, so
  the toolchains cannot be cross-matched to isolate the variable. The real
  differentiator (a charon closure-lowering change vs an upstream aeneas fix
  that postdates the fork's base) is **unresolved**.

**Disposition:** confirmed crash on the fork toolchain on valid Rust, but NOT a
confirmed fork-aeneas bug and very possibly already fixed upstream. DO NOT FILE
until disentangled — e.g. build upstream aeneas at its charon-0.1.196-era commit
and re-test N3 there.
