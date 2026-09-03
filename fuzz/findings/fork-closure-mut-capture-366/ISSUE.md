## Description

Translating a function whose closure **reads** through a captured `&mut`
reference aborts with an uncaught internal error (exit 2), killing translation
of the crate. The input is valid Rust (rustc accepts it).

```rust
pub fn read_via_closure(a: &mut u8) -> u8 {
    let read = || -> u8 { *a };
    read()
}
```

## Observed

```
[Error] Can't end abstraction 1 as it is set as non-endable
Compiler source: interp/InterpBorrows.ml, line 1203          (non-fatal)

[Error] Internal error: please file an issue
Compiler source: symbolic/SymbolicToPureValues.ml, line 366   (fatal)
```

Fatal backtrace (top frames):

```
gtranslate_adt_fields                       SymbolicToPureValues.ml:366
adt_avalue_to_consumed_aux                  SymbolicToPureValues.ml:459-475
tavalue_to_consumed_aux                     SymbolicToPureValues.ml:422-423
abs_to_consumed                             SymbolicToPureValues.ml:653-655
translate_end_abstraction_synth_input       SymbolicToPureExpressions.ml:826
```

Exit code 2.

## Expected

Successful translation (the function is well-typed and borrow-checks).

## Root cause (hypothesis)

`gtranslate_adt_fields` (`src/symbolic/SymbolicToPureValues.ml:366`), in the
"preserve all the fields" branch:

```ocaml
| TAdtId _ ->
    if filter_fields then ...
    else
      (* We should preserve all the fields *)
      let infos, fields =
        List.split (List.map ([%try_unwrap] span) info_fields)   (* line 366 *)
      in ...
```

`[%try_unwrap]` raises when an element of `info_fields` is `None`. This is
reached during **backward translation of the closure's captured environment**
(the ADT that holds the `&mut u8` capture): one field's info is `None`, but the
non-filtering path assumes every field is `Some`.

## Controls (verified)

| program | result |
|---|---|
| closure **reads** captured `&mut u8`, called (repro above) | **CRASH** `SymbolicToPureValues.ml:366` |
| closure reads captured `&mut u8`, **never called** | **CRASH** (same site) |
| closure **mutates** `*a` through `&mut u8` | clean feature-gate rejection (not a crash) |
| closure reads a captured shared `&[u8]` | different site: `InterpBorrows.ml:1203` (cf. AeneasVerif/aeneas#804 family) |

The read-vs-mutate asymmetry is notable: mutating through a captured `&mut` is
gated cleanly, but *reading* through one hits this internal error.

## Environment / caveat

- Reproduced on the cryspen fork toolchain: `aeneas 363f1711-dirty` + charon
  **v0.1.196**, `-backend lean -abort-on-error`.
- During fuzzing (2026-07-26) the **upstream** toolchain (AeneasVerif `main`
  `3a8586fa` + charon **v0.1.225**) translated the *same* input **successfully**.
  The crash-site function `gtranslate_adt_fields` is byte-identical between the
  fork and upstream sources, so this is very likely an **aeneas-or-charon
  version delta** — possibly already fixed upstream and resolvable by rebasing
  onto newer aeneas + charon, rather than a fork-introduced regression. Worth
  confirming by rebuilding at the fork's charon-0.1.196 era before investing in
  a fix.

## Provenance

Found by the in-tree fuzzing harness (`fuzz/`); auto-minimized to the two-line
function above. Repro + controls: `fuzz/findings/fork-closure-mut-capture-366/`.
