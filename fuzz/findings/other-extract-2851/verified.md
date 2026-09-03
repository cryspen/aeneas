# Verified triage: other-extract-2851

## Verdict

- **VALID crash:** NO. This is **not a crash**. aeneas exits 0 and generates the
  Lean output. The finding is a **harness false-positive**.
- **Classification: INVALID** (does not fit A/B/C — there is no failure). If
  forced: closest to (B), but it is not even a rejection — translation succeeds.
- **Genuinely NEW:** NO.
- **Proposed severity:** NONE (informational / harness bug).

## What actually happens

```
[Warn] When retrieving the builtin information for trait decl
       'core::iter::traits::iterator::Iterator', could not find the information
       for item 'collect'. The model defined in the Lean library seems to be
       missing the corresponding field.
Compiler source: extract/Extract.ml, line 2851
[Info] Generated: .../Crate.lean
[Info] Total execution time: 0.12 s
```

Exit code **0**. `Extract.ml:2851` is a `[%warn]` (not `[%craise]`) — the
fallback branch that, when a builtin trait model lacks a method field, warns and
computes the name from the LLBC definition instead. Extraction proceeds and a
valid `Crate.lean` is produced.

## Why the fuzzer flagged it

The oracle matched on the `Compiler source: <file>, line <n>` marker, which
`[%warn]` prints in exactly the same format as `[%craise]`. There was no
exception and no non-zero exit. See the harness note in
../unreachable-interploops-407/verified.md.

## Minimized repro (final)

```rust
pub fn collect() {
    let s = "hello";
    let _chs: Vec<char> = s.chars().collect();
}
```

The `StmtDup` mutation in the auto-min was irrelevant; a single `collect()` call
emits the same warning.

## Upstream applicability

Same benign behavior: upstream warns at `Extract.ml:2868` and exits 0. Not a bug
on either toolchain.
