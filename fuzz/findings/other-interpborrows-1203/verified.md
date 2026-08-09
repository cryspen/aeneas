# Verified triage: other-interpborrows-1203

## Verdict

- **VALID crash:** YES on the FORK toolchain; rustc accepts `min.rs`.
- **Classification: (C) DUPLICATE** of the known upstream issue
  **AeneasVerif/aeneas#804** ("closures that return references derived from
  captured state"). Underlying nature is a real sanity-check crash (class-A-like),
  but it is an already-known, already-skip-listed limitation, not a new finding.
- **Genuinely NEW:** NO.
- **Proposed severity:** LOW as a *new* item (known issue). It is fork-only and
  the seed test is already `//@ [!lean] skip` in `tests/src/`.

## Fingerprint

- message: `Can't end abstraction N as it is set as non-endable`
- fork:     `interp/InterpBorrows.ml:1203` (`end_abs_aux`, the `can_end` guard)
- reached during **backward** symbolic evaluation
  (`evaluate_function_symbolic_synthesize_backward_from_return`).
- **upstream: DOES NOT REPRODUCE** (exit 0).

## Minimized repro (final)

```rust
pub fn each_ref(s: &[u8; 1]) -> [&u8; 1] {
    std::array::from_fn(|i| &s[i])
}
```

The `[u8; 0] -> [&u8; 1]` in the original auto-min was an incidental
`IntEdge` mutation; the 1-element version is cleaner, and the original,
unmutated issue-804 form `each_ref(s: &[u8;10]) -> [&u8;10]` crashes identically.

## Minimization / shape sensitivity (fork)

| program                                         | result |
|-------------------------------------------------|--------|
| `from_fn(|i| &s[i])` on `[u8;10]` (orig #804)   | CRASH  |
| `from_fn(|i| &s[i])` on `[u8;1]`                | CRASH  |
| manual `[&s[0], &s[1]]` on `[u8;2]`             | OK     |
| manual `[&s[0]]` on `[u8;1]`                    | OK     |

=> The trigger is specifically the **closure passed to `array::from_fn`**
returning a reference into captured state, not arrays-of-references in general.

## Root cause (file:line)

`InterpBorrows.ml:1201-1205`: `end_abs_aux` refuses to end an abstraction whose
`can_end = false` (`[%craise] "Can't end abstraction N as it is set as
non-endable"`). During backward synthesis of `each_ref`, ending the shared loans
of the closure/array abstraction chain (`end_abs_loans` -> `end_shared_loan_aux`
-> `end_borrow_aux` -> `end_abs_aux`) reaches an abstraction that was marked
non-endable. This is the *safety net* that the bug-hunt doc's latent hazard **L2**
calls out (`InterpBorrows.ml:1201-1205`, re-kinding of suffix/join abstractions
with `can_end := true` and no endability assertion). Here it fires legitimately:
the array-of-refs-from-closure shape produces an abstraction the ender is asked
to end but which is (correctly or not) frozen. This is the concrete surface of
issue #804 on the older (charon v0.1.196) fork base.

## Upstream applicability

NOT AFFECTED on current upstream (charon v0.1.225 + `/tmp/aeneas-upstream`).
Upstream translates the crate to Lean (exit 0), axiomatizing
`core::array::from_fn` (`axiom core.array.from_fn ...`) and emitting the closure
`call_mut`/`call_once` bodies rather than driving backward evaluation into the
non-endable abstraction. So the crash was effectively resolved / worked around
between the two bases. (The two `.llbc` versions are mutually incompatible —
v0.1.196 vs v0.1.225 — so the toolchains cannot be crossed to isolate charon vs
aeneas; both variables moved together.)

## Fork-local-fix relevance

None. Crash is interpreter-level; fork's uncommitted edits are pure-ir/driver only.
