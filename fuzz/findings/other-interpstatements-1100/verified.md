# char-in-`match` crash — `Inconsistent state` / `Unexpected` in `eval_switch_raw`

**Severity:** MEDIUM (ungraceful crash on rustc-valid safe code). **Status:**
verified on fork AND upstream. **DEDUP RESULT: DUPLICATE of open upstream
AeneasVerif/aeneas#797** ("bug: Matching on chars throws an Uncaught exception";
reproducer `match c { 'a' => 0, _ => 1 }` — the exact symbolic variant here).
#797 itself asks that char-match "either be supported or throw a proper error
message", so the ungraceful-crash aspect is already captured upstream. NOT new;
do NOT file. Kept as a regression test + dedup entry.

## Fingerprint (primary — concrete char match)

| field        | value |
|--------------|-------|
| error_class  | `Other` |
| message      | `Inconsistent state` |
| file         | `interp/InterpStatements.ml` |
| line (fork)  | `1100` |
| line (upstream) | `1132` (within ±30 line-drift tolerance → same site) |
| top frame    | `Aeneas__InterpStatements.eval_switch_raw.(fun)` |

Verified via the harness oracle (`aeneas-fuzz one`):
- fork:     `crash[Other InterpStatements.ml:1100]`, dedup: NEW.
- upstream: `crash[Other InterpStatements.ml:1132]`, dedup: NEW.

## Root cause hypothesis

The switch/match evaluator (`eval_switch_raw`) does not handle a `char`
scrutinee. Two manifestations, both rustc-valid:

1. **Concrete** char literal (`let ch: char = 'g'; match ch { 'a' => .., _ => .. }`)
   → `[Error] Inconsistent state`, `InterpStatements.ml:1100` (see
   `observed-output.txt`). This is the concrete-evaluation path (a cousin of the
   N1 assert double-eval, which also fires in a concrete-`switch`/`assert`
   position).
2. **Symbolic** char (`fn g(ch: char) { match ch { 'a' => .., _ => .. } }`)
   → `(Failure Unexpected)` from `Charon__ValuesUtils.literal_as_scalar`
   (charon-ml `ValuesUtils.ml:6`) via `eval_switch_raw` at
   `InterpStatements.ml:1064` (see `observed-output-symbolic.txt`) — the
   evaluator tries to read the char literal *as a scalar* and fails.

So `char` matching is effectively unsupported and the code craises instead of
gating cleanly.

## Reproduce

```sh
cd <this dir>
sh repro.sh          # fork; set CHARON_UPSTREAM_BIN / AENEAS_UPSTREAM_ROOT for upstream
```

## Provenance

Discovered while de-risking the Phase-2 grammar generator's closed `char`-match
shape (`fuzz/harness/src/gen.rs`); minimized to the 3-line `f()` above and
verified by hand on clean fork + upstream binaries. The generator's `char` shape
was subsequently removed from the closed semantic-differential set (it only
produces crashes / Lean-`noncomputable` inconclusives), so this does not recur in
the oracle baseline.
