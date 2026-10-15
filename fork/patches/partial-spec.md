# partial-spec

## Summary

Adds the partial-correctness predicate `partialSpec x p_ok p_fail p_div`
(fork PRs #4, #31, #33): if `x` returns `a` then `p_ok a`, if it fails with `e`
then `p_fail e`, if it diverges then `p_div`. Unlike `spec`, it states what
happens on panics, so library operations can be specified without
preconditions.

`@[step]` accepts `partialSpec` theorems: for a theorem `T` it generates

- `T.step_spec`, a total-correctness `spec` whose hypotheses are the negated
  failure cases (one `h_fail_i` per disjunct, after pushing `¬` inwards) and
  the negated divergence condition, used by `step`/`step*`;
- `T.mvcgen_spec`, an `@[spec]` triple for `mvcgen` (needs
  `mvcgen-result-specs`).

A failure predicate written as `fun | C₁ => P₁ | … | _ => False` is first
rewritten into a disjunction with `error_pred_eq_disj`.

## Invariants

- `step` never sees `partialSpec` directly, only the generated `.step_spec`.
- `error_pred_eq_disj` enumerates exactly the constructors of `Error`.
- The theorems that generated proofs refer to (`spec_of_partialSpec`,
  `partialSpec_to_mvcgen`, `error_pred_eq_disj`, the `step_fail_*` lemmas,
  `mvcgen_fail_failEq_iff`, `mvcgen_fail_False_iff` and `mvcgen_uncurry'`) are
  public: generated proofs live in other modules.

## Differences from upstream

- `@[step]` on a theorem that cannot be registered (for instance one that is
  not a `spec`/`partialSpec` statement) only logs a warning and skips the
  theorem (`applyStepAttr` in `Tactic/Step/Init.lean`). Upstream's
  `saveStepSpecFromThm` raises an error instead; only the generation of the
  `mvcgen` lemma is a warning there. In the library, `ci-lean-iofail` turns
  such warnings into CI failures.

## Tests

- `backends/lean/Aeneas/Tactic/Step/Tests/SpecPartial.lean`: `step*` and
  `mvcgen` on single and chained `partialSpec` axioms, `#guard_msgs` on the
  generated `step_spec`/`mvcgen_spec` (one and several error cases,
  divergence).

## Rebase notes

- `reduce-error-cases` rewrites `error_pred_eq_disj` and the error cases in the
  tests; keep its anchors (the `theorem error_pred_eq_disj` header and body
  shape) intact.

- `Tactic/Step/Init.lean` was ported onto upstream's module-system version:
  upstream's `generateMvcgenSpec`/`saveStepSpecFromThm` were replaced by the
  registration code of this patch, with every `def` marked `meta` and the helper
  theorems public.

## History

- 2026-10-07: bootstrapped from fork PRs #4 (infrastructure part), #31 and #33
  (Step/Init.lean fixes); ported to the ITree-based monad (#1180, #1344) and the
  module system (#1230).
