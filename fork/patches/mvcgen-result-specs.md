# mvcgen-result-specs

## Summary

Makes `Std.Do`'s `mvcgen` usable on Aeneas programs (fork PRs #18, #31):

- `PostCond` accessors for the error monad's post-shape (`PostCond.ok`,
  `.fail`, `.div` and their `…Assertion` variants), so that no proof has to
  write raw projections such as `Q.2.1`;
- `@[spec]` lemmas for `ok` and `fail`, and `loop_spec` for `loop` (with an
  invariant and a well-founded measure; the measure is not needed when the
  postcondition allows divergence, i.e. `⇓?`);
- `@[spec]` on `uncurry`, so that `mvcgen` sees through tuple patterns in `do`
  blocks;
- lemmas relating triples to `ok` (`triple_post_eq_iff_eq`,
  `triple_iff_exists_ok`, `triple_with_self`, `triple_in_hypothesis`). These
  are used by rust-core-models proofs.

## Invariants

- mvcgen's WP for the error monad maps `ok` to the success postcondition,
  `fail e` to the failure postcondition at `e`, and divergence to the
  divergence postcondition; the `PostCond` accessors project exactly these.
- `loop_spec` is sound for both total (`⇓`, measure required) and partial
  (`⇓?`) correctness.
- No raw `Q.2.…` projections outside the accessor definitions.
- The specs and triple lemmas are universe-polymorphic (`Type u`), like the
  code Aeneas extracts (`Type _` binders since upstream #1412). In
  `loop_spec`, the state and result types share one universe: the body's
  triple is stated at `ControlFlow α β`, and its post-shape must be the
  same as `P`'s.

## Tests

- `backends/lean/Aeneas/Tactic/Step/Tests/MvcgenResult.lean`: `ok`/`fail` with
  `⇓` and `⇓?`, the accessors, `uncurry` in `do`, `loop_spec` in both modes,
  `triple_iff_exists_ok`, and the same on values in `Type 1` (with the lemmas
  stated for `Type`, the `triple_iff_exists_ok` and `loop_spec` examples
  fail).

## Rebase notes

- Upstream changed the monad to an ITree and added a level to the post-shape
  for "other effects" (#1180): divergence is the fourth component. Keep the
  accessors in sync with upstream's `WP` instance (`RustM.instWP` in
  `Std/WP.lean`).

- `loop_spec` is proved by fixpoint induction when the postcondition allows
  divergence. The admissibility it needs is `wp_admissible_of_div`: mvcgen's WP
  only looks at the head of a program, and the head of a chain's supremum
  occurs in the chain (`ITree.csup_ret_mem`/`ITree.csup_vis_mem`). Otherwise,
  by well-founded induction on the termination measure.

- Since Lean v4.35.0 the `mvcgen` tactic syntax is deprecated in favour of
  `vcgen`. Test files that use it set `linter.deprecated.syntax false`, as
  upstream's `MvcgenSpec.lean` does, so that the `--iofail` build stays quiet.

## History

- 2026-10-07: bootstrapped from fork PRs #18 and #31; ported to the ITree-based
  monad (#1180), its generic WPs (#1344) and the module system (#1230).
- 2026-10-20: lemmas generalised to `Type u` (upstream #1412); ported to Lean
  v4.35.0 (`wp_admissible_of_div`, deprecated `mvcgen` syntax in tests).
