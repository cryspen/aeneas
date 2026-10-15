# namespace-shadow-qualified-names

## Summary

In Lean, a local variable named like the first component of a qualified name
(a module, a type or a trait namespace) turns `ns.f` into a projection out of
the variable (aeneas#1098, hax#2173, cryspen/aeneas#61). Name collision
checks now also consider such prefixes (fork PR #63). Duplicate of upstream
PR AeneasVerif/aeneas#1326.

## Invariants

- In Lean, no local name equals the first component of a registered
  qualified name. Other backends are unaffected.

## Tests

- `tests/src/namespace-shadow.rs` (`tests/lean/NamespaceShadow.lean`): a
  variable named after a module (`cshadow`), and after the first component of a
  nested module path (`outer.inner.f`). Without the patch, both outputs fail to
  elaborate in Lean (checked on 2026-10-07). Names that are registered on their
  own, such as a type's name, are already renamed by the exact-name collision
  check and do not exercise this patch.

## Rebase notes

- Drop this patch once upstream #1326 is merged.

## History

- 2026-10-07: bootstrapped from fork PR #63.
