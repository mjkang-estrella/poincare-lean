# M5-glob-2 done report

## Delivered files

- `Poincare/Global/CartanContinuation.lean`
- `harness/reports/M5-glob-2_done.md`

No existing Lean files or `Poincare.lean` were edited.

## Proven Lean payload

The new module opens the Cartan continuation layer with non-axiomatic lemmas:

- `openPartialHomeomorph_eq_of_anchor_data_eq`
- `cartanMap_eq_of_anchor_data_eq`
- `cartanMap_eqOn_common_source_of_anchor_data_eq`
- `reanchoredOpenPartialHomeomorph`
- `reanchored_cartanMap_anchor`
- `firstStep_value_mem_target`
- `reanchored_anchor_mem_source`
- `reanchored_anchor_mem_target`
- `exists_reanchoredOpenPartialHomeomorph`
- `twoStep_restr_eqOnSource_of_differential_action`
- `twoStep_cartanMap_eq_of_differential_action`

The first group records the Cartan-germ determinacy seed: once the source
anchor, target value, and tangent alignment data are identified, the actual
Cartan map agrees on the common normal source.  The re-anchoring group builds
the next Cartan germ at an intermediate point with target value supplied by the
previous germ, using `tangentAlignment_nonempty` rather than a new certificate.

## Staging interface for rigid-10

The two-step lemmas consume the intended rigid-10 output as an explicit
`EqOn` hypothesis:

```lean
EqOn (CartanMap.openPartialHomeomorph g x₀ p₀ L₀)
  (reanchoredOpenPartialHomeomorph g x₀ p₀ L₀ x₁ L₁)
  ((CartanMap.openPartialHomeomorph g x₀ p₀ L₀).source ∩
    (reanchoredOpenPartialHomeomorph g x₀ p₀ L₀ x₁ L₁).source)
```

Geometrically, rigid-10 should prove this from equality of value and
differential action at `x₁`, plus exponential uniqueness for local isometries
on connected normal overlaps.  `CartanContinuation.lean` then converts it into
`≈`-equivalence of the restricted open partial homeomorphisms and a pointwise
two-step equality.

## Full continuation roadmap

1. Prove the rigid-10 differential-action theorem: the re-anchored Cartan data
   at `x₁` matches the original germ's value and differential, hence the two
   local Cartan maps agree on their common normal source.
2. Use the uniform normal radius/Lebesgue-number result to subdivide any path
   in `M` into finitely many steps whose consecutive points lie in a common
   normal-coordinate image.
3. Define continuation along a subdivided path by iterating the re-anchored
   Cartan germs, using the two-step restricted-source compatibility to remove
   subdivision dependence.
4. Prove homotopy invariance of the iterated continuation by filling a path
   homotopy with a sufficiently fine grid of uniform normal neighborhoods.
5. Use `SimplyConnectedSpace M` to make the continued value independent of the
   chosen path from the fixed basepoint, yielding one global function
   `Φ : M -> RoundSphere3`.
6. Prove `IsLocalHomeomorph Φ` from the local Cartan germ around each endpoint.
7. Feed `IsLocalHomeomorph Φ` into `CoveringSkeleton.lean`: compact source gives
   a covering map, and connected/simply connected hypotheses promote it to
   `M ≃ₜ RoundSphere3`.

## Verification

Command run:

```bash
lake build Poincare.Global.CartanContinuation
```

Actual result:

```text
✔ [2986/2986] Built Poincare.Global.CartanContinuation (2.9s)
Build completed successfully (2986 jobs).
```
