# M5-glob-23 blocked report

## Status

Blocked on upgrading the available chart-coordinate ray-cover identities to
the full manifold-level inputs required by
`RaysToBall.rigidStepCompatibleWith_of_common_source_expAt_ray_cover`.

Verified strict-partial payload added in the required new file:

- `Poincare/Global/RayCoverInputs.lean`

No existing Lean file was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.RayCoverInputs
  .common_source_expAt_inverse_and_reanchored_target_chart_coordinates
```

At every strict common-source point, it proves the two chart-coordinate facts
that are currently available without extra hypotheses:

1. the `x1` exponential partial homeomorphism inverse maps back to the source
   chart coordinate:

```lean
expAtChartOpenPartialHomeomorph (g := g) x1
  ((expAtChartOpenPartialHomeomorph (g := g) x1).symm ((chartAt E x1) x))
= (chartAt E x1) x
```

2. the re-centered Cartan germ has the expected target exponential chart
   coordinate:

```lean
expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) (s.map x1)
  (L1 ((expAtChartOpenPartialHomeomorph (g := g) x1).symm ((chartAt E x1) x)))
= (chartAt E (s.map x1)) (CartanMap.cartanMap g x1 (s.map x1) L1 x)
```

## Blocking boundary

The assembler still requires the stronger source endpoint identity

```lean
expAt g x1
  ((expAtChartOpenPartialHomeomorph (g := g) x1).symm ((chartAt E x1) x))
= x
```

The current `expAtChartOpenPartialHomeomorph` interface gives the inverse
identity in chart coordinates from target membership, but it does not export a
bridge from arbitrary membership in the partial-homeomorphism source/target to
the raw endpoint lying in the manifold chart source.  Without that bridge,
`chartAt` equality cannot be promoted to manifold-point equality.

The second requested input is also still not available at the needed strength:
the repository has anchor-based naturality for the re-centered Cartan map, but
no exported theorem identifying the old carried map `s.map x` with that
re-centered target exponential at every strict common-source point from the
induced alignment construction.  `NaturalityCascade` remains an eventual
one-dimensional reanchoring statement with explicit old-ray parameters and
side conditions, not a common-source pointwise velocity-identification
consumer.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/RayCoverInputs.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/RayCoverInputs.lean
git diff --check -- Poincare/Global/RayCoverInputs.lean
lake build Poincare.Global.RayCoverInputs
```

Actual result:

```text
placeholder scan: no matches
top-level declaration scan:
37:theorem common_source_expAt_inverse_and_reanchored_target_chart_coordinates

git diff --check -- Poincare/Global/RayCoverInputs.lean
exit status 0

lake build Poincare.Global.RayCoverInputs
✔ [3245/3245] Built Poincare.Global.RayCoverInputs (12s)
Build completed successfully (3245 jobs).
```

The build replayed pre-existing imported-module warnings. The new module built
successfully and introduced no reported warning.
