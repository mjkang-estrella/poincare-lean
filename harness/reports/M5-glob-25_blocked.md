# M5-glob-25 blocked report

## Status

Blocked on the fully non-hypothetical target-ray identity requested by the
task, with verified strict-partial progress in the required new Lean file:

- `Poincare/Global/TargetRayIdentity.lean`

No existing Lean file was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.TargetRayIdentity
  .target_ray_identity_of_target_chart_exp_naturality
```

It proves the chart-to-manifold endpoint bridge for the old carried map:
if the old map satisfies target-chart exponential naturality at `x₁` on the
strict common source, and both the old target value and the target exponential
endpoint lie in the `s.map x₁` chart source, then the pointwise target-ray
identity consumed by `TwoBridges` follows:

```lean
s.map x =
  GeodesicTransport.expAt roundSphereMetric3 (s.map x₁)
    (L₁
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) x₁).symm ((chartAt E x₁) x)))
```

The proof is non-vacuous: it rewrites the charted target exponential endpoint
and applies injectivity of the target chart on its source.

## Blocking boundary

The current repository still does not export the old carried map's
target-chart exponential naturality at the re-anchor:

```lean
GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) (s.map x₁)
    (L₁
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) x₁).symm ((chartAt E x₁) x))) =
  (chartAt E (s.map x₁)) (s.map x)
```

`OffAnchorNaturality.lean` proves this only assuming
`InducedAlignment.CompatibleStep.RigidStepCompatibleWith s x₁ L₁`, which is
the final compatibility conclusion, so it cannot discharge the missing input
without circularity.  The germ-level source/target re-anchor laws in
`NaturalityCascade.lean` also still state that upgrading shifted rays to the
full common normal-coordinate source requires a separate cover theorem.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/TargetRayIdentity.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/TargetRayIdentity.lean
git diff --check -- Poincare/Global/TargetRayIdentity.lean
lake build Poincare.Global.TargetRayIdentity
```

Actual result:

```text
placeholder scan: no matches
top-level declaration scan:
33:theorem target_ray_identity_of_target_chart_exp_naturality

git diff --check -- Poincare/Global/TargetRayIdentity.lean
exit status 0

lake build Poincare.Global.TargetRayIdentity
✔ [3247/3247] Built Poincare.Global.TargetRayIdentity (13s)
Build completed successfully (3247 jobs).
```

The build replayed pre-existing imported-module warnings. The new module built
successfully and introduced no reported warning.
