# M5-rigid-61 blocked: target interval package specialized, unscaled cascade feed still missing

## Status

Added `Poincare/Global/TargetPackage.lean` and did not edit existing Lean
modules, including `Poincare.lean`.

The new module specializes the generic cutoff-one norm assembly to the actual
round-sphere target metric by using
`roundSphereMetric3_hasConstantSectionalCurvature_one`, then feeds the
resulting target family-level quadratic identities into
`CascadePinned.hosted_rescaled_endpoint_pairing_eq_pinned_of_quadratic_and_linearized_uniqueOn_Icc`.

## Verified payload

The new module exports:

```lean
Poincare.TargetPackage.target_normA_eq_pinned_on_cutoff_one_Icc
Poincare.TargetPackage.target_hosted_quadratic_normA_eq_pinned_on_cutoff_one_Icc
Poincare.TargetPackage.target_hosted_rescaled_endpoint_pairing_eq_pinned_of_interval_norm_package
```

The final theorem proves the honest pinned endpoint formula for the target
hosted cascade shape with rescaled initial data:

```lean
∀ w w' : E,
  CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p₀) v)
      (Ψ w T).1 (Ψ w' T).1 =
    Real.sin T ^ 2 *
      CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • w) (T⁻¹ • w')
```

This theorem uses the target curvature witness internally and consumes the
non-vacuous interval/norm hypotheses required by
`CartanIsometryTheorem.actual_jacobi_norms_eq_pinned_on_cutoff_one_Icc`:
base `HasDerivAt`, linearized `HasDerivAt`, chart target membership,
cutoff-one germs, unit speed, orthogonality, differentiability of the blended
metric, scalar closed-ball membership, pinned closed-ball membership, and the
three initial scalar values.

## Remaining blocker

This still does not fire `EqualityChain.lean`, because that consumer needs the
unscaled target feed:

```lean
∀ a a' : E,
  CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p₀) (L v))
      (Ψt (L a) Tt).1 (Ψt (L a') Tt).1 =
    Real.sin θt ^ 2 * CartanMap.targetAnchorChartMetric p₀ (L a) (L a')
```

The available cascade-produced family has initial data

```lean
∀ w : E, Ψt w 0 = ((0 : E), Tt⁻¹ • w)
```

so the package proved from the current pinned bridge yields the rescaled
anchor metric:

```lean
Real.sin Tt ^ 2 *
  CartanMap.targetAnchorChartMetric p₀ (Tt⁻¹ • L a) (Tt⁻¹ • L a')
```

No exported theorem currently converts the actual target cascade's rescaled
hosted family into the unscaled `EqualityChain` formula above.  Equivalently,
the missing theorem must combine the hosted `(u,T)`/speed normalization with
the target interval package so that the sine factor and the two `Tt⁻¹` anchor
scales are replaced by the `θt`-formula on `(L a, L a')`.

The current `CartanCascade.lean` export also does not expose the interval/norm
facts needed to instantiate the package automatically for its target `αt` and
`Ψt`: in particular the `HasDerivAt` upgrades, unit-speed and orthogonality
facts, scalar closed-ball memberships, and initial `normA/normB/normC` values
for the actual target family remain outside the exported interface.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/TargetPackage.lean
```

Actual result: no matches.

Whitespace check:

```bash
git diff --check -- Poincare/Global/TargetPackage.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.TargetPackage
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module built successfully.

Final build lines:

```text
✔ [3175/3175] Built Poincare.Global.TargetPackage (15s)
Build completed successfully (3175 jobs).
```
