# M5-rigid-20 blocked report

## Build result

`lake build Poincare.Global.CoefficientEvolution` succeeded.

## Verified progress

New file: `Poincare/Global/CoefficientEvolution.lean`.

The module proves the fixed-vector compatibility identity:

* `GeodesicTransport.chartChristoffelField_fixed_pairing_eq_fderiv_metric`
  rewrites
  `((fderiv ℝ (chartGeodesicMetric g x₀) z) v) w w'`
  as
  `G z (Γ_z v w) w' + G z w (Γ_z v w')`.
* `GeodesicTransport.chart_metric_fixed_pairing_hasDerivAt_compatibility`
  proves the derivative identity for
  `τ ↦ chartGeodesicMetric g x₀ (zcurve τ) w w'`
  with fixed chart vectors, using the compatibility pairing identity.

The module also records the scalar ODE uniqueness surface:

* `CoefficientEvolution.scalar_weight_eq_of_same_ode_on_Icc`
  is the scalar linear ODE uniqueness theorem derived from the existing
  Picard-Lindelöf linear machinery.

## Pinning outcome

The sphere-side ODE was pinned first.  The explicit stereographic coefficient

`roundSpherePinnedWeight t = Real.cos (t / 2) ^ 4`

is proved to satisfy

`κ' = (-2 * Real.tan (t / 2)) * κ`

by `CoefficientEvolution.roundSpherePinnedWeight_hasDerivAt`.

The conformal-data check is also proved:

`CoefficientEvolution.stereographicScalarConformalFactor_two_tan_half`

shows that, away from the stereographic pole (`Real.cos (t / 2) ≠ 0`),

`stereographicScalarConformalFactor (2 * Real.tan (t / 2)) =
  roundSpherePinnedWeight t`.

## Remaining obstruction

The requested transverse-transverse endpoint pairing and punctured source
expansion are still not reachable from the current public APIs.

The new fixed-vector derivative identity supplies the compatibility side of
the coefficient evolution, but the repo still lacks a theorem reducing the
constant-curvature-1 source Christoffel structure along the radial geodesic to
the scalar coefficient ODE

`κ' = (-2 * Real.tan (t / 2)) * κ`

for the normalized source coefficient

`G(z(t))(w,w') / G(z₀)(w,w')`

with the needed transverse hypotheses and interval synchronization.  Without
that scalar ODE theorem, the ODE uniqueness lemma cannot identify the source
weight with the pinned sphere weight, and therefore cannot produce

`CartanLocalIsometry.PuncturedWeightedSourceEndpointExpansion g x₀
  (fun v => CartanExpansionBridge.roundSphereEndpointChartWeight p₀
    ((GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := roundSphereMetric3) p₀) (L v)))`.

No theorem wrapper for that missing expansion was added.
