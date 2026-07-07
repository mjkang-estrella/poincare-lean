# M5-rigid-17 blocked: generic punctured source expansion still missing

## Blocked statement

The exact remaining source theorem is:

```lean
theorem puncturedWeightedSourceEndpointExpansion_of_constantCurvature_one
    {M : Type u}
    [TopologicalSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) (p₀ : RoundSphere3)
    (L : CartanMap.TangentAlignment g x₀ p₀) :
    CartanLocalIsometry.PuncturedWeightedSourceEndpointExpansion g x₀
      (fun v : ClosedSmoothModel 3 =>
        CartanExpansionBridge.roundSphereEndpointChartWeight p₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v)))
```

With that theorem, `CartanPunctured.cartanMap_anchor_or_punctured_localIsometry_of_sourceExpansion_and_roundSphere`
would instantiate the corrected anchor-or-punctured local-isometry consumer.

## Missing ingredient

The missing generic ingredient is the endpoint chart-metric/Jacobi assembly:
a theorem converting the interval-scoped radial derivative, transverse
`sin t / t` Jacobi derivative, integrated Gauss cross-term, and endpoint
Jacobi-pairing computation into the full bilinear identity required by
`CartanLocalIsometry.PuncturedWeightedSourceEndpointExpansion`.

The existing files expose the pieces, but not this generic full endpoint
source expansion:

- `CartanDifferential.lean` gives radial/transverse derivative and radial
  cross-pairing statements under explicit PL-flow, linearized-flow, Jacobi, and
  Gauss interval hypotheses.
- `GaussLemmaIntegrated.lean` gives scalar integrated transverse Gauss laws.
- `JacobiOscillator.lean` gives the sine formula under interval hypotheses.
- `GaussLemmaRadial.lean` still records `ChartGeodesicInitialVelocitySmoothDependence`
  as the smooth-dependence interface needed to package transverse Gauss data.

I therefore did not add a theorem pretending to prove the punctured source
expansion.

## Verification

Requested verification command:

```text
lake build Poincare.Global.CartanSourceFinal
```

Actual result: build completed successfully (`Build completed successfully
(3149 jobs)`). The build emitted existing upstream warnings.
