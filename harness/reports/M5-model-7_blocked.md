# M5-model-7 blocked

## Scope

Added `Poincare/Global/RoundSphereCurvature.lean`.  No existing Lean source
file and no root import file was edited.

The frozen final theorem

```lean
theorem roundSphereMetric3_hasConstantSectionalCurvature_one :
    HasConstantSectionalCurvature3 roundSphereMetric3 1
```

is not proved in this partial.  I stopped at the first missing non-vacuous
transport bridge rather than adding a wrapper.

## Proved intermediates

General Christoffel germ-locality:

```lean
theorem CovariantDerivative.christoffelOneForm_congr_of_eventuallyEq
```

Round sphere chart coefficient transport:

```lean
theorem stereoInvFunAuxConformalFactor_roundSphereChartModelEquiv_symm
theorem roundSphereMetric3_chartMetric_eq
theorem roundSphereMetric3_blendedChartMetric_eq_conformal_of_cutoff_one
theorem roundSphereMetric3_chartBilin_eq_conformal_of_cutoff_one
theorem roundSphereMetric3_blendedChartMetric_eventuallyEq_conformal
```

Stereographic conformal Christoffel specialization:

```lean
theorem stereoInvFunAuxConformalFactor_grad
theorem christoffelOneForm_stereoInvFunAuxConformalFactor
```

Round sphere transported chart Christoffel bridge:

```lean
theorem roundSphereMetric3_chartChristoffelField_eq_sphereChristoffel_of_eventuallyEq_one
theorem roundSphereMetric3_chartChristoffelField_anchor_eq_sphereChristoffel
```

These lemmas prove the near-anchor coefficient representation requested in the
task and identify the transported chart Christoffel field for
`roundSphereMetric3` with the explicit `sphereChristoffel` field at the chart
anchor.

## Single missing bridge

The remaining missing bridge is:

```lean
-- expected shape, not yet proved
chart curvature of GeodesicTransport.chartLeviCivita roundSphereMetric3 x
on constant model extensions at extChartAt (𝓡 3) x x
=
mfderiv-pushforward / pullback of
CovariantDerivative.curvatureOp roundSphereMetric3.leviCivita
  (extend E3 u) (extend E3 w) (extend E3 a) x
```

Equivalently, the repo has value-level and connection-germ bridges
(`chartLeviCivita_eventuallyEq_closed`) and the model expansion
(`curvatureOp_modelLeviCivita_extend`), but I did not find a packaged theorem
that transports curvature of the chart `modelLeviCivita` connection back to
the manifold `curvatureOp` on canonical `extend` fields.  Proving the frozen
target now needs this bridge plus the final lowering step using
`roundSphereMetric3_chartMetric_eq` and
`conformalChartMetric_chartCurvatureOf_sphereChristoffel`.

## Next decomposition

1. Prove a chart curvature transport theorem for a closed metric:
   if the transported chart connection and the closed Levi-Civita connection
   agree as germs near `x`, then their curvature operators agree at `x` after
   applying the chart derivative/inverse-chart derivative to canonical
   extensions.
2. Specialize that theorem to `roundSphereMetric3` and the anchor chart.
3. Rewrite chart coefficients and Christoffel data using the lemmas in
   `RoundSphereCurvature.lean`.
4. Apply `conformalChartMetric_chartCurvatureOf_sphereChristoffel` and convert
   the chart Kulkarni-Nomizu form back to
   `ClosedSmoothRiemannianMetric.tensorKulkarniNomizuAt`.
5. Immediate next corollaries after the frozen theorem:
   `roundSphereMetric3.IsEinstein3` / `∀ x, roundSphereMetric3.IsEinsteinAt 2 x`
   via the constant-curvature-to-Einstein algebra, then
   `PositiveEinsteinMetric3 RoundSphere3`.

## Verification

Command run:

```bash
lake build Poincare.Global.RoundSphereCurvature
```

Result: success.  Lean built `Poincare.Global.RoundSphereCurvature`; the build
reported existing upstream linter warnings, with no errors in the new module.
