# M5-model-8 done report

## Completed

- Added `Poincare/Global/RoundSphereWitness.lean` without editing existing
  Lean files or `Poincare.lean`.
- Proved the chart-curvature germ locality lemma:
  `chartCurvatureOf_congr_of_eventuallyEq`.
- Proved the round-sphere Christoffel curvature congruence near the anchor:
  `roundSphereMetric3_chartCurvatureOf_chartChristoffelField_eq_sphereChristoffel`.
- Proved the lowered global/chart curvature bridge:
  `roundSphereMetric3_inner_chartTransported_curvature_eq_chartMetric`.
- Proved the anchor chart/global metric and Kulkarni-Nomizu comparisons:
  `roundSphereMetric3_chartMetric_anchor_eq_conformal` and
  `roundSphereMetric3_tensorKulkarniNomizuAt_eq_chart`.
- Proved the frozen deliverable:

```lean
theorem roundSphereMetric3_hasConstantSectionalCurvature_one :
    HasConstantSectionalCurvature3 roundSphereMetric3 1
```

## Verification

Command run:

```bash
lake build Poincare.Global.RoundSphereWitness
```

Result: success. The build completed `3108` jobs. The output contains existing
dependency lint warnings; the final verification run emitted no warning from
`Poincare/Global/RoundSphereWitness.lean`.

## Optional corollaries

The optional Einstein and `PositiveEinsteinMetric3 RoundSphere3` corollaries
were not added. The constant-curvature witness is complete; the optional
constant-curvature-to-Einstein direction was not forced in this task because it
is outside the frozen deliverable and was not already a short direct interface.
