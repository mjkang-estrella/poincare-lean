# M5-model-2 done: round S3 metric smoothness field

## Completed

- Finished `roundSphereMetric3_inner_contMDiff` in
  `Poincare/Global/RoundSphereMetric.lean`.
- Added the assembled
  `roundSphereMetric3 : ClosedSmoothRiemannianMetric 3 RoundSphere3`.
- Added the defining lemma:

  ```lean
  theorem roundSphereMetric3_inner_eq :
      roundSphereMetric3.inner = roundSphereMetric3_inner
  ```

## Proof shape

- Added the model-fiber abbreviation `RoundSphereModel3`.
- Proved smoothness of the model pullback operation
  `roundSphereMetric3_modelInner` by reducing the operator-valued `ContDiff`
  goal to pointwise evaluations with `contDiff_clm_apply_iff`; each scalar
  evaluation is `D ↦ inner ℝ (D v) (D w)`.
- Used `contMDiff_coe_sphere` and `ContMDiffAt.mfderiv_const` to obtain
  smoothness of the inclusion derivative in tangent coordinates.
- Used `contMDiffAt_hom_bundle` and the local
  `inCoordinates_apply_eq₂` trivialization equation to identify the metric
  section with the model pullback operation in coordinates.

## Verification

Command run:

```bash
lake build Poincare.Global.RoundSphereMetric
```

Actual result: success.

The edited Lean file contains no `sorry`, no new `axiom`, and no
`native_decide`.

## Follow-up candidates

- Compute the Einstein constant for `roundSphereMetric3`.
- Prove constant sectional curvature for `roundSphereMetric3`.
