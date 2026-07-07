# M5-rigid-6 done

## Artifact

- Added `Poincare/Global/ChartCurvatureBridgeZoneClose.lean`.

## Results

- Proved the zone field-choice naturality:
  `ChartCurvatureBridgeZoneClose.chartLeviCivita_curvatureOp_const_eq_chartTransported_curvatureOp_zone`.
- Instantiated the rigid-5 composition to remove the remaining bridge hypothesis:
  `ChartCurvatureBridgeZoneClose.chartCurvatureOf_chartChristoffelField_eq_chartTransported_curvatureOp_zone`.
- Proved the cutoff-one zone Kulkarni-Nomizu identity for constant-curvature-one metrics:
  `ChartCurvatureBridgeZoneClose.chartCurvatureOf_chartChristoffelField_constantCurvature_one_zone`.

## Verification

- `lake build Poincare.Global.ChartCurvatureBridgeZoneClose`
- Result: build completed successfully at 2026-07-07T02:02:00Z.

## Oscillator

- The interval oscillator `J'' = -J` was not added in this slice. The bridge needed by the rigid-4 machinery is now isolated as the unconditional zone identity above.
