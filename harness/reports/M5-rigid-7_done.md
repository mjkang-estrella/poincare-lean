# M5-rigid-7 done

## Artifact

- Added `Poincare/Global/JacobiOscillator.lean`.

## Results

- Proved the cutoff-one zone lowered contraction:
  `Poincare.chartCurvatureOf_chartChristoffelField_unit_orthogonal_lowered_zone`.
- Raised the contraction to vector form:
  `Poincare.chartCurvatureOf_chartChristoffelField_unit_orthogonal_zone`.
- Packaged Christoffel symmetry and derivative-slot symmetry for
  `GeodesicTransport.chartChristoffelField`:
  `Poincare.chartChristoffelField_eventually_symm`,
  `Poincare.chartChristoffelField_symm`,
  `Poincare.chartChristoffelField_fderiv_symm`.
- Proved the cutoff-one covariant coordinate Jacobi oscillator:
  `Poincare.coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_zone`
  and its state form
  `Poincare.coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_at_state`.
- Converted integrated Gauss orthogonality from `chartGeodesicMetric` to the
  transported chart metric at cutoff-one times:
  `Poincare.GeodesicTransport.chart_initialVelocity_integrated_transverse_gauss_orthogonal_chartMetric`.
- Exposed the sine position formula from the existing harmonic uniqueness
  theorem:
  `Poincare.jacobi_position_eq_sin_smul_on_Icc`.

## Verification

- `lake build Poincare.Global.JacobiOscillator`
- Result: build completed successfully (`Build completed successfully (3134 jobs)`).
- `rg -n "sorry|axiom|native_decide" Poincare/Global/JacobiOscillator.lean`: no matches.

No existing Lean file or import aggregator was edited.
