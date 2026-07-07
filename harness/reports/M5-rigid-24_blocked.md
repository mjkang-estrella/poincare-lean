# M5-rigid-24 blocked report

## Build result

`lake build Poincare.Global.JacobiNormSystem` completed successfully.

The build emitted existing upstream linter warnings; no errors were reported.

Forbidden-placeholder scan on `Poincare/Global/JacobiNormSystem.lean` found no
matches.

## Verified strict partial

New file: `Poincare/Global/JacobiNormSystem.lean`.

The module proves the non-vacuous scalar-system core:

* `JacobiNormSystem.chart_metric_pairing_hasDerivAt_covariant`
  converts coordinate derivatives of a time-varying endpoint metric pairing
  into pairings with the two covariant time derivatives, using the existing
  Christoffel/metric compatibility identity from `CoefficientEvolution.lean`.
* `JacobiNormSystem.normA_hasDerivAt` proves `a' = 2b`.
* `JacobiNormSystem.normB_hasDerivAt_of_oscillator` proves `b' = c - a`
  assuming the covariant oscillator derivative `D_t D_t J = -J`.
* `JacobiNormSystem.normC_hasDerivAt_of_oscillator` proves `c' = -2b` under
  the same oscillator hypothesis.

The model pinning is also formalized:

* `pinnedA q t = sin t ^ 2 * q`
* `pinnedB q t = sin t * cos t * q`
* `pinnedC q t = cos t ^ 2 * q`

with derivative theorems showing these solve the closed system.  The initial
values are pinned as

* `pinnedA q 0 = 0`
* `pinnedB q 0 = 0`
* `pinnedC q 0 = q`

so the correct initial tuple for `J(0)=0`, `D_t J(0)=w` is
`(0, 0, |w|²_anchor)`, not `(0, |w|²_anchor, |w|²_anchor)`.

The module also proves the polarization algebra:

* `symmetric_bilinear_polarization`
* `polarize_endpoint_pairing_of_quadratic`

This is the formal algebra needed to turn a quadratic `sin²` norm identity plus
linearity in the initial direction into the bilinear endpoint pairing.

## Remaining obstruction

I did not add a wrapper claiming the full coefficient formulas, exp-chart
pullback, or local-isometry theorem.

The missing assembly is still the genuine bridge from the exported
linearized-flow/Jacobi APIs to the covariant first- and second-derivative
hypotheses consumed by the scalar system:

* identify the chart-linearized state `(J,K)` with the covariant field pair
  `(J, D_t J)` used by `normB` and `normC`;
* feed `JacobiOscillator.lean`'s
  `coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_at_state`
  through that bookkeeping on an honest interval;
* package the resulting quadratic identity through ODE uniqueness into the
  exp-chart coefficient formulas and then the Cartan pullback/local-isometry
  surfaces.

The new module isolates the exact scalar-system target those future glue lemmas
need to feed, without introducing vacuous certificates or modifying existing
files.
