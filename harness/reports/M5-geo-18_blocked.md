# M5-geo-18 blocked

## Files

- Added `Poincare/Global/GeodesicLinearized.lean`.
- Added this report.
- No existing Lean file, root import file, or harness input file was edited.

## Lean payload

The new module builds a strict partial toward the linearized geodesic-flow
comparison.

- `coordinateJacobiAcceleration` and `coordinateJacobiFlowOperator`: the
  shaped chart Jacobi operator.  For `ψ = (J,K)` it unfolds to
  `(K, -(DΓ)_γ(J)(γ',γ') - Γ_γ(K,γ') - Γ_γ(γ',K))`; the two bilinear terms
  are kept separate because no Christoffel symmetry lemma is used here.
- `linearizedGeodesicFlowOperator` and `linearizedGeodesicFlowFieldAlong`:
  the Fréchet-linearized first-order geodesic vector field
  `D(geodesicFlowField Γ)_{γ t}` along a base chart curve.
- Linearity lemmas for `linearizedGeodesicFlowFieldAlong`: zero, additivity,
  and scalar multiplication in the variation variable.
- `continuous_linearizedGeodesicFlowOperator_comp`: coefficient continuity
  from the available `C¹` flow field and a continuous base curve.
- `exists_isPicardLindelof_continuous_linearODE`,
  `exists_solution_continuous_linearODE`, and
  `linearODE_solution_uniqueOn_Icc`: local Picard-Lindelöf existence and
  interval uniqueness for continuous time-dependent linear ODEs.
- `exists_linearizedGeodesicFlow_solution` and
  `exists_chartChristoffel_linearizedGeodesicFlow_solution`: local existence
  for the variational equation along the chart Christoffel geodesic flow.
- `geodesicFlowField_taylor_remainder_isLittleO` and chart-specialized
  variants: the verified first comparison estimate at a single base state,
  namely the first-order Taylor remainder
  `F(q) - F(base) - DF_base(q-base) = o(q-base)`.

## Blocker

The full difference-quotient comparison was not closed.  The missing estimate
is the uniform compact-tube version of the Taylor remainder:

```lean
uniformly for τ in Icc 0 ε and perturbed states q_s(τ) near γ(τ),
  F(q_s τ) - F(γ τ) - D F (γ τ) (q_s τ - γ τ) = o(‖q_s τ - γ τ‖)
```

This is the single estimate needed before the Grönwall step can compare
`α(z₀, v + s • w) - α(z₀, v) - s • Ψ` and derive the fixed-time
`HasDerivAt` statement.  The pointwise `o` estimate is now proved, but the
module does not yet package continuity of `DF` on the common compact tube into
the uniform modulus required by that argument.

## Verification

Command run:

```bash
lake build Poincare.Global.GeodesicLinearized
```

Actual result:

```text
Built Poincare.Global.GeodesicLinearized (3.2s)
Build completed successfully (2832 jobs).
```

The final target build had no diagnostics from
`Poincare/Global/GeodesicLinearized.lean`; the displayed warnings are existing
replayed warnings from earlier modules.
