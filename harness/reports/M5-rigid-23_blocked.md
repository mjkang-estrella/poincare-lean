# M5-rigid-23 blocked report

## Build result

`lake build Poincare.Global.CartanNormalCoords` completed successfully.

The build emitted existing upstream linter warnings; no errors were reported.

Forbidden-placeholder scan on `Poincare/Global/CartanNormalCoords.lean` found
no `sorry`, `axiom`, or `native_decide`.

## Verified strict partial

New file: `Poincare/Global/CartanNormalCoords.lean`.

The module contains one isolated non-vacuous statement:

* `CartanNormalCoords.expChart_symm_cartanChartMap_expChart_eq_tangentAlignment`

This proves the exp-normal-coordinate conjugation of the Cartan chart map:

`(expAtChart p₀).symm (cartanChartMap g x₀ p₀ L ((expAtChart x₀) v)) = L v`

under the two explicit source-membership hypotheses needed to avoid the
`OpenPartialHomeomorph` junk values.  This is the formal charted version of
`exp⁻¹_{p₀} ∘ Φ ∘ exp_{x₀} = L`.

## Remaining obstruction

The full requested normal-coordinate metric-coefficient and local-isometry
deliverables are still blocked by the public API boundary, not by the Cartan
linear conjugation.

The cited files expose the necessary ingredients only as interval-scoped or
directional statements:

* radial-radial: `GeodesicTransport.expAt_radialRadial_gauss_eventually` is a
  right-germ statement tied to `geodesicGermAt`, not a global coefficient
  theorem over `(expAtChartOpenPartialHomeomorph g x₀).source`;
* mixed: the integrated Gauss lemmas are stated for a chosen PL chart-flow
  family `α` and linearized solution `Ψ`, not as a mixed coefficient formula
  for `D(expAt)` in the exp chart;
* transverse-transverse: the Jacobi sin result gives the directional derivative
  `Real.sin t • w` under explicit harmonic-Jacobi interval hypotheses, but
  there is no exported bilinear theorem assembling these directional facts into
  the full exp-chart metric coefficient identity for arbitrary `u u'`.

Consequently I did not add a wrapper claiming the three coefficient formulas,
the pullback identity from those formulas, or the final local-isometry theorem.
The next required theorem is the genuine coefficient-assembly bridge from the
existing ray-law/Gauss/flow-derivative/Jacobi ingredients to
`CartanLocalIsometry.SourceEndpointExpansion` (and the matching target exp-chart
expansion) on the exp-chart source.
