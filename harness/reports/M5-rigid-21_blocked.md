# M5-rigid-21 blocked report

## Build result

`lake build Poincare.Global.CartanLocalIsometry Poincare.Global.CartanExpansionBridge Poincare.Global.CartanPunctured Poincare.Global.CartanWeightInvariant`
completed successfully.

The build emitted existing linter warnings from upstream modules; no errors
were reported.

Optional aggregate check: `lake build Poincare` also completed successfully.
It emitted existing upstream linter warnings and a nonfatal
`LibrarySuggestions` panic while replaying `Poincare.Surgery`.

Additional checks:

* Forbidden-placeholder scan on the touched Lean files found no matches.
* `git diff --check -- Poincare/Global/CartanWeightInvariant.lean Poincare.lean`
  completed cleanly.

## Verified progress

New file: `Poincare/Global/CartanWeightInvariant.lean`.

The module records the pin verdict: the demanded source-side identification
with the round-sphere stereographic scalar is not chart-invariant.  The formal
pin is:

* `CartanWeightInvariant.chartRescaledAbsoluteCoefficient_two_zero_ne_pinned`

It models the elementary chart rescaling `z -> 2 z`, under which raw chart
metric coefficients are multiplied by `1 / 4` at the anchor while the geometry
is unchanged.  Therefore a source atlas chart cannot be forced to use the
sphere chart's pinned scalar coefficient.

The module adds the source-owned/invariant replacement surface:

* `CartanWeightInvariant.PuncturedWeightedAnchorPairing`
* `CartanWeightInvariant.PuncturedWeightInvariantEndpointExpansionBundle`
* `CartanWeightInvariant.puncturedSourceOwnedEndpointExpansion_of_metric_identity`
* `CartanWeightInvariant.puncturedWeightInvariantEndpointExpansionBundle_of_same_weight`
* `CartanWeightInvariant.puncturedWeightInvariantEndpointExpansionBundle_of_sourceOwned_and_roundSphere`

The old same-weight algebra is preserved as a special case, but the new bundle
keeps `κsource` and `κtarget` separate and requires the weighted anchor pairing
where any Jacobian/alignment factor must be accounted for.

The adjusted pullback consumers are proved:

* `CartanWeightInvariant.cartanMap_chart_pullback_identity_of_weightInvariantEndpointExpansionBundle`
* `CartanWeightInvariant.cartanMap_isLocalIsometry_on_punctured_normalBall_of_weightInvariantEndpointExpansionBundle`
* `CartanWeightInvariant.cartanMap_isLocalIsometry_on_punctured_normalBall_of_sourceOwned_and_roundSphere`

`Poincare.lean` now imports `Poincare.Global.CartanWeightInvariant`.

## Remaining obstruction

This task remains blocked at the geometric source-expansion proof, not at the
Cartan algebra.

The true source-side theorem still needs a non-vacuous derivation of a
source-owned punctured metric identity:

`CartanLocalIsometry.PuncturedWeightedSourceEndpointExpansion g x0 κsource`

for a `κsource` constructed from the source chart coefficient evolution.  The
existing fixed-vector derivative identity and scalar uniqueness machinery from
`CoefficientEvolution` are enough shape-wise, but the repository still does
not expose the constant-curvature/geodesic reduction proving that the source
coefficient satisfies the required ODE and endpoint expansion in the arbitrary
`extChartAt` source chart.

Once that theorem is available, it should feed
`puncturedSourceOwnedEndpointExpansion_of_metric_identity`, and the final
consumer should use
`cartanMap_isLocalIsometry_on_punctured_normalBall_of_sourceOwned_and_roundSphere`
with an explicit weighted anchor pairing instead of identifying the source
weight with the sphere chart weight.
