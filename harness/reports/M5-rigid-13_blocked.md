Blocked: the full requested nonzero normal-ball theorem still needs a theorem
promoting the interval-scoped directional endpoint facts to the full bilinear
endpoint metric expansion fields.

Verified partial progress:

* Added `CartanLocalIsometry.SourceEndpointExpansion`,
  `TargetEndpointExpansion`, and `EndpointExpansionBundle`.
* Added `endpointExpansionBundle_of_metric_expansions`, a non-vacuous
  constructor from the exact source/target metric expansion identities.
* Added `cartanMap_chart_pullback_identity_of_endpointExpansionBundle` and
  `cartanMap_isLocalIsometry_on_normalBall_of_endpointExpansionBundle`, so
  rigid-11 can now consume the packaged endpoint expansion bundle directly.
* Added `Poincare/Global/CartanIsometryFinal.lean` with the unconditional
  anchor metric-preservation/local-isometry statement
  `CartanIsometryFinal.cartanChartMap_anchor_isLocalIsometry`.

Remaining obstruction:

The existing interval facts in `CartanDifferential.lean`,
`JacobiOscillator.lean`, `GaussLemmaIntegrated.lean`, and
`GeodesicSpeed.lean` prove radial/transverse derivatives and the Gauss
orthogonal cross term under PL/interval/cutoff hypotheses.  I did not find an
available theorem that converts those directional derivative statements into
the full bilinear chart-metric expansion required by the normal-ball endpoint
bundle for arbitrary `u u'`.  Adding the requested constant-curvature source
expansion, round-sphere target expansion, and unconditional nonzero
normal-ball local isometry would require that missing bridge.

Verification:

`lake build Poincare.Global.CartanLocalIsometry Poincare.Global.CartanIsometryFinal`
completed successfully.  The build produced existing project warnings in
upstream files and built both requested modules successfully.
