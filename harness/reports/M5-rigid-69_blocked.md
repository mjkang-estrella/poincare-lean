# M5-rigid-69 blocked: all-direction `horth` pinned false, transverse feed proved

## Pin outcome

The all-direction endpoint orthogonality claim from M5-rigid-68 is false.
`Poincare/Global/OrthogonalityFeed.lean` records the integrated Gauss pin:

```lean
Poincare.OrthogonalityFeed.chart_initialVelocity_radial_pairing_eq_t_mul_speed_sq_payload
Poincare.OrthogonalityFeed.chart_initialVelocity_radial_pairing_ne_zero_payload
```

For the radial initial-velocity variation `w = v`, the pairing is

```text
t * chartGeodesicMetric g x₀ z₀ v v
```

and is nonzero when both `t` and the initial speed square are nonzero.  Thus
the previous `∀ w` `horth` shape cannot be used honestly.

## Verified transverse replacement

Added `Poincare/Global/OrthogonalityFeed.lean` with the transverse truth:

```lean
Poincare.OrthogonalityFeed.chart_initialVelocity_integrated_transverse_gauss_payload_orthogonal
Poincare.OrthogonalityFeed.chartMetric_initialVelocity_integrated_transverse_gauss_payload_orthogonal
Poincare.OrthogonalityFeed.source_transverse_horth_on_Icc_of_payload
Poincare.OrthogonalityFeed.target_transverse_horth_on_Icc_of_payload
```

These consume the payload-discharged integrated Gauss law and convert it to the
`CovariantDerivative.chartMetric ... = 0` `horth` shape on any closed interval
contained in the open payload interval, under the real anchor-transverse
hypothesis.

Added only additive variants to `Poincare/Global/SpeedGeneric.lean`:

```lean
Poincare.SourcePackage.source_hosted_transverse_quadratic_normA_eq_speed_pinned_on_cutoff_one_Icc
Poincare.SourcePackage.source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_interval_norm_package
Poincare.TargetPackage.target_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_interval_norm_package
```

These variants leave the existing all-direction statements untouched and return
endpoint pairings only for anchor-transverse input pairs.

## Remaining blocker

I did not add a `cartanMap_isLocalIsometry` theorem.  The false all-direction
feed is replaced, but the final instantiation still needs a non-vacuous
assembly theorem combining:

1. radial-radial endpoint blocks from the speed/ray-law facts,
2. radial-transverse endpoint blocks from the integrated Gauss feed,
3. transverse-transverse endpoint blocks from the new transverse speed-generic
   variants,
4. the source/target hosted strict-derivative families from
   `TheLocalIsometry.lean` / `CartanCascade.lean`.

The existing `SpeedGeneric.cartanMap_isLocalIsometry_on_normalBall_of_common_speed_rescaled_anchor_pairings`
still consumes full all-direction endpoint pairings, so feeding it directly
would reintroduce the false radial `horth`.  The needed next bridge is a
radial/transverse-decomposed `cartanMap` consumer for the hosted speed-generic
data, not another all-direction wrapper.

## Verification

Forbidden-token scan:

```text
rg -n "\b(sorry|admit|axiom|native_decide)\b" \
  Poincare/Global/OrthogonalityFeed.lean Poincare/Global/SpeedGeneric.lean
```

returned no matches.

Whitespace check:

```text
git diff --check -- Poincare/Global/OrthogonalityFeed.lean Poincare/Global/SpeedGeneric.lean
```

passed with no output.

Required build:

```text
lake build Poincare.Global.OrthogonalityFeed Poincare.Global.SpeedGeneric
```

completed successfully:

```text
✔ [3180/3181] Built Poincare.Global.SpeedGeneric (17s)
⚠ [3181/3181] Built Poincare.Global.OrthogonalityFeed (3.1s)
Build completed successfully (3181 jobs).
```

The `OrthogonalityFeed` build emitted only unused-section-variable warnings on
two generic wrapper theorems; there were no Lean errors.
