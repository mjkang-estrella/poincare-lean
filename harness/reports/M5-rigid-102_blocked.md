# M5-rigid-102 blocked: scalar is false; corrected two-sided cancellation verified

## Scalar pin outcome

The scalar required by `PullbackFeed`

```lean
JacobiNormSystem.speedPinnedScale speed T * (T⁻¹ * T⁻¹) = 1
```

is false as a general identity.  The new module proves the concrete pin:

```lean
Poincare.ScalarPin.speedPinnedScale_inv_sq_ne_one_at_one_pi :
  JacobiNormSystem.speedPinnedScale 1 Real.pi *
      (Real.pi⁻¹ * Real.pi⁻¹) ≠ 1
```

At `speed = 1` and `T = π`, the sine factor is zero, so the left side is not
`1`.

## Verified progress

Added `Poincare/Global/ScalarPin.lean`.  No existing Lean files were edited,
including `Poincare.lean`.

The file records the true scalar relation:

```lean
Poincare.ScalarPin.speedPinnedScale_inv_sq_eq_normalized_sin_sq
```

which states that

```lean
JacobiNormSystem.speedPinnedScale speed T * (T⁻¹ * T⁻¹)
  = Real.sin (SourcePackage.normalizedRescaledAngle (speed * T)) ^ 2
```

for `speed ≠ 0` and `T ≠ 0`.

It also adds the corrected two-sided endpoint pairing adapter:

```lean
Poincare.ScalarPin.hosted_endpoint_pairing_feed_of_two_sided_speed_pin
```

This is the `EqualityChain`-style cancellation: source and target both carry
the same normalized sine-square factor, and that common factor cancels across
the source-target pairing comparison.  It does not try to cancel the
transverse sine scale against `T⁻²` alone.

For the transverse-block side conditions, the file adds source and target
bounded-center adapters:

```lean
Poincare.ScalarPin.source_transverseTransverse_of_enriched_gronwall_feed_of_center_norm_bound
Poincare.ScalarPin.target_transverseTransverse_of_enriched_gronwall_feed_of_center_norm_bound
```

These adapters remove raw `hplNorm` by constructing it via
`BoundedPackage.hosted_hplNorm_on_closedBall_of_center_norm_bound`, then feed
`AssemblyDone.source_transverseTransverse_of_enriched_gronwall_feed` and the
target analogue.

## Remaining blocker

The final `cartanMap_isLocalIsometry` wrapper is not stated.  Two nontrivial
items remain outside the public selector datum.

First, the selector still does not export the quantitative norm-system side
conditions needed by the bounded transverse adapters.  After threading
`hplNorm` through `BoundedPackage`, the remaining source-side fields are still
the following shapes, with target analogues:

```lean
hcenter :
  ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
    ‖(((0 : ℝ), (0 : ℝ),
      chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
        (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ + (radius : ℝ) ≤ (B : ℝ)

hbound : ‖Aop‖ * (B : ℝ) ≤ (LNorm : ℝ)

hmulT : (LNorm : ℝ) * T ≤ (radius : ℝ) - (rNorm : ℝ)

hqBound :
  ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
    CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
      |chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
        (T⁻¹ • w) (T⁻¹ • w)| ≤ qmax

hgronwallRadius :
  qmax * Real.exp (C * T) + qmax ≤ (radius : ℝ)

hpinnedRadius :
  ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
    CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
      (MembershipBound.speedPinnedMembershipRadius speed
        (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) : ℝ) ≤ (radius : ℝ)
```

The initial norm identities are also still required verbatim:

```lean
ha0 : ∀ w : E3, JacobiNormSystem.normA ... 0 = 0
hb0 : ∀ w : E3, JacobiNormSystem.normB ... 0 = 0
hc0 : ∀ w : E3, JacobiNormSystem.normC ... 0 =
  chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀) (T⁻¹ • w) (T⁻¹ • w)
```

Second, because the exact unit scalar is false, the corrected route gives
source and target pullbacks with a shared sine-square factor.  The available
final `EqualityChain` consumer still requires endpoint equivalences:

```lean
{A B : E3 ≃L[ℝ] E3}
(hA : (A : E3 →L[ℝ] E3) =
  linearizedEndpointCLM (Ψ := Ψs) Ts hadds hsmuls)
(hB : (B : E3 →L[ℝ] E3) =
  linearizedEndpointCLM (Ψ := Ψt) Tt haddt hsmult)
```

`PairingUpgrade` constructs these from exact unscaled anchor pullbacks.  The
new scalar pin shows that exact unscaled transverse pullback is not the true
identity.  A nonzero shared-scale positive-definite upgrade, or equivalent
selector-exported endpoint equivalences compatible with the sine-square
pullbacks, is still needed.

## Verification

- `lake build Poincare.Global.ScalarPin`
  - Result: success.
  - Final lines:

```text
✔ [3200/3200] Built Poincare.Global.ScalarPin (2.0s)
Build completed successfully (3200 jobs).
```

