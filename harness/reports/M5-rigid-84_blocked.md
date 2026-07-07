# M5-rigid-84 blocked: centered linearized PL package is not exported

## Status

Added `Poincare/Global/TheIsometry.lean`.  No existing Lean files were edited,
including `Poincare.lean`.

The assembly consumer is present:

```lean
Poincare.BundleDischarge.cartanMap_isLocalIsometry_of_common_oneSided_payload_transverse_feed
```

The bounded transverse-transverse feed is also present, but it is not yet
instantiable from the hosted linearized-family exports.  The first unfed
hypothesis is the centered linearized Picard-Lindelöf package demanded by
`Poincare.BoundedPackage.source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_plNorm_on_closedBall`
and, analogously, by the target feed:

```lean
(hplLinear : ∀ w w' : E3,
  IsPicardLindelof
    (fun s : ℝ => fun ψ : E3 × E3 =>
      linearizedGeodesicFlowOperator
        (chartChristoffelField g x₀) (γ s) ψ)
    (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
    ((0 : E3), T⁻¹ • (w + w')) aLin rLin LipLin KLin)
```

## Exact mismatch

The available hosted all-direction exporter consumes one zero-centered package:

```lean
(hpl : IsPicardLindelof
  (fun t : ℝ => fun ψ : E × E =>
    linearizedGeodesicFlowOperator
      (GeodesicTransport.chartChristoffelField g x₀) (γ t) ψ)
  (tmin := -ε) (tmax := ε)
  ⟨(0 : ℝ), by constructor <;> linarith⟩
  ((0 : E), (0 : E)) a r L K)
```

and exports a rescaled solution family with endpoint additivity and
homogeneity:

```lean
∃ Ψ : E → ℝ → E × E,
  (∀ w : E, Ψ w 0 = ((0 : E), T⁻¹ • w)) ∧
    (∀ w : E, ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (Ψ w) ... (Icc (-ε) ε) t) ∧
    (∀ w w' : E,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1) ∧
    ∀ (c : ℝ) (w : E),
      (Ψ (c • w) T).1 = c • (Ψ w T).1
```

This is not the same shape as the bounded feed.  The bounded feed needs a
`∀ w w'` family of `IsPicardLindelof` packages centered at
`((0 : E3), T⁻¹ • (w + w'))`, with one common tuple
`aLin rLin LipLin KLin`.  The exported theorem instead takes a single
zero-centered package at `((0 : E), (0 : E))` and does not return the centered
PL packages.

The next centered membership fields required by the same feed are likewise not
exported by the hosted family:

```lean
(hmem_add : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
  Ψ (w + w') s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
(hmem_sum : ∀ w w' : E3, ∀ s ∈ Icc tmin tmax,
  Ψ w s + Ψ w' s ∈ closedBall ((0 : E3), T⁻¹ • (w + w')) aLin)
```

`BoundedPackage.hosted_hplNorm_on_closedBall_of_center_norm_bound` solves the
separate scalar norm-system bounded-center package.  It does not supply this
linearized `E3 × E3` centered package, so it cannot feed `hplLinear`.

Consequently I did not state `cartanMap_isLocalIsometry`: doing so in
`TheIsometry.lean` would require a vacuous wrapper or an additional unproved
export.

## Verification

- `lake build Poincare.Global.TheIsometry`
  - Result: success.
  - Final lines:

```text
✔ [3193/3193] Built Poincare.Global.TheIsometry (1.6s)
Build completed successfully (3193 jobs).
```
