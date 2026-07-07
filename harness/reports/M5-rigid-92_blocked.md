# M5-rigid-92 blocked: common enriched time exported; final consumer still lacks a concrete hosted bundle

## Status

Added `Poincare/Global/CommonTime.lean`.  No existing Lean files were edited,
including `Poincare.lean`.

The new module proves the common-time re-export requested for the enriched
cascade:

- `CommonTime.targetAnchorChartMetric_inv_smul_align_eq_source`
- `CommonTime.target_anchorSpeed_of_source_anchorSpeed`
- `CommonTime.exists_shrunk_cutoff_one_strictDeriv_package_for_smaller_time`
- `CommonTime.exists_common_time_enriched_source_target_cascade`

The important exported shape now has one hosted scalar `T` on both sides:

```lean
EnrichedCascade.BaseCurvePackage g x₀ T εs as αs v
EnrichedCascade.BaseCurvePackage roundSphereMetric3 p₀ T εt aTgt αt (align v)
```

The construction does not assume `‖align v‖ = ‖v‖`.  The smallness of
`align v` is obtained by the operator-norm bound for the continuous linear
equivalence, and the common-speed identity is the anchor-metric identity

```lean
CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • align v) (T⁻¹ • align v) =
  CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • v) (T⁻¹ • v)
```

from `CartanMap.TangentAlignment.map_app`.

## Remaining blocker

The original `Ts`/`Tt` mismatch is removed by the new common theorem, but the
curvature-only `BundleDischarge.cartanMap_isLocalIsometry_of_common_oneSided_payload_transverse_feed`
still cannot be instantiated from the public exports without assuming a
concrete hosted bundle.

The common theorem still exports the source and target linearized families
conditionally:

```lean
∀ {aPL r Lip K : ℝ≥0}, 0 < (r : ℝ) →
  IsPicardLindelof ... →
    ∃ Ψ : E → ℝ → E × E, ...
```

The final consumer, however, needs concrete families and their endpoint/ray and
block fields at the same `T`, for example:

```lean
(hSourceRay : (PsiS v T).1 = T • Vs)
(hTargetRay : (PsiT (L v) T).1 = T • Vt)
```

and the transverse blocks:

```lean
(hSourceTransverseTransverse : ...)
(hTargetTransverseTransverse : ...)
```

`AssemblyDone` supplies the transverse-block theorem once bounded norm-system
PL data, radius bounds, and initial norm identities are supplied, but those
data are not packaged by the current public common-time theorem.  Stating the
curvature-only local-isometry theorem here would therefore still amount to
assuming the unfed hosted PL/ray/norm bundle in different notation.

## Verification

- `lake build Poincare.Global.CommonTime`
  - Result: success.
  - Final lines:

```text
✔ [3200/3200] Built Poincare.Global.CommonTime (3.0s)
Build completed successfully (3200 jobs).
```

- `rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/CommonTime.lean`
  - Result: no matches.
