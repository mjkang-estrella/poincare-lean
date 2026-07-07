# M5-rigid-91 blocked: Gronwall membership feeds the transverse blocks, final common-time bundle still missing

## Status

Added `Poincare/Global/AssemblyDone.lean`.  No existing Lean files were edited,
including `Poincare.lean`.

The new module feeds the non-circular Gronwall membership into the bounded
solution-feed shape actually used by the transverse polarization step:

- `AssemblyDone.source_hosted_transverse_quadratic_normA_eq_speed_pinned_of_bounded_membership`
- `AssemblyDone.source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_bounded_membership`
- `AssemblyDone.source_transverseTransverse_of_solutions_bounded_membership`
- `AssemblyDone.source_transverseTransverse_of_enriched_gronwall_feed`
- `AssemblyDone.target_transverseTransverse_of_enriched_gronwall_feed`

The source and target enriched theorems construct the actual `hmem` field from
`GronwallMembership.normState_mem_closedBall_qcenter_of_radius_ge`, using the
bounded `q` handoff plus the explicit pinned membership bound.

## Remaining blocker

The final curvature-only `cartanMap_isLocalIsometry` theorem is still not
stated.  The membership field is no longer the blocker.  The first remaining
assembly mismatch is the common-time requirement of
`BundleDischarge.cartanMap_isLocalIsometry_of_common_oneSided_payload_transverse_feed`.

That consumer has one shared time:

```lean
{PsiS PsiT : E3 → ℝ → E3 × E3}
{alphaS alphaT : E3 × E3 → ℝ → E3 × E3}
{speed T : ℝ} (hTpos : 0 < T)
```

and, for example, the target base field must be at that same `T`:

```lean
(hTargetBase : ∀ tau ∈ Icc (0 : ℝ) T,
  HasDerivWithinAt (alphaT (extChartAt I3 p0 p0, T⁻¹ • L v))
    (geodesicFlowField
      (GeodesicTransport.chartChristoffelField roundSphereMetric3 p0)
      (alphaT (extChartAt I3 p0 p0, T⁻¹ • L v) tau))
    (Icc (0 : ℝ) T) tau)
```

The current enriched common cascade exports separate source and target hosted
times:

```lean
BaseCurvePackage g x₀ Ts εs as αs v
BaseCurvePackage roundSphereMetric3 p₀ Tt εt aTgt αt (align v)
```

with no exported equality `Ts = Tt` and no retiming package that converts the
target fields to `Ts` or the source fields to `Tt`.  The same common-time
mismatch affects the target ray, speed, and target transverse block fields.

## Verification

- `lake build Poincare.Global.AssemblyDone`
  - Result: success.
  - Final lines:

```text
✔ [3199/3199] Built Poincare.Global.AssemblyDone (3.0s)
Build completed successfully (3199 jobs).
```

- `rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/AssemblyDone.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/AssemblyDone.lean`
  - Result: success.
