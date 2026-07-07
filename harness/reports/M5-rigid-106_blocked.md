# M5-rigid-106 blocked: selector-level transverse export verified, bounded norm-system radii still external

## Outcome

Added `Poincare/Global/TransverseExport.lean`.  No existing Lean files were
edited, including `Poincare.lean`.

The new module verifies the transverse package at the
`UniformFlowExport` selector datum as far as the currently exported bounded
norm-system data permits.  It proves the initial norm-state identities directly
from the enriched selector packages, restricts the base package to the same
linearized interval returned by the rigid-98 selector, and threads the selector
families through the bounded `ScalarPin` adapters.

## Verified payload

Initial identities discharged from the enriched packages:

```lean
Poincare.TransverseExport.normA_initial_eq_zero_of_enriched_packages
Poincare.TransverseExport.normB_initial_eq_zero_of_enriched_packages
Poincare.TransverseExport.normC_initial_eq_anchor_of_enriched_packages
```

Source and target transverse block adapters at an enriched selector datum:

```lean
Poincare.TransverseExport.source_transverseTransverse_of_selector_bounded_data
Poincare.TransverseExport.target_transverseTransverse_of_selector_bounded_data
```

Common source/target selector export:

```lean
Poincare.TransverseExport.exists_common_time_with_selector_transverse_block_exports
```

This unpacks:

```lean
UniformFlowExport.exists_common_time_with_uniform_flow_exports_and_enriched_selectors
```

and exports the selected `Ψs`/`Ψt`, additivity, homogeneity, strict derivative,
ray identity, and base/linearized packages.  The proof explicitly aligns the
intervals by restricting the base package from the wider base interval to the
linearized selector interval before feeding the transverse adapters.

## Remaining blocker

The initial identities are no longer a blocker.  The resisting interface is the
quantitative bounded norm-system package itself.  The selector-level theorem
can now turn the following source data, and the target analogue, into the exact
transverse block identity consumed by `BlockDiagonal`:

```lean
hcenter :
  ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
    ‖(((0 : ℝ), (0 : ℝ),
      chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
        (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ + (radius : ℝ) ≤ (B : ℝ)

hbound : ‖Aop‖ * (B : ℝ) ≤ (LNorm : ℝ)

hmulT : (LNorm : ℝ) * T ≤ (radius : ℝ) - (rNorm : ℝ)

hAop :
  ∀ x : Triple,
    Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1,
      -2 * speed ^ 2 * x.2.1)

hC : 0 ≤ C
hAopNorm : ‖Aop‖ ≤ C

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

So the transverse export is verified as a selector-level continuation from
bounded norm-system data, but a curvature-only `cartanMap_isLocalIsometry`
wrapper still cannot be stated without also exporting or constructing this
bounded norm-system radius tuple at the selector time.

## Verification

- `rg -n '\b(sorry|admit|axiom|native_decide)\b' Poincare/Global/TransverseExport.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/TransverseExport.lean`
  - Result: success.
- `lake build Poincare.Global.TransverseExport`
  - Result: success.  The build replayed pre-existing imported-module warnings;
    no failure was emitted from `Poincare/Global/TransverseExport.lean`.
  - Final lines:

```text
✔ [3208/3208] Built Poincare.Global.TransverseExport (9.4s)
Build completed successfully (3208 jobs).
```
