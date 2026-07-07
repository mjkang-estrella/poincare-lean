# M5-rigid-95 blocked: aligned selector exported, common `T < εlin` still missing

## Status

Added `Poincare/Global/IntervalAlign.lean`. No existing Lean files were edited,
including `Poincare.lean`.

The new module proves the non-vacuous interval-alignment bridge that was missing
after `M5-rigid-94`:

- `IntervalAlign.baseCurvePackage_restrict_interval`
  restricts an `EnrichedCascade.BaseCurvePackage` from `[-ε, ε]` to any smaller
  `[-ε', ε']`.
- `IntervalAlign.linearizedFamilyPackage_restrict_interval`
  restricts an `EnrichedCascade.LinearizedFamilyPackage` in the same way.
- `IntervalAlign.exists_linearized_family_on_aligned_interval_of_uniform_flow`
  consumes a zero-centered PL package already on the aligned interval
  `[-ε, ε]` with `T < ε`, threads the hosted flow facts
  `δ, hα0, hαder, hαmem, hαtarget, hexp`, and exports:
  - the selected all-direction family `Ψ`,
  - endpoint additivity and homogeneity at `T`,
  - `EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α v Ψ`,
  - the strict derivative
    `HasStrictFDerivAt (expAtChartOpenPartialHomeomorph (g := g) x₀)
      (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul) v`,
  - the radial ray field
    `(Ψ v T).1 = T • (α (extChartAt I3 x₀ x₀, T⁻¹ • v) T).2`.

This discharges the local mismatch once an aligned interval satisfying
`T < εlin` is available.

## First resisting witness

The remaining obstruction is the actual common-time choice of `T` relative to
the PL shrink. Existing exports still produce the PL shrink only after the
fixed common-time base curve has already been selected.

`CommonTime.exists_common_time_enriched_source_target_cascade` exports one fixed
common `T`, original margins `εs`, `εt`, and base packages on the original
intervals. Then `PLPackages.exists_shrunk_zero_centered_linearized_pl_package_of_baseCurvePackage`
can produce, for each selected base curve, a smaller interval:

```lean
∃ εlin : ℝ, ∃ hεlin_pos : 0 < εlin, εlin ≤ εs ∧
  ∃ aPL r Lip K : ℝ≥0, 0 < (r : ℝ) ∧
    IsPicardLindelof
      (fun s : ℝ => fun ψ : E3 × E3 =>
        linearizedGeodesicFlowOperator
          (chartChristoffelField g x₀)
          (αs (extChartAt I3 x₀ x₀, T⁻¹ • v) s) ψ)
      (tmin := -εlin) (tmax := εlin)
      ⟨(0 : ℝ), by constructor <;> linarith [hεlin_pos]⟩
      ((0 : E3), (0 : E3)) aPL r Lip K
```

But the aligned selector in `IntervalAlign` needs the missing relation:

```lean
T < εlin
```

for both the source and target PL intervals. There is currently no public
theorem strengthening the PL export to:

```lean
∀ v : E3, ‖v‖ < ρ →
  ∃ εlin : ℝ, ∃ hεlin_pos : 0 < εlin,
    εlin ≤ εs ∧ T < εlin ∧
      ∃ aPL r Lip K : ℝ≥0, 0 < (r : ℝ) ∧
        IsPicardLindelof ... (tmin := -εlin) (tmax := εlin) ...
```

nor a replayed common-time theorem that first obtains source and target PL
linearized bounds, then chooses the common `T` below both resulting shrunk
linearized intervals.

Without that `T < εlin_source` and `T < εlin_target` export, the final
`RayIdentification` and `BundleDischarge` consumers cannot be instantiated
from the current public theorem chain without assuming the missing alignment.

## Verification

- Forbidden-token scan on `Poincare/Global/IntervalAlign.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/IntervalAlign.lean`
  - Result: success.
- `lake build Poincare.Global.IntervalAlign`
  - Result: success. The build replayed pre-existing imported-module warnings.
  - Final lines:

```text
✔ [3202/3202] Built Poincare.Global.IntervalAlign (2.7s)
Build completed successfully (3202 jobs).
```
