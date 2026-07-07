# M5-rigid-96 blocked: PL shrinks thread only after the common time

## Status

Added `Poincare/Global/SmallTCommon.lean`. No existing Lean files were edited,
including `Poincare.lean`.

The new module proves the non-vacuous packaging theorem:

- `SmallTCommon.exists_common_time_enriched_source_target_with_linearized_pl_shrinks`

It reuses `CommonTime.exists_common_time_enriched_source_target_cascade`, then
applies
`PLPackages.exists_shrunk_zero_centered_linearized_pl_package_of_baseCurvePackage`
to the source and target base packages. The theorem exports, for each small
endpoint direction `v`, the existing common `T`, source and target base
packages, and concrete zero-centered PL witnesses:

```lean
∃ εlin_source : ℝ, ∃ hεlin_source_pos : 0 < εlin_source,
  εlin_source ≤ εs ∧
    ∃ aPL r Lip K : ℝ≥0, 0 < (r : ℝ) ∧
      IsPicardLindelof
        (fun s : ℝ => fun ψ : E3 × E3 =>
          linearizedGeodesicFlowOperator
            (chartChristoffelField g x₀)
            (αs (extChartAt I3 x₀ x₀, T⁻¹ • v) s) ψ)
        (tmin := -εlin_source) (tmax := εlin_source)
        ⟨(0 : ℝ), by constructor <;> linarith [hεlin_source_pos]⟩
        ((0 : E3), (0 : E3)) aPL r Lip K
```

and the analogous target witness with `roundSphereMetric3`, `p₀`, `αt`, and
`align v`.

## First resisting witness

The requested strengthened common-time theorem needs the PL shrinks in the
time choice:

```lean
T < min (...existing terms..., εlin_source, εlin_target)
```

or equivalently the two fields:

```lean
T < εlin_source
T < εlin_target
```

The available PL export has the opposite quantifier order. It requires an
already selected base curve:

```lean
(hbase : EnrichedCascade.BaseCurvePackage g x₀ T εs as αs v) →
  ∃ εlin_source : ℝ, ∃ hεlin_source_pos : 0 < εlin_source,
    εlin_source ≤ εs ∧
      ∃ aPL r Lip K : ℝ≥0, 0 < (r : ℝ) ∧
        IsPicardLindelof ... (tmin := -εlin_source) (tmax := εlin_source) ...
```

But `hbase` is produced only after `CommonTime` has already fixed the common
`T` and after the endpoint direction `v` has been introduced:

```lean
∃ ρ > 0, ∃ T > 0, ... ∀ v : E3, ‖v‖ < ρ →
  EnrichedCascade.BaseCurvePackage g x₀ T εs as αs v ∧
  EnrichedCascade.BaseCurvePackage roundSphereMetric3 p₀ T εt aTgt αt (align v) ∧
  ...
```

Thus the concrete `εlin_source` and `εlin_target` witnesses are not available
at the point where `CommonTime.lean` chooses

```lean
let T : ℝ := min εs εt / 2
```

and the current PL theorem gives no lower bound relating the later shrink to
that already fixed `T`. This is exactly the missing input for
`IntervalAlign.exists_linearized_family_on_aligned_interval_of_uniform_flow`,
which requires `T < εlin` before it can select the family, strict derivative,
and radial ray field on the aligned interval.

Strengthening the theorem as requested would require a new export that either
produces linearized PL margins before the common-time choice, or gives a
uniform lower bound ensuring the later PL shrink is larger than the chosen
common `T`.

## Verification

- Forbidden-token scan on `Poincare/Global/SmallTCommon.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/SmallTCommon.lean`
  - Result: success.
- `lake build Poincare.Global.SmallTCommon`
  - Result: success. The build replayed pre-existing imported-module warnings;
    no warning was emitted from `Poincare/Global/SmallTCommon.lean`.
  - Final lines:

```text
✔ [3203/3203] Built Poincare.Global.SmallTCommon (2.6s)
Build completed successfully (3203 jobs).
```
