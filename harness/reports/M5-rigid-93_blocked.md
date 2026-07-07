# M5-rigid-93 blocked: common time is available, but the concrete hosted PL witness is not exported

## Status

Added `Poincare/Global/MasterBundle.lean`.  No existing Lean files were edited,
including `Poincare.lean`.

The new module imports the current final chain:

- `CommonTime.exists_common_time_enriched_source_target_cascade`
- `AssemblyDone.source_transverseTransverse_of_enriched_gronwall_feed`
- `AssemblyDone.target_transverseTransverse_of_enriched_gronwall_feed`
- `BundleDischarge.cartanMap_isLocalIsometry_of_common_oneSided_payload_transverse_feed`

No curvature-only theorem is stated.  Stating one from the current public
exports would require assuming the missing hosted bundle in different notation.

## First resisting witness

After unpacking
`CommonTime.exists_common_time_enriched_source_target_cascade`, the source and
target base packages are at one shared `T`, but the actual linearized families
`PsiS` and `PsiT` are still behind conditional Picard-Lindelöf premises.

The first concrete source witness that is not exported is:

```lean
∃ aPL r Lip K : ℝ≥0, 0 < (r : ℝ) ∧
  IsPicardLindelof
    (fun s : ℝ => fun ψ : E3 × E3 =>
      linearizedGeodesicFlowOperator
        (chartChristoffelField g x₀)
        (αs (extChartAt I3 x₀ x₀, T⁻¹ • v) s) ψ)
    (tmin := -εs) (tmax := εs)
    ⟨(0 : ℝ), by constructor <;> linarith [hεs_pos]⟩
    ((0 : E3), (0 : E3)) aPL r Lip K
```

The target side has the same missing witness with `roundSphereMetric3`, `p₀`,
`αt`, and `align v`:

```lean
∃ aPL r Lip K : ℝ≥0, 0 < (r : ℝ) ∧
  IsPicardLindelof
    (fun s : ℝ => fun ψ : E3 × E3 =>
      linearizedGeodesicFlowOperator
        (chartChristoffelField roundSphereMetric3 p₀)
        (αt (extChartAt I3 p₀ p₀, T⁻¹ • align v) s) ψ)
    (tmin := -εt) (tmax := εt)
    ⟨(0 : ℝ), by constructor <;> linarith [hεt_pos]⟩
    ((0 : E3), (0 : E3)) aPL r Lip K
```

The available common-time theorem only exports:

```lean
∀ {aPL r Lip K : ℝ≥0}, 0 < (r : ℝ) →
  IsPicardLindelof ... ((0 : E3), (0 : E3)) aPL r Lip K →
    ∃ Ψ : E3 → ℝ → E3 × E3, ...
```

Without concrete instances of these PL packages, the master bundle cannot
select the common-time `PsiS` and `PsiT`.  Therefore the downstream ray fields
are also unreachable:

```lean
hSourceRay : (PsiS v T).1 = T • Vs
hTargetRay : (PsiT (align v) T).1 = T • Vt
```

## Verification

- `rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/MasterBundle.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/MasterBundle.lean`
  - Result: success.
- `lake build Poincare.Global.MasterBundle`
  - Result: success.  The build replayed pre-existing imported-module warnings.
  - Final lines:

```text
✔ [3201/3201] Built Poincare.Global.MasterBundle (1.6s)
Build completed successfully (3201 jobs).
```
