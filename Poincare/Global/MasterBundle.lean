import Poincare.Global.BundleDischarge
import Poincare.Global.CommonTime

/-!
# Master bundle boundary

This module records the M5-rigid-93 assembly boundary.  The imported chain has
the common-time enriched cascade, the bounded Gronwall transverse feeds, the
ray/speed reconciliation feed, and the final consumer
`BundleDischarge.cartanMap_isLocalIsometry_of_common_oneSided_payload_transverse_feed`.

The requested curvature-only master existence theorem is not stated here.  The
first witness that is not exported by the public common-time API is the
concrete zero-centered linearized Picard-Lindelof package needed before the
common-time theorem yields actual source and target families `PsiS` and
`PsiT`.

After unpacking
`CommonTime.exists_common_time_enriched_source_target_cascade`, the source side
is still conditional on this missing concrete witness:

```
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

The target side has the identical obstruction with `roundSphereMetric3`, `p₀`,
`αt`, and `align v`:

```
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

The exported common-time theorem currently provides only the conditional form:

```
∀ {aPL r Lip K : ℝ≥0}, 0 < (r : ℝ) →
  IsPicardLindelof ... ((0 : E3), (0 : E3)) aPL r Lip K →
    ∃ Ψ : E3 → ℝ → E3 × E3, ...
```

Without those concrete PL witnesses, the master bundle cannot even select the
common `PsiS` and `PsiT` values needed by the final consumer.  Consequently the
ray fields are also unreachable from the current exports:

```
hSourceRay : (PsiS v T).1 = T • Vs
hTargetRay : (PsiT (align v) T).1 = T • Vt
```

Assuming any of these fields here would merely restate the missing hosted
bundle in another notation, so this module remains theorem-free.
-/

noncomputable section

namespace Poincare
namespace MasterBundle

end MasterBundle
end Poincare
