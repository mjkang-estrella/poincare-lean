import Poincare.Global.RiemannianContext
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Poincare.CompactCoefficientEllipticity

abbrev E := ClosedSmoothModel 3
abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ

/-- A continuous positive family has a single positive quadratic lower bound. -/
theorem exists_uniform_coercivity {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : K → Bilin) (hA : Continuous A) (hpos : ∀ x v, v ≠ 0 → 0 < A x v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ x v, c * ‖v‖ ^ 2 ≤ A x v v := by
  have hcompact : IsCompact ((Set.univ : Set K) ×ˢ Metric.sphere (0 : E) 1) :=
    isCompact_univ.prod (isCompact_sphere (0 : E) 1)
  have hcont : Continuous (fun p : K × E => A p.1 p.2 p.2) :=
    ((hA.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  obtain ⟨c, hc, hbound⟩ := hcompact.exists_forall_le' hcont.continuousOn
    (a := (0 : ℝ)) (by
      intro p hp
      apply hpos p.1 p.2
      have hn : ‖p.2‖ = 1 := by simpa using hp.2
      intro hz
      simp [hz] at hn)
  refine ⟨c, hc, ?_⟩
  intro x v
  by_cases hv : v = 0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hu : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := norm_smul_inv_norm hv
  have hb := hbound (x, (‖v‖⁻¹ : ℝ) • v) ⟨Set.mem_univ x, by simpa using hu⟩
  have hscale : (A x ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v)) * ‖v‖ ^ 2 =
      A x v v := by
    simp only [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    field_simp
  calc
    c * ‖v‖ ^ 2 ≤ A x ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hb (sq_nonneg ‖v‖)
    _ = A x v v := hscale

end Poincare.CompactCoefficientEllipticity
