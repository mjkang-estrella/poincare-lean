import Poincare.Global.BufferedTensorGraphTransportDefinitions

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.BufferedTensorGraphTransport
open FiniteAtlasParabolicTensorSpace
universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- The gate and destination partition keep the coefficient on its genuine destination support. -/
theorem weight_zero_off_coordSupport (A : AtlasData M) (i : Fin A.cover.chartCount)
    (θ ξ : ClosedSmoothModel 3 → ℝ) (F : ClosedSmoothModel 3 → ClosedSmoothModel 3)
    (a b c d : Fin 3)
    (hθ : tsupport θ ⊆ (chart A i).target)
    (z : ClosedSmoothModel 3) (hz : z ∉ coordSupport A i) :
    weight A i θ ξ F a b c d z = 0 := by
  by_cases hzero : θ z = 0
  · simp [weight, hzero]
  · have ht : z ∈ (chart A i).target := hθ (subset_tsupport θ hzero)
    have hp : A.partition i ((chart A i).symm z) = 0 := by
      by_contra hp
      apply hz
      exact ⟨(chart A i).symm z, subset_tsupport (A.partition i) hp,
        (chart A i).right_inv ht⟩
    simp [weight, hp]

/-- Gated ambient pullback recovers the actual chart tensor coefficient, with destination weight only. -/
theorem weight_pullback_chart (A : AtlasData M) (i : Fin A.cover.chartCount)
    (θ ξ : ClosedSmoothModel 3 → ℝ) (F : ClosedSmoothModel 3 → ClosedSmoothModel 3)
    (a b c d : Fin 3) (j : Fin A.cover.chartCount)
    (hθ : tsupport θ ⊆ ((chart A i).symm.trans (chart A j)).source)
    (hF : ∀ z ∈ tsupport θ, ∀ᶠ y in 𝓝 z, F y = change A i j y)
    (hone : ∀ z ∈ (chart A i) ''
      (tsupport (A.partition i) ∩ (chart A j).symm '' tsupport ξ), θ z = 1)
    (f : ClosedSmoothModel 3 → ℝ) (x : M) (hi : x ∈ (chart A i).source) :
    weight A i θ ξ F a b c d (chart A i x) * f (F (chart A i x)) =
      A.partition i x * (@ite ℝ (x ∈ (chart A j).source) (Classical.propDecidable _)
        (ξ (chart A j x) * jac A i j x a c * jac A i j x b d * f (chart A j x)) 0) := by
  classical
  have hK (hj : x ∈ (chart A j).source)
      (hp : A.partition i x ≠ 0) (hξ : ξ (chart A j x) ≠ 0) :
      chart A i x ∈ (chart A i) ''
        (tsupport (A.partition i) ∩ (chart A j).symm '' tsupport ξ) := by
    refine ⟨x, ⟨subset_tsupport (A.partition i) hp, ?_⟩, rfl⟩
    exact ⟨chart A j x, subset_tsupport ξ hξ, (chart A j).left_inv hj⟩
  by_cases ht : θ (chart A i x) = 0
  · by_cases hj : x ∈ (chart A j).source
    · by_cases hp : A.partition i x = 0
      · simp [weight, ht, hp]
      · have hξ : ξ (chart A j x) = 0 := by
          by_contra hξ
          have h := hone _ (hK hj hp hξ)
          simp [ht] at h
        simp [weight, ht, hj, hξ]
    · simp [weight, ht, hj]
  · have hts : chart A i x ∈ tsupport θ := subset_tsupport θ ht
    have hsource := hθ hts
    have hj : x ∈ (chart A j).source := by
      have hj' : (chart A i).symm (chart A i x) ∈ (chart A j).source := hsource.2
      rwa [(chart A i).left_inv hi] at hj'
    have hg : F =ᶠ[𝓝 (chart A i x)] change A i j := hF _ hts
    have hf : F (chart A i x) = chart A j x := by
      exact hg.eq_of_nhds.trans (change_chart A i j x hi)
    have hdf : fderiv ℝ F (chart A i x) = fderiv ℝ (change A i j) (chart A i x) :=
      hg.fderiv_eq
    by_cases hp : A.partition i x = 0
    · simp [weight, (chart A i).left_inv hi, hp]
    · by_cases hξ : ξ (chart A j x) = 0
      · simp [weight, hf, hξ, hj]
      · have htone := hone _ (hK hj hp hξ)
        simp only [weight, htone, one_mul, (chart A i).left_inv hi, hf, hdf,
          if_pos hj, jac]
        ring

end Poincare.BufferedTensorGraphTransport
