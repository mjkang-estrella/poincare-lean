import Poincare.Global.BufferedUnweightedGraphTransportDefinitions

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.BufferedUnweightedGraphTransport
open FiniteAtlasParabolicTensorSpace
universe u

/-- A source buffer vanishes outside its transported support on the true chart source. -/
private theorem source_buffer_zero_off_carrier
    {M : Type u} [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (A : AtlasData M) (i j : Fin A.cover.chartCount)
    (ξ : ClosedSmoothModel 3 → ℝ) (y : ClosedSmoothModel 3)
    (hy : (chart A i).symm y ∉ (chart A j).symm '' tsupport ξ)
    (hsource : (chart A i).symm y ∈ (chart A j).source) :
    ξ (change A i j y) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hξ
  apply hy
  refine ⟨change A i j y, hξ, ?_⟩
  exact (chart A j).left_inv hsource

/-- Original buffered chart gates recover the genuine tensor transport as a germ
on the destination partition support, for arbitrary source coefficients. -/
theorem weighted_source_germ
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (A : AtlasData M) (i j : Fin A.cover.chartCount)
    (θ ψ ξ : ClosedSmoothModel 3 → ℝ)
    (F : ClosedSmoothModel 3 → ClosedSmoothModel 3) (c d : Fin 3)
    (hcompact : HasCompactSupport ξ)
    (htarget : tsupport ξ ⊆ (chart A j).target)
    (hθ : tsupport θ ⊆ ((chart A i).symm.trans (chart A j)).source)
    (hF : ∀ v ∈ tsupport θ, ∀ᶠ y in nhds v, F y = change A i j y)
    (hone : ∀ v ∈ (chart A i) ''
      (tsupport (A.partition i) ∩ (chart A j).symm '' tsupport ξ),
      ∀ᶠ y in nhds v, θ y = 1)
    (f : (Fin 3 × Fin 3) → ClosedSmoothModel 3 → ℝ)
    (z : ClosedSmoothModel 3) (hz : z ∈ coordSupport A i)
    (hψ : ∀ᶠ y in nhds z, ψ y = 1) :
    ∀ᶠ y in nhds z,
      (∑ a : Fin 3, ∑ b : Fin 3, weight θ ψ ξ F a b c d y * f (a,b) (F y)) =
        (@ite ℝ ((chart A i).symm y ∈ (chart A j).source)
          (Classical.propDecidable _)
          (ξ (change A i j y) * ∑ a : Fin 3, ∑ b : Fin 3,
            (fderiv ℝ (change A i j) y ((EuclideanSpace.basisFun (Fin 3) ℝ) c)) a *
            (fderiv ℝ (change A i j) y ((EuclideanSpace.basisFun (Fin 3) ℝ) d)) b *
            f (a,b) (change A i j y)) 0) := by
  classical
  let K : Set M := (chart A j).symm '' tsupport ξ
  have hKcompact : IsCompact K :=
    hcompact.image_of_continuousOn
      ((continuousOn_extChartAt_symm (A.cover.anchor j)).mono htarget)
  have hKsource : K ⊆ (chart A j).source := by
    rintro x ⟨v, hv, rfl⟩
    exact (chart A j).map_target (htarget hv)
  have hzTarget : z ∈ (chart A i).target := coordSupport_subset_target A i hz
  have hcontinuous : ContinuousAt (chart A i).symm z :=
    continuousAt_extChartAt_symm'' hzTarget
  by_cases hzK : (chart A i).symm z ∈ K
  · obtain ⟨x, hx, hcx⟩ := hz
    have hxi : x ∈ (chart A i).source := partition_support_source A i hx
    have hinverse : (chart A i).symm z = x := by
      rw [← hcx]
      exact (chart A i).left_inv hxi
    have hzGate : z ∈ (chart A i) ''
        (tsupport (A.partition i) ∩ (chart A j).symm '' tsupport ξ) :=
      ⟨x, ⟨hx, by simpa only [hinverse] using hzK⟩, hcx⟩
    have hθgerm := hone z hzGate
    have hθz : θ z = 1 := Filter.EventuallyEq.eq_of_nhds hθgerm
    have hzθ : z ∈ tsupport θ :=
      subset_tsupport θ (by simpa only [Function.mem_support, hθz] using
        (one_ne_zero : (1 : ℝ) ≠ 0))
    have hFgerm : F =ᶠ[nhds z] change A i j := hF z hzθ
    have hDFgerm : fderiv ℝ F =ᶠ[nhds z] fderiv ℝ (change A i j) := hFgerm.fderiv
    have hsource : ∀ᶠ y in nhds z, (chart A i).symm y ∈ (chart A j).source :=
      hcontinuous.eventually_mem
        ((isOpen_extChartAt_source (A.cover.anchor j)).mem_nhds (hKsource hzK))
    filter_upwards [hθgerm, hψ, hFgerm, hDFgerm, hsource]
      with y hyθ hyψ hyF hyD hySource
    simp only [weight, hyθ, hyψ, one_mul, hyF, hyD, if_pos hySource]
    simp only [Finset.mul_sum, mul_assoc]
  · have hoff : ∀ᶠ y in nhds z, (chart A i).symm y ∉ K :=
      hcontinuous.eventually_mem (hKcompact.isClosed.isOpen_compl.mem_nhds hzK)
    filter_upwards [hoff] with y hy
    have hξzero (hs : (chart A i).symm y ∈ (chart A j).source) :
        ξ (change A i j y) = 0 :=
      source_buffer_zero_off_carrier A i j ξ y hy hs
    have hleft : (∑ a : Fin 3, ∑ b : Fin 3,
        weight θ ψ ξ F a b c d y * f (a,b) (F y)) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b _
      by_cases hyθ : θ y = 0
      · simp [weight, hyθ]
      · have hySupport : y ∈ tsupport θ := subset_tsupport θ hyθ
        have hySource : (chart A i).symm y ∈ (chart A j).source := (hθ hySupport).2
        have hyF : F y = change A i j y :=
          Filter.EventuallyEq.eq_of_nhds (hF y hySupport)
        simp [weight, hyF, hξzero hySource]
    rw [hleft]
    by_cases hySource : (chart A i).symm y ∈ (chart A j).source
    · simp [hySource, hξzero hySource]
    · simp [hySource]

end Poincare.BufferedUnweightedGraphTransport
