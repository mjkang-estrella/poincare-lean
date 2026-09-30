import Poincare.Global.CompactBufferedChartOverlap
import Poincare.Global.SmoothCutoffVectorExtension
import Poincare.Global.BufferedFrozenParabolicSolver

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.BufferedChartTransitionExtensions

open FiniteAtlasParabolicTensorSpace

universe u

/-- Actual coordinate changes have smooth compact extensions agreeing near every gate support. -/
theorem exists_gated_chart_extensions
    {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (A : AtlasData M) (ξ : Fin A.cover.chartCount → ClosedSmoothModel 3 → ℝ)
    (hcompact : ∀ k, HasCompactSupport (ξ k))
    (htarget : ∀ k, tsupport (ξ k) ⊆ (chart A k).target)
    (houter : ∀ k, ∀ z ∈ tsupport (ξ k),
      ∀ᶠ y in 𝓝 z, GeodesicTransport.cutoff (n := 3) (A.cover.anchor k) y = 1)
    (hpartition : ∀ k, ∀ z ∈ coordSupport A k,
      ∀ᶠ y in 𝓝 z, GeodesicTransport.cutoff (n := 3) (A.cover.anchor k) y = 1) :
    ∃ θ : Fin A.cover.chartCount → Fin A.cover.chartCount → ClosedSmoothModel 3 → ℝ,
    ∃ F : Fin A.cover.chartCount → Fin A.cover.chartCount →
      ClosedSmoothModel 3 → ClosedSmoothModel 3,
    ∀ i j,
      let K := (chart A i) ''
        (tsupport (A.partition i) ∩ (chart A j).symm '' tsupport (ξ j))
      let O := ((chart A i).symm.trans (chart A j)).source ∩
        (fun z : ClosedSmoothModel 3 =>
          ∀ᶠ y in 𝓝 z, GeodesicTransport.cutoff (n := 3) (A.cover.anchor i) y = 1) ∩
        (change A i j) ⁻¹' (fun z : ClosedSmoothModel 3 =>
          ∀ᶠ y in 𝓝 z, GeodesicTransport.cutoff (n := 3) (A.cover.anchor j) y = 1)
      ContDiff ℝ ∞ (θ i j) ∧ HasCompactSupport (θ i j) ∧
      (∀ z, θ i j z ∈ Icc 0 1) ∧ tsupport (θ i j) ⊆ O ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 z, θ i j y = 1) ∧
      ContDiff ℝ ∞ (F i j) ∧ HasCompactSupport (F i j) ∧
      (∀ z ∈ tsupport (θ i j), ∀ᶠ y in 𝓝 z, F i j y = change A i j y) ∧
      ∃ L : NNReal, LipschitzWith L (F i j) := by
  classical
  let K (i j : Fin A.cover.chartCount) : Set (ClosedSmoothModel 3) :=
    (chart A i) '' (tsupport (A.partition i) ∩ (chart A j).symm '' tsupport (ξ j))
  let O (i j : Fin A.cover.chartCount) : Set (ClosedSmoothModel 3) :=
    ((chart A i).symm.trans (chart A j)).source ∩
      {z | ∀ᶠ y in 𝓝 z, GeodesicTransport.cutoff (n := 3) (A.cover.anchor i) y = 1} ∩
      (change A i j) ⁻¹'
      {z | ∀ᶠ y in 𝓝 z, GeodesicTransport.cutoff (n := 3) (A.cover.anchor j) y = 1}
  have hshape (i j : Fin A.cover.chartCount) :
      IsCompact (K i j) ∧ IsOpen (O i j) ∧ K i j ⊆ O i j :=
    CompactBufferedChartOverlap.isCompact_subset_good_overlap
      A ξ hcompact htarget houter hpartition i j
  have hsingle (i j : Fin A.cover.chartCount) :
      ∃ θ : ClosedSmoothModel 3 → ℝ,
      ∃ F : ClosedSmoothModel 3 → ClosedSmoothModel 3,
        ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
        (∀ z, θ z ∈ Icc 0 1) ∧ tsupport θ ⊆ O i j ∧
        (∀ z ∈ K i j, ∀ᶠ y in 𝓝 z, θ y = 1) ∧
        ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
        (∀ z ∈ tsupport θ, ∀ᶠ y in 𝓝 z, F y = change A i j y) ∧
        ∃ L : NNReal, LipschitzWith L F := by
    obtain ⟨hK, hO, hKO⟩ := hshape i j
    obtain ⟨θ, hθ, hcθ, hθO, hθK, hθ01⟩ :=
      BufferedFrozenParabolicSolver.exists_buffered_cutoff hK hO hKO
    obtain ⟨η, hη, hcη, hηO, hηθ, _⟩ :=
      BufferedFrozenParabolicSolver.exists_buffered_cutoff hcθ hO hθO
    have hchange : ContDiffOn ℝ ∞ (change A i j)
        ((chart A i).symm.trans (chart A j)).source :=
      contDiffOn_ext_coord_change (I := closedSmoothModelWithCorners 3) (n := ∞)
        (A.cover.anchor j) (A.cover.anchor i)
    have hchangeO : ContDiffOn ℝ ∞ (change A i j) (O i j) :=
      hchange.mono (fun _ hz => hz.1.1)
    let F : ClosedSmoothModel 3 → ClosedSmoothModel 3 :=
      fun z => η z • change A i j z
    obtain ⟨hF, hcF⟩ :=
      SmoothCutoffVectorExtension.contDiff_hasCompactSupport_cutoff_smul (O i j) hO
        (change A i j) hchangeO η hη hcη hηO
    obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcF hF (by simp)
    have hagree : ∀ z ∈ tsupport θ, ∀ᶠ y in 𝓝 z, F y = change A i j y := by
      intro z hz
      filter_upwards [hηθ z hz] with y hy
      simp only [F, hy, one_smul]
    exact ⟨θ, F, hθ, hcθ, hθ01, hθO, hθK, hF, hcF, hagree, L, hL⟩
  choose θ F hproperties using hsingle
  exact ⟨θ, F, hproperties⟩

end Poincare.BufferedChartTransitionExtensions
