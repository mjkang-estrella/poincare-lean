import Poincare.Global.MetricCoefficientNeighborhoods
import Poincare.Global.RefinedFiniteAtlasExistence

/-!
# Buffered finite atlas for the actual inverse metric

The inverse entries of the given metric select coordinate neighborhoods at
each preferred chart center. A finite refinement places the partition supports
in these neighborhoods, and nested compact cutoffs retain both the requested
coefficient bound and the fixed-anchor cutoff-one germs.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace Poincare.MetricAdaptedBufferedAtlas

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (modelWithCornersSelf ℝ (ClosedSmoothModel 3)) ∞ M]

/-- Construct finite buffered chart geometry from the actual initial metric
and a strictly positive tolerance at every manifold point. -/
theorem exists_metric_adapted_buffered_atlas
    (g0 : ClosedSmoothRiemannianMetric 3 M) (ε : M → ℝ)
    (hε : ∀ p, 0 < ε p) :
    ∃ A : FiniteAtlasParabolicTensorSpace.AtlasData M,
      ∃ ψ ξ : Fin A.cover.chartCount → ClosedSmoothModel 3 → ℝ, ∀ k,
        ContDiff ℝ ∞ (ψ k) ∧ HasCompactSupport (ψ k) ∧
        (∀ z ∈ FiniteAtlasParabolicTensorSpace.coordSupport A k,
          ∀ᶠ y in nhds z, ψ k y = 1) ∧
        (∀ z, ψ k z ∈ Icc 0 1) ∧
        ContDiff ℝ ∞ (ξ k) ∧ HasCompactSupport (ξ k) ∧
        (∀ z, ξ k z ∈ Icc 0 1) ∧
        (∀ z ∈ tsupport (ψ k), ξ k z = 1) ∧
        tsupport (ξ k) ⊆ (FiniteAtlasParabolicTensorSpace.chart A k).target ∧
        (∀ z ∈ tsupport (ξ k), ∀ᶠ y in nhds z,
          GeodesicTransport.cutoff (n := 3) (A.cover.anchor k) y = 1) ∧
        (∀ z ∈ tsupport (ξ k), ∀ a b : Fin 3,
          |(inverseChartPullbackGramMatrixField g0 (A.cover.anchor k) z)⁻¹ a b -
            (inverseChartPullbackGramMatrixField g0 (A.cover.anchor k)
              (extChartAt (modelWithCornersSelf ℝ (ClosedSmoothModel 3))
                (A.cover.anchor k) (A.cover.anchor k)))⁻¹ a b| ≤ ε (A.cover.anchor k)) := by
  classical
  obtain ⟨V, hV, hosc⟩ :=
    MetricCoefficientNeighborhoods.exists_coefficient_neighborhoods g0 ε hε
  obtain ⟨A, _hanchor, hregionV⟩ :=
    RefinedFiniteAtlasExistence.exists_refined_atlasData V
      (fun p => (hV p).1) (fun p => (hV p).2.1)
  have hsupportV (k : Fin A.cover.chartCount) :
      FiniteAtlasParabolicTensorSpace.coordSupport A k ⊆ V (A.cover.anchor k) := by
    exact (image_mono ((A.subordinate k).trans subset_closure)).trans (hregionV k)
  have hbuffers (k : Fin A.cover.chartCount) :=
    BufferedFrozenParabolicSolver.exists_nested_cutoffs
      (FiniteAtlasParabolicTensorSpace.isCompact_coordSupport A k)
      (hV (A.cover.anchor k)).1 (hsupportV k)
  choose U₁ ψ ξ hU₁open hU₁compact hU₁V hψ hψcompact hψU₁ hψone hψrange
    hξ hξcompact hξV hξU₁ hξrange hξψ using hbuffers
  refine ⟨A, ψ, ξ, ?_⟩
  intro k
  refine ⟨hψ k, hψcompact k, hψone k, hψrange k,
    hξ k, hξcompact k, hξrange k, hξψ k, ?_, ?_, ?_⟩
  · exact (hξV k).trans (hV (A.cover.anchor k)).2.2.1
  · intro z hz
    exact (hV (A.cover.anchor k)).2.2.2 z (hξV k hz)
  · exact hosc (A.cover.anchor k) (ξ k) (hξV k)

end Poincare.MetricAdaptedBufferedAtlas
