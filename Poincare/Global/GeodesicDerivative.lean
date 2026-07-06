import Poincare.Global.GeodesicLinearized
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Compact-uniform Taylor remainder for the chart geodesic flow

This module records the compact-uniform first-order Taylor estimate needed
before the initial-velocity derivative comparison.  The full Gronwall
comparison is not closed here: the new verified payload is the uniform
`O(ε * ‖q - base‖)` Taylor remainder on a compact convex first-order tube.
-/

noncomputable section

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/--
Uniform first-order Taylor remainder on a compact convex set.

The proof is the Heine-Cantor route: continuity of `fderiv` gives uniform
continuity on the compact set; the mean-value inequality applied to
`z ↦ f z - fderiv ℝ f x z` on `K ∩ closedBall x δ` turns that uniform
derivative modulus into a uniform Taylor remainder bound.
-/
theorem uniform_taylor_remainder_norm_le_on_compact_convex
    {f : X → Y} {K : Set X}
    (hf : ContDiff ℝ 1 f) (hK_compact : IsCompact K)
    (hK_convex : Convex ℝ K) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x ∈ K, ∀ y ∈ K,
      ‖y - x‖ ≤ δ →
        ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ ε * ‖y - x‖ := by
  intro ε hε
  have hdf_cont : ContinuousOn (fun x : X ↦ fderiv ℝ f x) K :=
    (hf.continuous_fderiv (by norm_num)).continuousOn
  have hdf_uc : UniformContinuousOn (fun x : X ↦ fderiv ℝ f x) K :=
    hK_compact.uniformContinuousOn_of_continuous hdf_cont
  rcases (Metric.uniformContinuousOn_iff_le.mp hdf_uc) ε hε with
    ⟨δ, hδ, hδprop⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hyx
  let A : X →L[ℝ] Y := fderiv ℝ f x
  let S : Set X := K ∩ closedBall x δ
  have hxS : x ∈ S := by
    refine ⟨hx, ?_⟩
    simp [hδ.le]
  have hyS : y ∈ S := by
    refine ⟨hy, ?_⟩
    simpa [S, dist_eq_norm] using hyx
  have hS_convex : Convex ℝ S :=
    hK_convex.inter (convex_closedBall x δ)
  have hder :
      ∀ z ∈ S,
        HasFDerivWithinAt (fun z : X ↦ f z - A z)
          (fderiv ℝ f z - A) S z := by
    intro z _hz
    have hfz : HasFDerivAt f (fderiv ℝ f z) z :=
      (hf.differentiable (by norm_num) z).hasFDerivAt
    have hAz : HasFDerivAt (fun z : X ↦ A z) A z :=
      A.hasFDerivAt
    exact (hfz.sub hAz).hasFDerivWithinAt
  have hbound : ∀ z ∈ S, ‖fderiv ℝ f z - A‖ ≤ ε := by
    intro z hz
    have hzK : z ∈ K := hz.1
    have hzx : dist z x ≤ δ := by
      simpa [S] using hz.2
    simpa [A, dist_eq_norm] using hδprop z hzK x hx hzx
  have hmvt :
      ‖(fun z : X ↦ f z - A z) y - (fun z : X ↦ f z - A z) x‖ ≤
        ε * ‖y - x‖ :=
    hS_convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (𝕜 := ℝ) hder hbound hxS hyS
  have hrewrite :
      (f y - A y) - (f x - A x) =
        f y - f x - A (y - x) := by
    rw [map_sub]
    abel
  simpa [hrewrite] using hmvt

/--
Uniform Taylor remainder for any `C¹` first-order geodesic flow field on a
compact convex first-order tube.
-/
theorem geodesicFlowField_uniform_taylor_remainder_norm_le_on_compact_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {K : Set (E × E)}
    (hF : ContDiff ℝ 1 (geodesicFlowField Γ)) (hK_compact : IsCompact K)
    (hK_convex : Convex ℝ K) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ base ∈ K, ∀ q ∈ K,
      ‖q - base‖ ≤ δ →
        ‖geodesicFlowField Γ q - geodesicFlowField Γ base -
            linearizedGeodesicFlowOperator Γ base (q - base)‖ ≤
          ε * ‖q - base‖ := by
  simpa [linearizedGeodesicFlowOperator] using
    (uniform_taylor_remainder_norm_le_on_compact_convex
      (f := geodesicFlowField Γ) (K := K) hF hK_compact hK_convex)

/--
Uniform Taylor remainder for the chart Christoffel geodesic flow field on a
compact convex first-order chart tube.
-/
theorem chartChristoffel_geodesicFlowField_uniform_taylor_remainder_norm_le_on_compact_convex
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (ClosedSmoothModel n) M]
    [IsManifold (closedSmoothModelWithCorners n) ∞ M]
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {K : Set (ClosedSmoothModel n × ClosedSmoothModel n)}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ base ∈ K, ∀ q ∈ K,
      ‖q - base‖ ≤ δ →
        ‖geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀) q -
            geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀) base -
              linearizedGeodesicFlowOperator
                (GeodesicTransport.chartChristoffelField g x₀) base (q - base)‖ ≤
          ε * ‖q - base‖ := by
  exact
    geodesicFlowField_uniform_taylor_remainder_norm_le_on_compact_convex
      (Γ := GeodesicTransport.chartChristoffelField g x₀)
      (K := K)
      (GeodesicTransport.geodesicFlowField_chartChristoffelField_contDiff
        (g := g) (x₀ := x₀))
      hK_compact hK_convex

end Poincare
