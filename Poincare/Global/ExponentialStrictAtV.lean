import Poincare.Global.LinearizedCLM
import Poincare.Global.ExponentialLocalHomeo
import Poincare.Global.RoundSphereMetric

/-!
# Shifted-base strict exponential boundary

This module records the shifted-base two-point Taylor estimate needed for the
strict derivative of the charted exponential away from the origin.  The full
endpoint strict derivative still requires propagating this estimate through the
linearized endpoint Gronwall comparison.
-/

noncomputable section

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/--
Uniform two-point Taylor estimate with the derivative frozen at a nearby base.

On a compact convex set, a `C¹` map has uniformly continuous derivative.  Hence,
if `x` and `y` are both close to `base`, then the two-point increment
`f y - f x` is controlled by the single linearization at `base`, uniformly in
all three points.
-/
theorem uniform_two_point_taylor_at_base_norm_le_on_compact_convex
    {f : X → Y} {K : Set X}
    (hf : ContDiff ℝ 1 f) (hK_compact : IsCompact K)
    (hK_convex : Convex ℝ K) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ base ∈ K, ∀ x ∈ K, ∀ y ∈ K,
      ‖x - base‖ ≤ δ →
        ‖y - base‖ ≤ δ →
          ‖f y - f x - fderiv ℝ f base (y - x)‖ ≤ ε * ‖y - x‖ := by
  intro ε hε
  have hdf_cont : ContinuousOn (fun x : X ↦ fderiv ℝ f x) K :=
    (hf.continuous_fderiv (by norm_num)).continuousOn
  have hdf_uc : UniformContinuousOn (fun x : X ↦ fderiv ℝ f x) K :=
    hK_compact.uniformContinuousOn_of_continuous hdf_cont
  rcases (Metric.uniformContinuousOn_iff_le.mp hdf_uc) ε hε with
    ⟨δ, hδ, hδprop⟩
  refine ⟨δ, hδ, ?_⟩
  intro base hbase x hx y hy hxbase hybase
  let A : X →L[ℝ] Y := fderiv ℝ f base
  let S : Set X := K ∩ closedBall base δ
  have hxS : x ∈ S := by
    refine ⟨hx, ?_⟩
    simpa [S, dist_eq_norm] using hxbase
  have hyS : y ∈ S := by
    refine ⟨hy, ?_⟩
    simpa [S, dist_eq_norm] using hybase
  have hS_convex : Convex ℝ S :=
    hK_convex.inter (convex_closedBall base δ)
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
    have hdist : dist z base ≤ δ := by
      simpa [S] using hz.2
    simpa [A, dist_eq_norm] using hδprop z hzK base hbase hdist
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
The shifted-base two-point Taylor estimate for the chart Christoffel geodesic
flow field on a compact convex tube.
-/
theorem chartChristoffel_geodesicFlowField_uniform_two_point_taylor_at_base_norm_le_on_compact_convex
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (ClosedSmoothModel n) M]
    [IsManifold (closedSmoothModelWithCorners n) ∞ M]
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {K : Set (ClosedSmoothModel n × ClosedSmoothModel n)}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ base ∈ K, ∀ x ∈ K, ∀ y ∈ K,
        ‖x - base‖ ≤ δ →
          ‖y - base‖ ≤ δ →
            ‖geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀) y -
                geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀) x -
                  linearizedGeodesicFlowOperator
                    (GeodesicTransport.chartChristoffelField g x₀) base (y - x)‖ ≤
              ε * ‖y - x‖ := by
  simpa [linearizedGeodesicFlowOperator] using
    (uniform_two_point_taylor_at_base_norm_le_on_compact_convex
      (f := geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀))
      (K := K)
      (GeodesicTransport.geodesicFlowField_chartChristoffelField_contDiff
        (g := g) (x₀ := x₀))
      hK_compact hK_convex)

/--
Closed-ball form of the shifted-base two-point Taylor estimate for the chart
Christoffel geodesic flow field.
-/
theorem chartChristoffel_geodesicFlowField_uniform_two_point_taylor_at_base_norm_le_closedBall
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (ClosedSmoothModel n) M]
    [IsManifold (closedSmoothModelWithCorners n) ∞ M]
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (p : ClosedSmoothModel n × ClosedSmoothModel n) (a : ℝ) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ base ∈ closedBall p a,
        ∀ x ∈ closedBall p a,
          ∀ y ∈ closedBall p a,
            ‖x - base‖ ≤ δ →
              ‖y - base‖ ≤ δ →
                ‖geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀) y -
                    geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀) x -
                      linearizedGeodesicFlowOperator
                        (GeodesicTransport.chartChristoffelField g x₀) base (y - x)‖ ≤
                  ε * ‖y - x‖ := by
  exact
    chartChristoffel_geodesicFlowField_uniform_two_point_taylor_at_base_norm_le_on_compact_convex
      (g := g) (x₀ := x₀)
      (K := closedBall p a)
      (isCompact_closedBall p a)
      (convex_closedBall p a)

/--
Round-sphere instance of the shifted-base two-point Taylor estimate for the
chart Christoffel geodesic flow field.
-/
theorem roundSphereMetric3_geodesicFlowField_uniform_two_point_taylor_at_base_norm_le_closedBall
    (x₀ : RoundSphere3)
    (p : ClosedSmoothModel 3 × ClosedSmoothModel 3) (a : ℝ) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ base ∈ closedBall p a,
        ∀ x ∈ closedBall p a,
          ∀ y ∈ closedBall p a,
            ‖x - base‖ ≤ δ →
              ‖y - base‖ ≤ δ →
                ‖geodesicFlowField
                    (GeodesicTransport.chartChristoffelField roundSphereMetric3 x₀) y -
                    geodesicFlowField
                      (GeodesicTransport.chartChristoffelField roundSphereMetric3 x₀) x -
                      linearizedGeodesicFlowOperator
                        (GeodesicTransport.chartChristoffelField roundSphereMetric3 x₀)
                        base (y - x)‖ ≤
                  ε * ‖y - x‖ := by
  exact
    chartChristoffel_geodesicFlowField_uniform_two_point_taylor_at_base_norm_le_closedBall
      (g := roundSphereMetric3) (x₀ := x₀) p a

end Poincare
